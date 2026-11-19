/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.EuclideanBall
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import CAS.ExactTactic

/-!
# A fixed compact backward cone

The cone with vertex `(1, 0)` parametrizes every backward cone with vertex
`(t, x)` by `(s, z) ↦ (t s, x + t z)`. Its affine restriction maps compose
exactly. This lets a single integral operator describe all sufficiently short
time intervals, including signed times near the initial slice.
-/

@[expose] public noncomputable section

open Set
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower

/-- The normalized closed backward cone in three spatial dimensions. -/
def cone : Set (ℝ × ℝ^3) :=
  {q | q.1 ∈ Icc 0 1 ∧ ‖q.2‖ ≤ 1 - q.1}

/-- The normalized cone is compact. -/
theorem isCompact_cone : IsCompact cone := by
  apply (isCompact_closedBall (0 : ℝ × ℝ^3) 1).of_isClosed_subset
  · exact ((isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le continuous_snd.norm (continuous_const.sub continuous_fst)))
  · intro q hq
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
    exact ⟨by simpa only [Real.norm_eq_abs, abs_of_nonneg hq.1.1] using hq.1.2,
      hq.2.trans (by linarith [hq.1.1])⟩

/-- Points in the normalized backward cone. -/
abbrev Cone := ↥cone

instance : CompactSpace Cone := isCompact_iff_compactSpace.mp isCompact_cone

/-- The time coordinate of a point in the cone. -/
def coneTime (q : Cone) : ℝ := q.1.1

/-- The spatial coordinate of a point in the cone. -/
def coneSpace (q : Cone) : ℝ^3 := q.1.2

/-- Normalized time lies in the unit interval. -/
theorem coneTime_mem (q : Cone) : coneTime q ∈ Icc (0 : ℝ) 1 := q.2.1

/-- The spatial distance to the axis is bounded by the remaining time. -/
theorem norm_coneSpace_le (q : Cone) : ‖coneSpace q‖ ≤ 1 - coneTime q := q.2.2

/-- The vertex at normalized time one. -/
def vertex : Cone := ⟨(1, 0), by simp [cone]⟩

/-- Restrict to the backward cone with vertex at a given cone point. -/
def descend (q r : Cone) : Cone := by
  refine ⟨(coneTime q * coneTime r, coneSpace q + coneTime q • coneSpace r), ?_⟩
  have hq := coneTime_mem q
  have hr := coneTime_mem r
  refine ⟨⟨mul_nonneg hq.1 hr.1,
    (mul_le_mul_of_nonneg_left hr.2 hq.1).trans (by simpa using hq.2)⟩, ?_⟩
  calc
    ‖coneSpace q + coneTime q • coneSpace r‖ ≤
        ‖coneSpace q‖ + coneTime q * ‖coneSpace r‖ := by
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hq.1] using
        norm_add_le (coneSpace q) (coneTime q • coneSpace r)
    _ ≤ (1 - coneTime q) + coneTime q * (1 - coneTime r) := add_le_add (norm_coneSpace_le q)
        (mul_le_mul_of_nonneg_left (norm_coneSpace_le r) hq.1)
    _ = 1 - coneTime q * coneTime r := by cas

/-- Restriction multiplies normalized times. -/
@[simp] theorem coneTime_descend (q r : Cone) :
    coneTime (descend q r) = coneTime q * coneTime r := rfl

/-- Restriction translates and scales the spatial coordinate. -/
@[simp] theorem coneSpace_descend (q r : Cone) :
    coneSpace (descend q r) = coneSpace q + coneTime q • coneSpace r := rfl

/-- Cone restriction depends continuously on both cone points. -/
theorem continuous_descend : Continuous (fun p : Cone × Cone ↦ descend p.1 p.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_subtype_val.fst.comp continuous_fst).mul
    (continuous_subtype_val.fst.comp continuous_snd)).prodMk
    ((continuous_subtype_val.snd.comp continuous_fst).add
      ((continuous_subtype_val.fst.comp continuous_fst).smul
        (continuous_subtype_val.snd.comp continuous_snd)))

/-- Restricting a cone twice agrees with the composed affine restriction. -/
theorem descend_assoc (q r s : Cone) :
    descend (descend q r) s = descend q (descend r s) := by
  apply Subtype.ext
  apply Prod.ext
  · exact mul_assoc _ _ _
  · change coneSpace q + coneTime q • coneSpace r + (coneTime q * coneTime r) • coneSpace s =
      coneSpace q + coneTime q • (coneSpace r + coneTime r • coneSpace s)
    rw [smul_add, smul_smul, add_assoc]

/-- Restriction to the vertex changes no cone point. -/
@[simp] theorem descend_vertex_left (q : Cone) : descend vertex q = q := by
  apply Subtype.ext
  simp [descend, vertex, coneTime, coneSpace]

/-- The vertex of the restricted cone is its defining point. -/
@[simp] theorem descend_vertex_right (q : Cone) : descend q vertex = q := by
  apply Subtype.ext
  simp [descend, vertex, coneTime, coneSpace]

/-- Points on the lateral boundary, parametrized by time and direction. -/
def rim (s : I) (ω : Metric.sphere (0 : ℝ^3) 1) : Cone :=
  ⟨((s : ℝ), (1 - (s : ℝ)) • (ω : ℝ^3)), s.2, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr s.2.2),
      mem_sphere_zero_iff_norm.mp ω.2, mul_one]⟩

/-- The lateral boundary parametrization is continuous, including its vertex. -/
theorem continuous_rim :
    Continuous (fun p : I × Metric.sphere (0 : ℝ^3) 1 ↦ rim p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).prodMk
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd))

end WaveEquation.SmallData.Classical.LocalPower
