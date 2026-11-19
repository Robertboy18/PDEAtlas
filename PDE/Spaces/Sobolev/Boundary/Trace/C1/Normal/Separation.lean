/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal

/-!
# Separation along the intrinsic boundary normal

The normal component of a boundary displacement is smaller than any fixed
multiple of its length near a C¹ boundary point. Consequently, points on
either side of the normal line stay quantitatively separated from the
entire boundary. This estimate controls the two singularities in a paired
single-layer kernel.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Filter Metric Set
open scoped Topology InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- Boundary displacements have an arbitrarily small relative normal
component near their base point. -/
theorem eventually_abs_normal_inner_le (x : frontier Ω) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 (x : ℝ^n), y ∈ frontier Ω →
      |inner ℝ (outwardUnitNormal (Ω := Ω) x) (y - x)| ≤ ε * ‖y - x‖ := by
  obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier (Ω := Ω) x.property
  let f : ℝ^n → ℝ := fun y ↦ (hΩ.chart i y) (PDE.Common.lastIndex (n := n))
  let L : ℝ^n →L[ℝ] ℝ :=
    (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
      (fderiv ℝ (fun y ↦ hΩ.chart i y) x)
  let c := chartConormal (Ω := Ω) i x
  have hc : 0 < ‖c‖ := norm_pos_iff.mpr (chartConormal_ne_zero i hi)
  have hf : HasFDerivAt f L x := hasFDerivAt_chartLastCoordinate i x
  have hzero : f x = 0 := (chartLastCoordinate_eq_zero_iff i hi).mpr x.property
  have hdual : (InnerProductSpace.toDual ℝ (ℝ^n)) c = L :=
    (InnerProductSpace.toDual ℝ (ℝ^n)).apply_symm_apply L
  have hnormal : outwardUnitNormal (Ω := Ω) x = -‖c‖⁻¹ • c := by
    rw [outwardUnitNormal_eq_chart x i hi]
    rfl
  filter_upwards [(hΩ.chart i).open_source.mem_nhds hi,
    hf.isLittleO.bound (mul_pos hε hc)] with y hy herr hyb
  have hyzero : f y = 0 := (chartLastCoordinate_eq_zero_iff i hy).mpr hyb
  have herror : |L (y - x)| ≤ ε * ‖c‖ * ‖y - x‖ := by
    simpa only [hyzero, hzero, sub_zero, zero_sub, norm_neg, Real.norm_eq_abs] using herr
  rw [hnormal, real_inner_smul_left, ← InnerProductSpace.toDual_apply_apply, hdual,
    abs_mul, abs_neg, abs_of_pos (inv_pos.mpr hc)]
  calc
    _ ≤ ‖c‖⁻¹ * (ε * ‖c‖ * ‖y - x‖) :=
      mul_le_mul_of_nonneg_left herror (inv_nonneg.mpr hc.le)
    _ = ε * ‖y - x‖ := by field_simp

omit [Fact (0 < n)] in
private theorem norm_sub_smul_normal_ge
    (v ν : ℝ^n) (hν : ‖ν‖ = 1)
    (hangle : |inner ℝ ν v| ≤ ‖v‖ / 2) (t : ℝ) :
    (|t| + ‖v‖) / 2 ≤ ‖v - t • ν‖ := by
  have hinner : inner ℝ v (t • ν) ≤ |t| * ‖v‖ / 2 := by
    rw [real_inner_smul_right, real_inner_comm ν v]
    calc
      _ ≤ |t * inner ℝ ν v| := le_abs_self _
      _ = |t| * |inner ℝ ν v| := abs_mul _ _
      _ ≤ |t| * (‖v‖ / 2) :=
        mul_le_mul_of_nonneg_left hangle (abs_nonneg t)
      _ = |t| * ‖v‖ / 2 := by ring
  have hsq := norm_sub_sq_real v (t • ν)
  rw [norm_smul, Real.norm_eq_abs, hν, mul_one] at hsq
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  nlinarith [sq_nonneg (‖v‖ - |t|)]

/-- A sufficiently short signed normal displacement is separated from
every boundary point by half the sum of its height and boundary distance.
The radius is chosen before either the displacement or the boundary point. -/
theorem exists_normal_separation (x : frontier Ω) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∀ y ∈ frontier Ω,
      (|t| + ‖y - x‖) / 2 ≤
        ‖(x : ℝ^n) + t • outwardUnitNormal (Ω := Ω) x - y‖ := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_abs_normal_inner_le (Ω := Ω) x (ε := 1 / 2) (by norm_num))
  refine ⟨r / 4, by positivity, ?_⟩
  intro t ht y hy
  have hν := norm_outwardUnitNormal (Ω := Ω) x
  have heq : (x : ℝ^n) + t • outwardUnitNormal (Ω := Ω) x - y =
      -((y - x) - t • outwardUnitNormal (Ω := Ω) x) := by abel
  rw [heq, norm_neg]
  by_cases hnear : ‖y - x‖ < r
  · apply norm_sub_smul_normal_ge _ _ hν
    have hangle := hball (by simpa only [dist_eq_norm] using hnear) hy
    simpa only [one_div, mul_comm, div_eq_mul_inv, one_mul] using hangle
  · have hfar := norm_sub_norm_le (y - x) (t • outwardUnitNormal (Ω := Ω) x)
    rw [norm_smul, Real.norm_eq_abs, hν, mul_one] at hfar
    have hrle : r ≤ ‖y - x‖ := le_of_not_gt hnear
    linarith

end SobolevSpace.Trace.C1
