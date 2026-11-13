/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.NormalFrequency
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bounded restriction in normal-frequency coordinates

The adjoint of the isometric normal-frequency lifting is a contraction onto
the boundary `L²` space. Its right inverse is the lifting itself. These are
statements about weighted Fourier coordinates; identifying them with
restriction of physical functions requires the Fourier slice formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace SobolevSpace.Fractional.Trace

/-- Integration against the normalized kernel, initially characterized by duality. -/
def normalRestriction (n : ℕ) :
    Lp ℂ 2 (volume : Measure (ℝ^n × ℝ)) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ^n) :=
  (normalLiftLI n).toContinuousLinearMap.adjoint

/-- Normal-frequency restriction has operator norm at most one. -/
theorem norm_normalRestriction_le (n : ℕ) : ‖normalRestriction n‖ ≤ 1 := by
  rw [normalRestriction, ContinuousLinearMap.adjoint.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, one_mul, le_refl]

/-- The normal-frequency restriction estimate. -/
theorem norm_normalRestriction_apply_le (n : ℕ)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ))) :
    ‖normalRestriction n u‖ ≤ ‖u‖ :=
  ((normalRestriction n).le_opNorm u).trans
    (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (norm_normalRestriction_le n) (norm_nonneg u))

/-- Restriction of a lifted boundary coordinate is the original coordinate. -/
theorem normalRestriction_normalLift (n : ℕ) (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    normalRestriction n (normalLift v) = v := by
  exact congr($(LinearIsometry.adjoint_comp_self (normalLiftLI n)) v)

/-- Every boundary `L²` coordinate has a lift of exactly the same norm. -/
theorem normalRestriction_surjective (n : ℕ) : Function.Surjective (normalRestriction n) :=
  fun v ↦ ⟨normalLift v, normalRestriction_normalLift n v⟩

/-- The duality identity determining normal-frequency restriction. -/
theorem inner_normalRestriction (n : ℕ)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ)))
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    ⟪v, normalRestriction n u⟫_ℂ = ⟪normalLift v, u⟫_ℂ :=
  (normalLiftLI n).toContinuousLinearMap.adjoint_inner_right v u

/-- The kernel lift has minimal norm among all coordinates with its boundary value. -/
theorem normalLift_norm_le_of_restriction_eq (n : ℕ)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n × ℝ)))
    (v : Lp ℂ 2 (volume : Measure ℝ^n))
    (h : normalRestriction n u = v) :
    ‖normalLift v‖ ≤ ‖u‖ := by
  rw [norm_normalLift, ← h]
  exact norm_normalRestriction_apply_le n u

end SobolevSpace.Fractional.Trace
