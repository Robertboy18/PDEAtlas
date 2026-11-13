/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Pullback.Operator

/-!
# Quadratic bounded pullback on intrinsic fractional spaces

The case `p = 2` of the bounded pullback of `Operator`, with the quadratic component
bounds and the operator-norm bound obtained by specialization.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal FractionalSobolev

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)} {L D : ℝ≥0}

section Quadratic

variable (hs : 0 ≤ (n : ℝ) / 2 + s) (hE : Measurable (fun x ↦ E x))
  (hL : LipschitzOnWith L E E.source)
  (hD : Measure.map E (volume.restrict E.source) ≤
    (D : ℝ≥0∞) • volume.restrict E.target)

/-- Quadratic compatibility name for the single bounded pullback construction. -/
abbrev pullbackCLM : W^{s,2}(E.target) →L[ℝ] W^{s,2}(E.source) :=
  pullbackL (p := 2) hs hE hL hD (by norm_num)

/-- The original quadratic component bound, specialized from the p-energy estimate. -/
theorem norm_toLp_pullback_sq_le (u : W^{s,2}(E.target)) :
    ‖toLp n s E.source (pullback (p := 2) hs hE hL hD u)‖ ^ 2 ≤
      (D : ℝ) * ‖toLp n s E.target u‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, mul_pow] using
    norm_toLp_pullback_rpow_le (p := 2) hs hE hL hD (by norm_num) u

/-- The original quadratic component bound, specialized from the p-energy estimate. -/
theorem norm_differenceQuotient_pullback_sq_le (u : W^{s,2}(E.target)) :
    ‖differenceQuotient n s E.source (pullback (p := 2) hs hE hL hD u)‖ ^ 2 ≤
      ((L : ℝ) ^ ((n : ℝ) / 2 + s) * D) ^ 2 *
        ‖differenceQuotient n s E.target u‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, mul_pow] using
    norm_differenceQuotient_pullback_rpow_le (p := 2) hs hE hL hD (by norm_num) u

/-- The original quadratic component bound, specialized from the p-energy estimate. -/
theorem norm_pullback_sq_le (u : W^{s,2}(E.target)) :
    ‖pullback (p := 2) hs hE hL hD u‖ ^ 2 ≤
      (D : ℝ) * ‖toLp n s E.target u‖ ^ 2 +
        ((L : ℝ) ^ ((n : ℝ) / 2 + s) * D) ^ 2 *
          ‖differenceQuotient n s E.target u‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, mul_pow] using
    norm_pullback_rpow_le (p := 2) hs hE hL hD (by norm_num) u

/-- A finite graph-norm bound, with all constants supplied by chart geometry. -/
theorem norm_pullback_le (u : W^{s,2}(E.target)) :
    ‖pullback (p := 2) hs hE hL hD u‖ ≤
      Real.sqrt ((D : ℝ) + ((L : ℝ) ^ ((n : ℝ) / 2 + s) * D) ^ 2) * ‖u‖ := by
  have hv := norm_pullback_sq_le hs hE hL hD u
  have hu := norm_sq_eq u
  have hC : 0 ≤ (D : ℝ) + ((L : ℝ) ^ ((n : ℝ) / 2 + s) * D) ^ 2 := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hC]
  nlinarith [mul_nonneg D.coe_nonneg (sq_nonneg ‖differenceQuotient n s E.target u‖),
    mul_nonneg (sq_nonneg ((L : ℝ) ^ ((n : ℝ) / 2 + s) * D))
      (sq_nonneg ‖toLp n s E.target u‖)]

/-- At `p = 2`, the physical representative of the pullback is the composition with the chart. -/
theorem toLp_pullbackCLM_apply_ae (u : W^{s,2}(E.target)) :
    (toLp n s E.source (pullbackCLM hs hE hL hD u) : ℝ^n → ℝ) =ᵐ[volume.restrict E.source]
      (toLp n s E.target u : ℝ^n → ℝ) ∘ E :=
  toLp_pullbackL_apply_ae (p := 2) hs hE hL hD (by norm_num) u

/-- At `p = 2`, any representative of `u` composed with the chart represents the pullback. -/
theorem toLp_pullbackCLM_apply_ae_of_ae_eq (u : W^{s,2}(E.target))
    {f : ℝ^n → ℝ} (hf : (toLp n s E.target u : ℝ^n → ℝ) =ᵐ[volume.restrict E.target] f) :
    (toLp n s E.source (pullbackCLM hs hE hL hD u) : ℝ^n → ℝ) =ᵐ[volume.restrict E.source]
      f ∘ E :=
  toLp_pullbackL_apply_ae_of_ae_eq (p := 2) hs hE hL hD (by norm_num) u hf

/-- At `p = 2`, the pullback of the element built from `f` is the element built from `f ∘ E`. -/
theorem pullbackCLM_ofFunction {f : ℝ^n → ℝ} (hf : MemGagliardo n s E.target f) :
    pullbackCLM hs hE hL hD (ofFunction f hf) =
      ofFunction (f ∘ E) (Pullback.memGagliardo_comp hs hE hL hD hf) :=
  pullbackL_ofFunction (p := 2) hs hE hL hD (by norm_num) hf

/-- At `p = 2`, the pullback does not depend on the chosen Lipschitz and volume bounds. -/
theorem pullbackCLM_eq {L' D' : ℝ≥0}
    (hL' : LipschitzOnWith L' E E.source)
    (hD' : Measure.map E (volume.restrict E.source) ≤
      (D' : ℝ≥0∞) • volume.restrict E.target) :
    pullbackCLM hs hE hL hD = pullbackCLM hs hE hL' hD' :=
  pullbackL_eq (p := 2) hs hE hL hD (by norm_num) hL' hD'

/-- The operator norm is bounded by the two quantitative component estimates. -/
theorem norm_pullbackCLM_le :
    ‖pullbackCLM hs hE hL hD‖ ≤
      Real.sqrt ((D : ℝ) + ((L : ℝ) ^ ((n : ℝ) / 2 + s) * D) ^ 2) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    (norm_pullback_le hs hE hL hD)

variable {M J : ℝ≥0}
  (hSymm : Measurable (fun y ↦ E.symm y))
  (hM : LipschitzOnWith M E.symm E.target)
  (hJ : Measure.map E.symm (volume.restrict E.target) ≤
    (J : ℝ≥0∞) • volume.restrict E.source)

/-- Pulling back along a chart and then its inverse recovers the original
intrinsic element, as witnessed by the physical L2 representative. -/
theorem pullbackCLM_symm_pullbackCLM (u : W^{s,2}(E.target)) :
    pullbackCLM hs hSymm hM hJ (pullbackCLM hs hE hL hD u) = u :=
  pullbackL_symm_pullbackL (p := 2) hs hE hL hD hSymm hM hJ (by norm_num) u

end Quadratic

end SobolevSpace.Fractional.GagliardoSpace
