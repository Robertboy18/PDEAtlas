/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.GraphNorm
import PDE.Spaces.Sobolev.Fractional.Domain.Gagliardo.ZeroDimensional
import PDE.Spaces.Sobolev.Fractional.WholeSpace.ZeroDimensional

/-!
# The completed whole-space Gagliardo–Bessel equivalence

For every dimension and `0 < s < 1`, the complete real Gagliardo graph space on `ℝ^n`
is continuously real-linearly equivalent to `H^{s}(ℝ^n; ℝ)`. The equivalence
preserves the physical `L²` class.

In positive dimension, write `J` for the kernel integral at a unit vector, with Fourier character
`exp(2π i ⟪h, ξ⟫)`. The exact graph-norm identity of `Gagliardo.GraphNorm` is

`‖u‖G² = ‖u‖₂² + J ‖‖ξ‖^s 𝓕u‖₂²`.

Mathlib's Bessel weight is `(1 + ‖ξ‖²)^(s/2)`. The two norms are comparable, with the
explicit, nonoptimal bounds

`‖u‖Hˢ ≤ (1 + (√J)⁻¹) ‖u‖G`,  `‖u‖G ≤ (1 + √J) ‖u‖Hˢ`.

The physical `L²` term is retained, with Mathlib's Fourier normalization.
In dimension zero both norms equal the `L²` norm, so the equivalence is an isometry.
The raw-function identity from `Domain/GagliardoFourier` enters twice:
it identifies the physical `L²` ranges in `Gagliardo/Realization`, and here it identifies
the stored difference-quotient norm. Thus the result concerns the complete spaces,
not only functions for which both seminorms were already known to be finite.
-/

@[expose] public section

noncomputable section

open MeasureTheory TemperedDistribution BesselPotentialSpace
open scoped BesselPotentialSpace ENNReal FourierTransform Real SchwartzMap Sobolev

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ}

namespace GagliardoSpace

/-- The Bessel norm controls the graph norm, including its physical `L²` coordinate. -/
theorem norm_le_toHsSpaceReal (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace n s Set.univ) :
    ‖u‖ ≤ (1 + √(gagliardoFourierConstant n s hn)) * ‖toHsSpaceReal hs0 hs1 u‖ := by
  have hgraph := norm_sq_eq u
  have hsum : ‖u‖ ≤ ‖toLp n s Set.univ u‖ + ‖differenceQuotient n s Set.univ u‖ := by
    nlinarith [norm_nonneg u, norm_nonneg (toLp n s Set.univ u),
      norm_nonneg (differenceQuotient n s Set.univ u),
      mul_nonneg (norm_nonneg (toLp n s Set.univ u))
        (norm_nonneg (differenceQuotient n s Set.univ u))]
  rw [← norm_toL2CLM_eq, norm_differenceQuotient_eq hn hs0 hs1,
    ← norm_toL2Fun_toHsSpaceReal hs0 hs1] at hsum
  calc
    ‖u‖ ≤ ‖toL2Fun hs0.le (toHsSpaceReal hs0 hs1 u).1‖ +
        √(gagliardoFourierConstant n s hn) *
          ‖homogeneousFourierLp hs0.le (toHsSpaceReal hs0 hs1 u).1‖ := hsum
    _ ≤ ‖toHsSpaceReal hs0 hs1 u‖ +
        √(gagliardoFourierConstant n s hn) * ‖toHsSpaceReal hs0 hs1 u‖ :=
      add_le_add (norm_toL2Fun_le hs0.le _)
        (mul_le_mul_of_nonneg_left (norm_homogeneousFourierLp_le hs0.le _)
          (Real.sqrt_nonneg _))
    _ = (1 + √(gagliardoFourierConstant n s hn)) * ‖toHsSpaceReal hs0 hs1 u‖ := by
      rw [add_mul, one_mul]

/-- In dimension zero both realizations have exactly their physical `L²` norm. -/
theorem norm_toHsSpaceReal_zero_dimensional (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace 0 s Set.univ) :
    ‖toHsSpaceReal hs0 hs1 u‖ = ‖u‖ := by
  rw [← HsSpaceReal.norm_toL2FunCLM_zero_dimensional hs0.le,
    toL2FunCLM_toHsSpaceReal, norm_toL2CLM_eq, norm_toLp_zero_dimensional]

/-- The complete whole-space Gagliardo space is continuously real-linearly equivalent
to the real Bessel-potential space in every dimension. Both directions preserve the physical
`L²` function. The equivalence is isometric in dimension zero. -/
def equivHsSpaceReal (hs0 : 0 < s) (hs1 : s < 1) :
    GagliardoSpace n s Set.univ ≃L[ℝ] H^{s}(ℝ^n; ℝ) :=
  (linearEquivHsSpaceReal hs0 hs1).toContinuousLinearEquivOfBounds
    (if hn : 1 ≤ n then 1 + (√(gagliardoFourierConstant n s hn))⁻¹ else 1)
    (if hn : 1 ≤ n then 1 + √(gagliardoFourierConstant n s hn) else 1)
    (fun u ↦ by
      change ‖toHsSpaceReal hs0 hs1 u‖ ≤ _
      by_cases hn : 1 ≤ n
      · simpa only [dite_eq_left hn] using norm_toHsSpaceReal_le hn hs0 hs1 u
      · have hn0 : n = 0 := by omega
        subst n
        simpa only [dite_eq_right hn, one_mul] using
          (norm_toHsSpaceReal_zero_dimensional hs0 hs1 u).le)
    (fun v ↦ by
      by_cases hn : 1 ≤ n
      · have h := norm_le_toHsSpaceReal hn hs0 hs1
          ((linearEquivHsSpaceReal hs0 hs1).symm v)
        change ‖(linearEquivHsSpaceReal hs0 hs1).symm v‖ ≤
          (1 + √(gagliardoFourierConstant n s hn)) *
            ‖linearEquivHsSpaceReal hs0 hs1 ((linearEquivHsSpaceReal hs0 hs1).symm v)‖ at h
        simpa only [dite_eq_left hn, LinearEquiv.apply_symm_apply] using h
      · have hn0 : n = 0 := by omega
        subst n
        have h := norm_toHsSpaceReal_zero_dimensional hs0 hs1
          ((linearEquivHsSpaceReal hs0 hs1).symm v)
        change ‖linearEquivHsSpaceReal hs0 hs1
          ((linearEquivHsSpaceReal hs0 hs1).symm v)‖ =
            ‖(linearEquivHsSpaceReal hs0 hs1).symm v‖ at h
        simpa only [dite_eq_right hn, one_mul, LinearEquiv.apply_symm_apply] using h.ge)

/-- The continuous equivalence preserves the physical `L²` class. -/
@[simp]
theorem toL2FunCLM_equivHsSpaceReal (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace n s Set.univ) :
    HsSpaceReal.toL2FunCLM n hs0.le (equivHsSpaceReal hs0 hs1 u) = toL2CLM n s u :=
  toL2FunCLM_toHsSpaceReal hs0 hs1 u

/-- The inverse equivalence also preserves the physical `L²` class. -/
@[simp]
theorem toL2CLM_equivHsSpaceReal_symm (hs0 : 0 < s) (hs1 : s < 1)
    (v : H^{s}(ℝ^n; ℝ)) :
    toL2CLM n s ((equivHsSpaceReal hs0 hs1).symm v) = HsSpaceReal.toL2FunCLM n hs0.le v := by
  rw [← toL2FunCLM_equivHsSpaceReal hs0 hs1, ContinuousLinearEquiv.apply_symm_apply]

/-- An explicit bound for the forward continuous equivalence. -/
theorem norm_equivHsSpaceReal_le (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (u : GagliardoSpace n s Set.univ) :
    ‖equivHsSpaceReal hs0 hs1 u‖ ≤
      (1 + (√(gagliardoFourierConstant n s hn))⁻¹) * ‖u‖ :=
  norm_toHsSpaceReal_le hn hs0 hs1 u

/-- An explicit bound for the inverse continuous equivalence. -/
theorem norm_equivHsSpaceReal_symm_le (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1)
    (v : H^{s}(ℝ^n; ℝ)) :
    ‖(equivHsSpaceReal hs0 hs1).symm v‖ ≤
      (1 + √(gagliardoFourierConstant n s hn)) * ‖v‖ := by
  have h := norm_le_toHsSpaceReal hn hs0 hs1 ((equivHsSpaceReal hs0 hs1).symm v)
  change ‖(equivHsSpaceReal hs0 hs1).symm v‖ ≤
    (1 + √(gagliardoFourierConstant n s hn)) *
      ‖equivHsSpaceReal hs0 hs1 ((equivHsSpaceReal hs0 hs1).symm v)‖ at h
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

end GagliardoSpace
end SobolevSpace.Fractional
