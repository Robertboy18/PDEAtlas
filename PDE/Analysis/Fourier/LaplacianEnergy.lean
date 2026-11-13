/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# Fourier energy of the Laplacian

For a Schwartz map on `ℝ^n` with values in a complex Hilbert space, Mathlib's
Fourier-multiplier formula for the Laplacian combines with Plancherel's theorem. Under
Mathlib's convention `𝓕 f ξ = ∫ x, exp (-2π i ⟪x, ξ⟫) • f x`, the multiplier of `Δ` is
`-(2π)^2 ‖ξ‖^2`; consequently, its squared `L²` energy carries the factor `(2π)^4`.

In Evans's convention, §4.3.1, Theorem 2(ii) gives `(Δu)^ = -|y|^2 û`, and Plancherel's
theorem then gives `‖Δu‖² = ∫ |y|^4 |û|^2 dy`, with no factor `2π`. The multiplier formula is
Mathlib's `SchwartzMap.laplacian_eq_fourierMultiplierCLM` and Plancherel's theorem is
`SchwartzMap.integral_norm_sq_fourier`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.1, Theorem 1, p. 187, and Theorem 2(ii), p. 189.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis.Fourier

open FourierTransform Laplacian MeasureTheory
open scoped SchwartzMap

/-- Plancherel's identity for the Laplacian under Mathlib's Fourier normalization.

The multiplier `-(2π)^2 ‖ξ‖^2` becomes the weight `(2π)^4 ‖ξ‖^4` after taking squared
norms. -/
theorem integral_norm_sq_laplacian_eq_fourier {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (f : 𝓢(ℝ^n, H)) :
    ∫ x, ‖Δ f x‖ ^ 2 =
      ∫ ξ, (2 * Real.pi) ^ 4 * ‖ξ‖ ^ 4 * ‖𝓕 f ξ‖ ^ 2 := by
  have hg : (fun ξ : ℝ^n ↦ ‖ξ‖ ^ 2).HasTemperateGrowth := by
    fun_prop
  rw [← SchwartzMap.integral_norm_sq_fourier (Δ f)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ ?_)
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM]
  simp only [SchwartzMap.fourierMultiplierCLM_apply, neg_smul,
    FourierTransform.fourier_neg, fourier_smul, fourier_fourierInv_eq, neg_apply,
    smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg, norm_neg, norm_smul,
    norm_pow, norm_mul, Real.norm_ofNat, Real.norm_eq_abs]
  rw [abs_of_pos Real.pi_pos, abs_of_nonneg (norm_nonneg ξ)]
  ring

end PDE.Analysis.Fourier
