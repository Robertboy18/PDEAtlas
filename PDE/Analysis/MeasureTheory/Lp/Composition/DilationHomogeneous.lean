/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation
public import PDE.Common.Euclidean
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The `Lᵖ` norm of a homogeneous rescaling

A function on `ℝⁿ` that is homogeneous of degree `-k` up to a cutoff at radius `R` has the form
`R⁻ᵏ f(x / R)`. Its `Lᵖ` norm is exactly `R^{n/p - k} ‖f‖_{Lᵖ}`, for every `R > 0`. So a
localized field and its derivatives have `Lᵖ` norms that are powers of the radius times
constants that do not depend on `R`; `NavierStokes.Nonuniqueness.eLpNorm_localizationRemainder`
is the case `n = 3`, `k = 1`. It follows that a function homogeneous of degree `-k` has `Lᵖ` norm
zero or infinity whenever `n/p ≠ k`. For instance the scale-invariant datum of a self-similar
solution on `ℝ³`, homogeneous of degree `-1`, is square integrable only if it vanishes almost
everywhere.

## Main results

* `MeasureTheory.eLpNorm_inv_pow_smul_comp_inv_smul` (all dimensions `n`, all exponents `p`, all
  `R > 0`, all `k : ℕ`): `‖R⁻ᵏ f(· / R)‖_{Lᵖ(ℝⁿ)} = R^{n/p - k} ‖f‖_{Lᵖ(ℝⁿ)}`, with `n/p = 0`
  for `p = ∞`.
* `MeasureTheory.eLpNorm_eq_zero_or_top_of_homogeneous` (all `n`, `p`, `k` with `n/p ≠ k`): a
  function homogeneous of degree `-k` has `Lᵖ` norm `0` or `∞`.

## How it works

The factor `R⁻ᵏ` comes out of the norm, and the dilation `x ↦ x / R` multiplies the measure by
`Rⁿ`, so the norm by `R^{n/p}` (`MeasureTheory.eLpNorm_comp_smul`). A homogeneous function is
unchanged by the rescaling with `R = 2`, while its norm is multiplied by `2^{n/p - k} ≠ 1`.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.2, the localization of
  the scale-invariant datum, and Remark 2. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

namespace MeasureTheory

open Module
open scoped ENNReal

/-- **The `Lᵖ` norm of a homogeneous rescaling**: for `R > 0`,
`‖R⁻ᵏ f(· / R)‖_{Lᵖ(ℝⁿ)} = R^{n/p - k} ‖f‖_{Lᵖ(ℝⁿ)}`. The factor `R⁻ᵏ` comes out, and the
dilation contributes `R^{n/p}`. -/
theorem eLpNorm_inv_pow_smul_comp_inv_smul {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ^n → F} (hf : AEStronglyMeasurable f volume) {R : ℝ} (hR : 0 < R)
    (k : ℕ) (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ R⁻¹ ^ k • f (R⁻¹ • x)) p volume =
      ENNReal.ofReal (R ^ ((n : ℝ) / p.toReal - k)) * eLpNorm f p volume := by
  have h1 : eLpNorm (fun x ↦ R⁻¹ ^ k • f (R⁻¹ • x)) p volume =
      ‖R⁻¹ ^ k‖ₑ * eLpNorm (fun x ↦ f (R⁻¹ • x)) p volume :=
    eLpNorm_const_smul (R⁻¹ ^ k) (fun x ↦ f (R⁻¹ • x)) p volume
  have hdil : dilationFactor (ℝ^n) R⁻¹ p = ENNReal.ofReal (R ^ ((n : ℝ) / p.toReal)) := by
    rw [dilationFactor, finrank_euclideanSpace_fin, inv_pow, inv_inv, abs_of_pos (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ENNReal.toReal_div,
      ENNReal.toReal_one, ← Real.rpow_natCast, ← Real.rpow_mul hR.le, mul_one_div]
  have hk : ‖R⁻¹ ^ k‖ₑ = ENNReal.ofReal (R ^ (-(k : ℝ))) := by
    rw [Real.eNorm_eq_ofReal (by positivity), Real.rpow_neg hR.le, Real.rpow_natCast, inv_pow]
  rw [h1, eLpNorm_comp_smul hf (inv_ne_zero hR.ne'), hdil, hk, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hR, neg_add_eq_sub]

/-- **A homogeneous function has `Lᵖ` norm zero or infinity.** If `f(c x) = c⁻ᵏ f(x)` for all
`c > 0` and `n/p ≠ k`, then `‖f‖_{Lᵖ(ℝⁿ)}` is `0` or `∞`: the rescaling by `R = 2` leaves `f`
unchanged and multiplies its norm by `2^{n/p - k} ≠ 1`. -/
theorem eLpNorm_eq_zero_or_top_of_homogeneous {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ^n → F} (hf : AEStronglyMeasurable f volume) {k : ℕ} {p : ℝ≥0∞}
    (hhom : ∀ x (c : ℝ), 0 < c → f (c • x) = c⁻¹ ^ k • f x) (hne : (n : ℝ) / p.toReal ≠ k) :
    eLpNorm f p volume = 0 ∨ eLpNorm f p volume = ⊤ := by
  have h := eLpNorm_inv_pow_smul_comp_inv_smul hf (R := 2) two_pos k p
  have hfun : (fun x ↦ (2 : ℝ)⁻¹ ^ k • f ((2 : ℝ)⁻¹ • x)) = f := by
    funext x
    rw [hhom x _ (by positivity), inv_inv, smul_smul, ← mul_pow, inv_mul_cancel₀ two_ne_zero,
      one_pow, one_smul]
  rw [hfun] at h
  by_contra hcon
  rw [not_or] at hcon
  have ha0 : (eLpNorm f p volume).toReal ≠ 0 := (ENNReal.toReal_pos hcon.1 hcon.2).ne'
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  have h3 : (2 : ℝ) ^ ((n : ℝ) / p.toReal - k) = 1 :=
    mul_right_cancel₀ ha0 (h2.symm.trans (one_mul _).symm)
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr hne) with hlt | hgt
  · exact (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hlt).ne h3
  · exact (Real.one_lt_rpow one_lt_two hgt).ne' h3

end MeasureTheory
