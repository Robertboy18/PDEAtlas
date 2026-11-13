/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.TruncatedPower
public import PDE.Analysis.Calculus.LipschitzTopDeriv

/-!
# Lipschitz top derivative of truncated-power B-splines

The `n`-th derivative of the truncated power `x ↦ x₊^(n + 1)` is `(n + 1)! x₊`, a Lipschitz
function. Hence the order-`n + 2` truncated-power B-spline, a finite combination of reflected and
translated truncated powers, has `n` continuous derivatives and a locally Lipschitz `n`-th
derivative: it lies in the local class `C^{n,1}`. For sixth-order splines (`n = 4`) this is
`C^{4,1}` regularity.

## Main results

* `lipschitzTopDeriv_posPart_pow`: the truncated power `x ↦ x₊^(n + 1)` lies in the local class
  `C^{n,1}`.
* `lipschitzTopDeriv_truncatedPowerBSpline`: the order-`n + 2` truncated-power B-spline lies in
  the local class `C^{n,1}`.
-/

@[expose] public section

namespace CAS.Splines

open PDE.Analysis

/-- The truncated power `x ↦ x₊^(n + 1)` lies in the local class `C^{n,1}`. -/
theorem lipschitzTopDeriv_posPart_pow (n : ℕ) :
    LipschitzTopDeriv n (fun x : ℝ ↦ x⁺ ^ (n + 1)) := by
  induction n with
  | zero =>
    refine ⟨by simpa using (contDiff_zero (𝕜 := ℝ)).mpr continuous_posPart, ?_⟩
    simp only [iteratedDeriv_zero, zero_add, pow_one]
    exact (LipschitzWith.id.max_const 0).locallyLipschitz
  | succ n ih =>
    have hderiv : deriv (fun x : ℝ ↦ x⁺ ^ (n + 1 + 1)) =
        fun x ↦ ((n + 2 : ℕ) : ℝ) * x⁺ ^ (n + 1) :=
      funext fun x ↦ (PDE.Analysis.hasDerivAt_posPart_pow n x).deriv
    refine ⟨PDE.Analysis.contDiff_posPart_pow_succ (n + 1), ?_⟩
    rw [iteratedDeriv_succ', hderiv]
    exact (ih.const_mul _).locallyLipschitz

/-- An order-`n + 2` truncated-power B-spline lies in the local class `C^{n,1}`: its `n`-th
derivative is a combination of the Lipschitz functions `x ↦ (sⱼ - x)₊`. -/
theorem lipschitzTopDeriv_truncatedPowerBSpline (n : ℕ) (knots : Fin (n + 3) → ℝ) :
    LipschitzTopDeriv n (truncatedPowerBSpline n knots) := by
  unfold truncatedPowerBSpline
  apply LipschitzTopDeriv.sum
  intro j _
  simpa only [div_eq_mul_inv, mul_comm _ (splineDividedDifferenceDenominator knots j)⁻¹,
    mul_assoc] using
    (((lipschitzTopDeriv_posPart_pow n).comp_const_sub (knots j)).const_mul (n + 2 : ℝ)).const_mul
      (splineDividedDifferenceDenominator knots j)⁻¹

end CAS.Splines
