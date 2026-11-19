/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.InitialPotential.Regularity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Spatial derivatives of the continued value

At a joint differentiability point, the spatial slice derivative is the
spatial component of the Fréchet derivative. Spatial Lipschitz
preservation therefore bounds that component by the initial Lipschitz
constant, independently of the time Lipschitz constant.

The spatial Lipschitz preservation is (28) of Evans, §3.3.2(b), Lemma 2: `u(·, t)` has the
Lipschitz constant of `g`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(b), Lemma 2 and its proof, equation (28).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace HamiltonJacobi.HopfLax

/-- Restricting the continued value to a spatial slice identifies its
derivative, including nonpositive times where the continuation is the datum. -/
theorem hasDerivAt_value_of_differentiableAt_forwardValue {L h : ℝ → ℝ} {p : ℝ × ℝ}
    (hd : DifferentiableAt ℝ (forwardValue L h) p) :
    HasDerivAt (value L h (max p.2 0)) (fderiv ℝ (forwardValue L h) p (1, 0)) p.1 := by
  simpa only [forwardValue, Function.comp_def, id_eq] using hd.hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))

/-- The spatial component of the totalized derivative is bounded by
the datum's Lipschitz constant everywhere. At nondifferentiability points,
Mathlib's `fderiv` is zero. -/
theorem norm_spatial_fderiv_forwardValue_le {L h : ℝ → ℝ} (hL : Superlinear L) {K : ℝ≥0}
    (hh : LipschitzWith K h) (p : ℝ × ℝ) :
    ‖fderiv ℝ (forwardValue L h) p (1, 0)‖ ≤ K := by
  by_cases hd : DifferentiableAt ℝ (forwardValue L h) p
  · rw [← (hasDerivAt_value_of_differentiableAt_forwardValue hd).deriv]
    exact norm_deriv_le_of_lipschitz (lipschitzWith_value hL hh (le_max_right _ _))
  · simp only [fderiv_zero_of_not_differentiableAt hd, zero_apply, norm_zero, NNReal.coe_nonneg]

end HamiltonJacobi.HopfLax
