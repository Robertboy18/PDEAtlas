/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Variational
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Differentiating the value at a fixed minimizing footpoint

An attained footpoint gives a smooth upper competitor as the endpoint varies:
`z ↦ h y + t * L ((z - y) / t)`. The term `h y` stays constant. At a point
where the value is differentiable, Fermat's theorem identifies its derivative
with the cost derivative. No derivative of the Lipschitz datum is needed at
the minimizing footpoint.

`deriv_value_eq_deriv_cost_of_fixed_footpoint` is the identity `w_x = L'((x - y(x, t))/t)` of
step 4 of the proof of Evans, §3.4.2, Theorem 1, at a point where `w(·, t)` is differentiable.
Evans differentiates `tL((x - y(x, t))/t) + h(y(x, t))` in `x`, which needs `x ↦ y(x, t)` and
`x ↦ h(y(x, t))` to be differentiable; the competitor with a fixed footpoint avoids this.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.2, equation (24), Theorem 1 and step 4 of
  its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace HamiltonJacobi.HopfLax

/-- A fixed footpoint supplies an upper competitor for every spatial endpoint. -/
theorem value_le_fixed_footpoint {L h : ℝ → ℝ} (hL : Superlinear L) {K : ℝ≥0}
    (hh : LipschitzWith K h) {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    value L h t x ≤ h y + t * L ((x - y) / t) := by
  have h := value_le_cost hL hh ht.le x ((x - y) / t)
  have heq : x - t * ((x - y) / t) = y := by
    field_simp [ht.ne']
    ring
  simpa only [cost, smul_eq_mul, heq] using h

/-- Positive-time attainment in the velocity formula gives a
minimizing footpoint. -/
theorem exists_value_eq_fixed_footpoint {L h : ℝ → ℝ} (hcont : Continuous L) (hL : Superlinear L)
    {K : ℝ≥0} (hh : LipschitzWith K h) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∃ y, value L h t x = h y + t * L ((x - y) / t) := by
  obtain ⟨q, hq, _⟩ := exists_minimizer hcont hL hh ht x
  refine ⟨x - t * q, ?_⟩
  have heq : (x - (x - t * q)) / t = q := by
    field_simp [ht.ne']
    ring
  simpa only [heq, cost, smul_eq_mul] using hq

/-- At a spatial differentiability point, every attained footpoint gives the
same derivative of the value. The initial potential need only be Lipschitz. -/
theorem deriv_value_eq_deriv_cost_of_fixed_footpoint {L h : ℝ → ℝ} (hL : Superlinear L) {K : ℝ≥0}
    (hh : LipschitzWith K h) {t x y : ℝ} (ht : 0 < t)
    (hy : value L h t x = h y + t * L ((x - y) / t)) (hvalue : DifferentiableAt ℝ (value L h t) x)
    (hcost : DifferentiableAt ℝ L ((x - y) / t)) :
    deriv (value L h t) x = deriv L ((x - y) / t) := by
  have hfixed : HasDerivAt (fun z : ℝ ↦ h y + t * L ((z - y) / t))
        (deriv L ((x - y) / t)) x := by
    convert ((hcost.hasDerivAt.scomp x
      (((hasDerivAt_id x).sub_const y).div_const t)).const_mul t).const_add (h y) using 1
    · rfl
    · simp only [smul_eq_mul]
      field_simp [ht.ne']
  have hmin : IsLocalMin
      (fun z : ℝ ↦ (h y + t * L ((z - y) / t)) - value L h t z) x := by
    refine Filter.Eventually.of_forall fun z ↦ ?_
    dsimp only
    rw [← hy, sub_self]
    exact sub_nonneg.mpr (value_le_fixed_footpoint hL hh ht z y)
  have hz := hmin.hasDerivAt_eq_zero (hfixed.sub hvalue.hasDerivAt)
  exact (sub_eq_zero.mp hz).symm

end HamiltonJacobi.HopfLax
