/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.NullLagrangian.Basic
public import PDE.Analysis.Calculus.Jacobian.Piola

/-!
# The determinant is a null Lagrangian

The derivative in entry `(k,i)` of the determinant density is `adjugate P i k`, including
when `P` is singular. Its value derivative is zero. Thus its Euler–Lagrange expression
is minus the divergence of a cofactor row, which vanishes by the local `C²` Piola identity
(the Lemma on divergence-free rows, equation (20), in Evans, §8.1.4(b)).
This proves Evans, §8.1.4(b), Theorem 2 in every natural dimension.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.1.4(b), (20) and Theorem 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Elementwise

namespace PDE.CalculusOfVariations

variable {n : ℕ}

/-- The gradient-only determinant density for maps between equal-dimensional Euclidean spaces. -/
def determinantLagrangian (P : Matrix (Fin n) (Fin n) ℝ) (_z _x : ℝ^n) : ℝ :=
  P.det

/-- The determinant density is jointly smooth in the matrix, value, and spatial variables. -/
theorem contDiff_determinantLagrangian {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun q : Matrix (Fin n) (Fin n) ℝ × ℝ^n × ℝ^n ↦
      determinantLagrangian q.1 q.2.1 q.2.2) :=
  Analysis.Matrix.contDiff_det.comp contDiff_fst

/-- The matrix derivative of the density exists at every matrix. -/
theorem hasFDerivAt_determinantLagrangian_matrix
    (P : Matrix (Fin n) (Fin n) ℝ) (z x : ℝ^n) :
    HasFDerivAt (fun Q ↦ determinantLagrangian Q z x) (Analysis.Matrix.detDerivative P) P :=
  Analysis.Matrix.hasFDerivAt_det P

/-- The value derivative of the density is zero. -/
theorem hasFDerivAt_determinantLagrangian_value
    (P : Matrix (Fin n) (Fin n) ℝ) (z x : ℝ^n) :
    HasFDerivAt (fun w ↦ determinantLagrangian P w x) (0 : ℝ^n →L[ℝ] ℝ) z :=
  hasFDerivAt_const _ _

/-- The determinant's Euler–Lagrange expression vanishes at every `C²` germ. -/
theorem classicalEulerLagrange_determinant_eq_zero
    {u : ℝ^n → ℝ^n} {x : ℝ^n} (hu : ContDiffAt ℝ 2 u x) (k : Fin n) :
    classicalEulerLagrange determinantLagrangian u x k = 0 := by
  unfold classicalEulerLagrange determinantLagrangian
  simp only [Analysis.Matrix.fderiv_det_single, fderiv_const_apply, zero_apply, add_zero]
  rw [Analysis.sum_partialDeriv_adjugate_jacobianMatrix_eq_zero hu k, neg_zero]

/-- Every `C²` map on an open domain satisfies the determinant's Euler–Lagrange system. -/
theorem classicalEulerLagrange_determinant_eq_zero_on
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) {u : ℝ^n → ℝ^n}
    (hu : ContDiffOn ℝ 2 u Ω) {x : ℝ^n} (hx : x ∈ Ω) (k : Fin n) :
    classicalEulerLagrange determinantLagrangian u x k = 0 :=
  classicalEulerLagrange_determinant_eq_zero (hu.contDiffAt (hΩ.mem_nhds hx)) k

/-- The determinant is a null Lagrangian on every open domain, for all natural dimensions.
The stronger preceding theorem already applies to `C²` maps. -/
theorem isNullLagrangianOn_determinant {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω) :
    IsNullLagrangianOn Ω determinantLagrangian := by
  intro u hu x hx k
  exact classicalEulerLagrange_determinant_eq_zero_on hΩ (hu.of_le (by simp)) hx k

end PDE.CalculusOfVariations
