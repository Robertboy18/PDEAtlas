/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Equation
public import PDE.Parabolic.MaximumPrinciple.Strong.Maximum

/-!
# The strong maximum principle for heat flow

An interior maximum at positive time forces a heat subsolution to be constant throughout the
preceding cylinder. The same holds for a supersolution at a minimum. These are part (ii) of Evans's
§2.3.3(a), Theorem 4 (Strong maximum principle for the heat equation) and its minimum version, for
subsolutions and supersolutions on a connected open set.

Only spatial `C²` regularity and a time derivative inside `(0,T)` are used. Continuity includes the
final time, so the contact may occur at `t = T`. There is no assumption about the solution after
`T`, and the spatial domain need not be bounded or have a smooth boundary.

## Main results

* `eqOn_const_of_isMaxOn`: the strong maximum principle for subsolutions.
* `eqOn_const_of_isMinOn`: the strong minimum principle for supersolutions.

## How it works

Evans derives Theorem 4 for solutions from the mean-value property on heat balls, §2.3.2, Theorem 3,
and spreads the maximum along polygonal paths. We take instead the identity diffusion matrix and
zero drift and potential in `ParabolicMaximum.matrix_strong_maximum_zero_potential` and
`ParabolicMaximum.matrix_strong_minimum_zero_potential`, the variable-coefficient principles of
Evans's §7.1.4(c), Theorem 11. `heatParabolicOperator_eq_matrixParabolicOperator` identifies the two
operators.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, Theorem 3 (A mean-value property for the heat
  equation), p. 53; §2.3.3(a), Theorem 4 (Strong maximum principle for the heat equation) and its
  proof, pp. 55-56; §7.1.4(c), Theorem 11 (Strong maximum principle), pp. 396-397.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

namespace HeatEquation

open ParabolicMaximum Set

variable {n : ℕ}

/-- The identity diffusion matrix gives precisely the coordinate heat operator.
Both sides use the same second partial derivatives, so no regularity hypothesis is needed. -/
theorem heatParabolicOperator_eq_matrixParabolicOperator
    (u : ℝ^n → ℝ → ℝ) (x : ℝ^n) (t : ℝ) :
    heatParabolicOperator u x t =
      matrixParabolicOperator (fun _ _ ↦ 1) (fun _ _ ↦ 0) (fun _ _ ↦ 0) u x t := by
  classical
  simp [heatParabolicOperator, matrixParabolicOperator, EllipticMaximum.matrixOperator,
    Matrix.one_apply, laplacian, sub_eq_add_neg]

private theorem identity_ellipticity (d : ℝ^n) :
    1 * ‖d‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n,
      (1 : Matrix (Fin n) (Fin n) ℝ) i j * d i * d j := by
  classical
  rw [one_mul, EuclideanSpace.real_norm_sq_eq]
  simp [Matrix.one_apply, pow_two]

variable {U : Set (ℝ^n)} {T : ℝ} {u : ℝ^n → ℝ → ℝ}
  (hU : IsOpen U) (hconn : IsPreconnected U)
  (hucont : ContinuousOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T))
  (huspace : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, ContDiffAt ℝ 2 (fun y ↦ u y t) x)
  (hutime : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ (u x) t)
  {x₀ : ℝ^n} (hx₀ : x₀ ∈ U) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioc 0 T)

include hU hconn hucont huspace hutime hx₀ ht₀

/-- A heat subsolution attaining its global maximum at an interior point at
positive time is constant on the entire closed cylinder before that time. -/
theorem eqOn_const_of_isMaxOn
    (hsub : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, heatParabolicOperator u x t ≤ 0)
    (hmax : IsMaxOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T) (x₀, t₀)) :
    EqOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (fun _ ↦ u x₀ t₀) (closedCylinder U t₀) := by
  apply matrix_strong_maximum_zero_potential hU hconn (show (0 : ℝ) < 1 by norm_num)
    (fun _ _ ↦ 1) (fun _ _ ↦ 0) (fun _ _ ↦ 0)
    continuousOn_const continuousOn_const continuousOn_const
    (fun _ _ _ _ ↦ Matrix.isSymm_one) (fun _ _ _ _ ↦ identity_ellipticity)
    hucont huspace hutime hx₀ ht₀ (fun _ _ _ _ ↦ rfl) ?_ hmax
  intro x hx t ht
  rw [← heatParabolicOperator_eq_matrixParabolicOperator]
  exact hsub x hx t ht

/-- A heat supersolution attaining its global minimum at an interior point at
positive time is constant on the entire closed cylinder before that time. -/
theorem eqOn_const_of_isMinOn
    (hsuper : ∀ x ∈ U, ∀ t ∈ Ioo 0 T, 0 ≤ heatParabolicOperator u x t)
    (hmin : IsMinOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (closedCylinder U T) (x₀, t₀)) :
    EqOn (fun p : ℝ^n × ℝ ↦ u p.1 p.2) (fun _ ↦ u x₀ t₀) (closedCylinder U t₀) := by
  apply matrix_strong_minimum_zero_potential hU hconn (show (0 : ℝ) < 1 by norm_num)
    (fun _ _ ↦ 1) (fun _ _ ↦ 0) (fun _ _ ↦ 0)
    continuousOn_const continuousOn_const continuousOn_const
    (fun _ _ _ _ ↦ Matrix.isSymm_one) (fun _ _ _ _ ↦ identity_ellipticity)
    hucont huspace hutime hx₀ ht₀ (fun _ _ _ _ ↦ rfl) ?_ hmin
  intro x hx t ht
  rw [← heatParabolicOperator_eq_matrixParabolicOperator]
  exact hsuper x hx t ht

end HeatEquation
