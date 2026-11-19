/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.Calculus.WeakFormIntegrands
public import CAS.ExactTactic
public import CAS.ClosedForm.Expression.Rotation

/-!
# Symbolic variational-integrand checks

In the weak formulation of Evans's §6.1.2, (7)-(9), a pointwise equation is replaced by integral
identities against test functions. SymLean's `cas` tactic checks the algebraic integrands of such
identities for sample functions in the plane: the Dirichlet integrand `∇u · ∇v`
(`quadratic_dirichlet_integrand_x`), the `L²` mass integrand (`coordinate_mass_integrand_xy`), the
Poisson and modified Helmholtz weak-form integrands (`quadratic_poisson_weak_integrand_x`,
`linear_modified_helmholtz_weak_integrand_xy`), and the symmetric-gradient energy density of a rigid
rotation (`rigid_rotation_sym_energy_integrand_zero`). The identities are also stated in Euclidean
coordinates and integrated over an arbitrary set `Ω`. The Sobolev and Lax-Milgram arguments of the
library do not depend on these checks.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.1.2 (Weak solutions), (7)-(9), pp. 313-314.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace VariationalEquation.Symbolic

open CAS
open CAS.Certificate
open CAS.Euclid2
open MeasureTheory

noncomputable section

/-! ## Shared sample expressions -/

/-- A quadratic trial function `u(x,y)=x²+y²`. -/
def quadraticTrial2 : Verified.Expr (Fin 2) :=
  x ^ 2 + y ^ 2

/-- Coordinate test function `v(x,y)=x`. -/
def coordinateTestX2 : Verified.Expr (Fin 2) :=
  x

/-- Coordinate test function `v(x,y)=y`. -/
def coordinateTestY2 : Verified.Expr (Fin 2) :=
  y

private theorem rotationField2_partialDeriv_00
    (p : ℝ^2) :
    (∂[(0 : Fin 2)]
      (fun q : ℝ^2 ↦ (rotationField2 (0 : Fin 2)).eval q)) p = 0 := by
  rw [Verified.Expr.partialDeriv_eval_eq
    (expr := rotationField2 (0 : Fin 2)) (x := p) (i := (0 : Fin 2))]
  · simp [rotationField2, Verified.Expr.eval,
      Verified.Expr.diff, Verified.Expr.SymVar.expr]
  · exact rotationField2_validAt p (0 : Fin 2)

private theorem rotationField2_partialDeriv_01
    (p : ℝ^2) :
    (∂[(1 : Fin 2)]
      (fun q : ℝ^2 ↦ (rotationField2 (0 : Fin 2)).eval q)) p = -1 := by
  rw [Verified.Expr.partialDeriv_eval_eq
    (expr := rotationField2 (0 : Fin 2)) (x := p) (i := (1 : Fin 2))]
  · simp [rotationField2, Verified.Expr.eval,
      Verified.Expr.diff, Verified.Expr.SymVar.expr]
  · exact rotationField2_validAt p (0 : Fin 2)

private theorem rotationField2_partialDeriv_10
    (p : ℝ^2) :
    (∂[(0 : Fin 2)]
      (fun q : ℝ^2 ↦ (rotationField2 (1 : Fin 2)).eval q)) p = 1 := by
  rw [Verified.Expr.partialDeriv_eval_eq
    (expr := rotationField2 (1 : Fin 2)) (x := p) (i := (0 : Fin 2))]
  · simp [rotationField2, Verified.Expr.eval,
      Verified.Expr.diff, Verified.Expr.SymVar.expr]
  · exact rotationField2_validAt p (1 : Fin 2)

private theorem rotationField2_partialDeriv_11
    (p : ℝ^2) :
    (∂[(1 : Fin 2)]
      (fun q : ℝ^2 ↦ (rotationField2 (1 : Fin 2)).eval q)) p = 0 := by
  rw [Verified.Expr.partialDeriv_eval_eq
    (expr := rotationField2 (1 : Fin 2)) (x := p) (i := (1 : Fin 2))]
  · simp [rotationField2, Verified.Expr.eval,
      Verified.Expr.diff, Verified.Expr.SymVar.expr]
  · exact rotationField2_validAt p (1 : Fin 2)

/-- The Euclidean symmetric-gradient entries of the rigid rotation `(-y,x)` vanish. -/
theorem rotationField2_symGrad_entry_zero
    (p : ℝ^2) (i j : Fin 2) :
    (∂[j]
        (fun q : ℝ^2 ↦ (rotationField2 i).eval q)) p +
      (∂[i]
        (fun q : ℝ^2 ↦ (rotationField2 j).eval q)) p = 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [rotationField2_partialDeriv_00, rotationField2_partialDeriv_01,
      rotationField2_partialDeriv_10, rotationField2_partialDeriv_11]

/-- Constant source used in the sample Poisson weak-form integrand. -/
def constantSource4_2 : Verified.Expr (Fin 2) :=
  4

/-- Difference residual for `∇(x²+y²) · ∇x = 2x`. -/
def quadraticDirichletIdentityResidualX2 : Verified.Expr (Fin 2) :=
  dirichletIntegrand quadraticTrial2 coordinateTestX2 -
    (2 * x : Verified.Expr (Fin 2))

/-- Difference residual for the sample `L²` mass-integrand identity. -/
def coordinateMassIdentityResidualXY : Verified.Expr (Fin 2) :=
  massIntegrand coordinateTestX2 coordinateTestY2 -
    (x * y : Verified.Expr (Fin 2))

/-- Small-strain energy density of the rigid planar rotation. -/
def rigidRotationSymEnergyIntegrand2 : Verified.Expr (Fin 2) :=
  symmetricGradientEnergyIntegrand rotationField2 rotationField2

/--
The Poisson weak-form integrand `∇u · ∇v - f v` for
`u=x²+y²`, `f=4`, and `v=x`.
-/
def quadraticPoissonWeakResidualX2 : Verified.Expr (Fin 2) :=
  poissonWeakResidualIntegrand quadraticTrial2 constantSource4_2 coordinateTestX2

/-- Difference residual for the sample Poisson weak-form integrand identity. -/
def quadraticPoissonWeakIdentityResidualX2 : Verified.Expr (Fin 2) :=
  quadraticPoissonWeakResidualX2 - (-(2 * x) : Verified.Expr (Fin 2))

/-- Fully simplified value of the sample Dirichlet-form integrand: `∇(x²+y²)·∇x = 2x`. -/
theorem quadratic_dirichlet_integrand_x_eval_eq_expected
    (p : ℝ^2) :
    (dirichletIntegrand quadraticTrial2 coordinateTestX2).eval p =
      (2 * x : Verified.Expr (Fin 2)).eval p := by
  rw [dirichletIntegrand_eval_eq_sum_partialDeriv_mul
    (u := quadraticTrial2) (v := coordinateTestX2) (x := p)
    (by symbolic_assumptions) (by symbolic_assumptions)]
  have hux := Verified.Expr.partialDeriv_eval_eq
    (expr := quadraticTrial2) (x := p) (i := (0 : Fin 2)) (by symbolic_assumptions)
  have huy := Verified.Expr.partialDeriv_eval_eq
    (expr := quadraticTrial2) (x := p) (i := (1 : Fin 2)) (by symbolic_assumptions)
  have hvx := Verified.Expr.partialDeriv_eval_eq
    (expr := coordinateTestX2) (x := p) (i := (0 : Fin 2)) (by symbolic_assumptions)
  have hvy := Verified.Expr.partialDeriv_eval_eq
    (expr := coordinateTestX2) (x := p) (i := (1 : Fin 2)) (by symbolic_assumptions)
  rw [Fin.sum_univ_two, hux, huy, hvx, hvy]
  cas [quadraticTrial2, coordinateTestX2,
    Verified.Expr.diff, Verified.Expr.eval, Verified.Expr.SymVar.expr]

private theorem quadratic_dirichlet_identity_residual_x_eval_zero
    (p : ℝ^2) : quadraticDirichletIdentityResidualX2.eval p = 0 := by
  change
    (dirichletIntegrand quadraticTrial2 coordinateTestX2).eval p -
      (2 * x : Verified.Expr (Fin 2)).eval p = 0
  rw [quadratic_dirichlet_integrand_x_eval_eq_expected]
  simp

private theorem coordinate_mass_identity_residual_xy_eval_zero
    (p : ℝ^2) : coordinateMassIdentityResidualXY.eval p = 0 := by
  change
    (massIntegrand coordinateTestX2 coordinateTestY2).eval p -
      (x * y : Verified.Expr (Fin 2)).eval p = 0
  rw [massIntegrand_eval_eq_mul]
  cas [coordinateTestX2, coordinateTestY2,
    Verified.Expr.eval, Verified.Expr.SymVar.expr]

private theorem rigid_rotation_sym_energy_integrand2_eval_zero
    (p : ℝ^2) : rigidRotationSymEnergyIntegrand2.eval p = 0 := by
  change (symmetricGradientEnergyIntegrand rotationField2 rotationField2).eval p = 0
  rw [symmetricGradientEnergyIntegrand_eval_eq_sum_partialDeriv_average_mul_average
    (u := rotationField2) (v := rotationField2) (x := p)
    (rotationField2_validAt p) (rotationField2_validAt p)]
  simp [rotationField2_symGrad_entry_zero p]

private theorem quadratic_poisson_weak_identity_residual_x_eval_zero
    (p : ℝ^2) : quadraticPoissonWeakIdentityResidualX2.eval p = 0 := by
  change
    quadraticPoissonWeakResidualX2.eval p -
      (-(2 * x) : Verified.Expr (Fin 2)).eval p = 0
  unfold quadraticPoissonWeakResidualX2
  rw [poissonWeakResidualIntegrand_eval_eq_sum_partialDeriv_mul_sub
    (u := quadraticTrial2) (f := constantSource4_2) (v := coordinateTestX2) (x := p)
    (by symbolic_assumptions) (by symbolic_assumptions)]
  rw [← dirichletIntegrand_eval_eq_sum_partialDeriv_mul
    (u := quadraticTrial2) (v := coordinateTestX2) (x := p)
    (by symbolic_assumptions) (by symbolic_assumptions)]
  rw [quadratic_dirichlet_integrand_x_eval_eq_expected]
  cas [constantSource4_2, coordinateTestX2,
    Verified.Expr.eval, Verified.Expr.SymVar.expr]

private theorem residualBound_univ_zero_of_forall_eq_zero
    (f : ℝ^2 → ℝ) (h : ∀ p, f p = 0) :
    ResidualBound f Set.univ 0 := by
  intro p _hp
  simp [h p]

private theorem integral_eq_zero_of_forall_eq_zero
    (f : ℝ^2 → ℝ) (h : ∀ p, f p = 0) (Ω : Set (ℝ^2)) :
    (∫ p in Ω, f p) = 0 := by
  calc
    (∫ p in Ω, f p) = ∫ _p in Ω, (0 : ℝ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with p
      exact h p
    _ = 0 := by simp

/-! ## Dirichlet and mass-form integrands -/

/-- Checked Dirichlet-form integrand identity: `∇(x²+y²) · ∇x = 2x`. -/
theorem quadratic_dirichlet_integrand_x :
    ResidualBound
      (fun p : ℝ^2 ↦ quadraticDirichletIdentityResidualX2.eval p) Set.univ 0 := by
  exact residualBound_univ_zero_of_forall_eq_zero _
    quadratic_dirichlet_identity_residual_x_eval_zero

/-- Checked `L²` mass-form integrand identity: `x*y = x*y`. -/
theorem coordinate_mass_integrand_xy :
    ResidualBound
      (fun p : ℝ^2 ↦ coordinateMassIdentityResidualXY.eval p) Set.univ 0 := by
  exact residualBound_univ_zero_of_forall_eq_zero _
    coordinate_mass_identity_residual_xy_eval_zero

/--
Checked symmetric-gradient energy identity:
a rigid planar rotation has zero small-strain energy density.
-/
theorem rigid_rotation_sym_energy_integrand_zero :
    ResidualBound
      (fun p : ℝ^2 ↦ rigidRotationSymEnergyIntegrand2.eval p) Set.univ 0 := by
  exact residualBound_univ_zero_of_forall_eq_zero _
    rigid_rotation_sym_energy_integrand2_eval_zero

/--
Public equality theorem for the sample Dirichlet-form integrand.

The `cas` tactic proves the closed-form symbolic equality once, and the pointwise and
integral lemmas use the resulting `Set.EqOn` statement.
-/
theorem quadratic_dirichlet_integrand_x_symbolic_eq :
    Set.EqOn
      (fun p : ℝ^2 ↦ (dirichletIntegrand quadraticTrial2 coordinateTestX2).eval p)
      (fun p : ℝ^2 ↦ (2 * x : Verified.Expr (Fin 2)).eval p)
      Set.univ := by
  intro p _hp
  have h := quadratic_dirichlet_identity_residual_x_eval_zero p
  apply sub_eq_zero.mp
  simpa [quadraticDirichletIdentityResidualX2, Verified.Expr.eval] using h

/-- Public equality theorem for the sample `L²` mass integrand. -/
theorem coordinate_mass_integrand_xy_symbolic_eq :
    Set.EqOn
      (fun p : ℝ^2 ↦ (massIntegrand coordinateTestX2 coordinateTestY2).eval p)
      (fun p : ℝ^2 ↦ (x * y : Verified.Expr (Fin 2)).eval p)
      Set.univ := by
  intro p _hp
  have h := coordinate_mass_identity_residual_xy_eval_zero p
  apply sub_eq_zero.mp
  simpa [coordinateMassIdentityResidualXY, Verified.Expr.eval] using h

/-- Public equality theorem for the rigid-rotation symmetric-gradient energy density. -/
theorem rigid_rotation_sym_energy_integrand_symbolic_eq :
    Set.EqOn
      (fun p : ℝ^2 ↦
        (symmetricGradientEnergyIntegrand rotationField2 rotationField2).eval p)
      (fun p : ℝ^2 ↦ (0 : Verified.Expr (Fin 2)).eval p)
      Set.univ := by
  intro p _hp
  simpa [rigidRotationSymEnergyIntegrand2, Verified.Expr.eval] using
    rigid_rotation_sym_energy_integrand2_eval_zero p

/--
Euclidean derivative form of the Dirichlet-form integrand.

The integrand `∇u · ∇v` is the principal part of the bilinear form (8) of Evans's §6.1.2
with identity coefficients. The `cas` tactic proves its closed form, and the theorem
restates it with Euclidean coordinate partial derivatives.
-/
theorem quadratic_dirichlet_integrand_x_eval_eq_euclidean_derivatives
    (p : ℝ^2) :
    (dirichletIntegrand quadraticTrial2 coordinateTestX2).eval p =
      ∑ i : Fin 2,
        (∂[i]
          (fun q : ℝ^2 ↦ quadraticTrial2.eval q)) p *
          (∂[i]
            (fun q : ℝ^2 ↦ coordinateTestX2.eval q)) p := by
  exact dirichletIntegrand_eval_eq_sum_partialDeriv_mul
    (u := quadraticTrial2) (v := coordinateTestX2) (x := p)
    (by symbolic_assumptions) (by symbolic_assumptions)

/-- Euclidean product form of the `L²` mass integrand. -/
theorem coordinate_mass_integrand_xy_eval_eq_product
    (p : ℝ^2) :
    (massIntegrand coordinateTestX2 coordinateTestY2).eval p =
      coordinateTestX2.eval p * coordinateTestY2.eval p := by
  exact massIntegrand_eval_eq_mul
    (u := coordinateTestX2) (v := coordinateTestY2) (x := p)

/-- Fully simplified value of the sample mass-form integrand: `x*y = x*y`. -/
theorem coordinate_mass_integrand_xy_eval_eq_expected
    (p : ℝ^2) :
    (massIntegrand coordinateTestX2 coordinateTestY2).eval p =
      (x * y : Verified.Expr (Fin 2)).eval p := by
  exact coordinate_mass_integrand_xy_symbolic_eq trivial

/-- Integrated Euclidean derivative form of the Dirichlet-form identity. -/
theorem quadratic_dirichlet_integrand_x_integral_eq_euclidean_derivatives
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, (dirichletIntegrand quadraticTrial2 coordinateTestX2).eval q) =
      ∫ q in Ω,
        (∑ i : Fin 2,
          (∂[i]
            (fun r : ℝ^2 ↦ quadraticTrial2.eval r)) q *
            (∂[i]
              (fun r : ℝ^2 ↦ coordinateTestX2.eval r)) q) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact quadratic_dirichlet_integrand_x_eval_eq_euclidean_derivatives q

/-- Integrated Euclidean product form of the mass-form identity. -/
theorem coordinate_mass_integrand_xy_integral_eq_product
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, (massIntegrand coordinateTestX2 coordinateTestY2).eval q) =
      ∫ q in Ω, coordinateTestX2.eval q * coordinateTestY2.eval q := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact coordinate_mass_integrand_xy_eval_eq_product q

/-- Integrated closed-form identity for the Dirichlet-form building block. -/
theorem quadratic_dirichlet_integrand_x_integral_eq_expected
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, (dirichletIntegrand quadraticTrial2 coordinateTestX2).eval q) =
      ∫ q in Ω, (2 * x : Verified.Expr (Fin 2)).eval q := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact quadratic_dirichlet_integrand_x_eval_eq_expected q

/-- Integrated closed-form identity for the mass-form building block. -/
theorem coordinate_mass_integrand_xy_integral_eq_expected
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, (massIntegrand coordinateTestX2 coordinateTestY2).eval q) =
      ∫ q in Ω, (x * y : Verified.Expr (Fin 2)).eval q := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact coordinate_mass_integrand_xy_eval_eq_expected q

/-- Euclidean coordinate-partial density for the sample Dirichlet-form identity. -/
def quadraticDirichletDensityX2 (q : ℝ^2) : ℝ :=
  ∑ i : Fin 2,
    (∂[i]
      (fun r : ℝ^2 ↦ quadraticTrial2.eval r)) q *
      (∂[i]
        (fun r : ℝ^2 ↦ coordinateTestX2.eval r)) q

/-- Closed-form density `2x` for the sample Dirichlet-form identity. -/
def quadraticDirichletExpectedDensityX2 (q : ℝ^2) : ℝ :=
  (2 * x : Verified.Expr (Fin 2)).eval q

/-- Pointwise Euclidean Dirichlet density identity: `∇(x²+y²) · ∇x = 2x`. -/
theorem quadratic_dirichlet_density_eq_expected
    (p : ℝ^2) :
    quadraticDirichletDensityX2 p = quadraticDirichletExpectedDensityX2 p := by
  unfold quadraticDirichletDensityX2 quadraticDirichletExpectedDensityX2
  rw [← quadratic_dirichlet_integrand_x_eval_eq_euclidean_derivatives p]
  exact quadratic_dirichlet_integrand_x_eval_eq_expected p

/--
Euclidean Dirichlet density identity:
`∇(x²+y²) · ∇x` integrates to `2x`.
-/
theorem quadratic_dirichlet_density_integral_eq_expected
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, quadraticDirichletDensityX2 q) =
      ∫ q in Ω, quadraticDirichletExpectedDensityX2 q := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact quadratic_dirichlet_density_eq_expected q

/--
Euclidean symmetric-gradient energy form for the rigid rotation example.

The right-hand side is the small-strain energy density `∑ ε_ij ε_ij` of linear elasticity,
with `ε = (Du + Duᵀ)/2`, written with coordinate partial derivatives.
-/
theorem rigid_rotation_sym_energy_integrand_eval_eq_euclidean_derivatives
    (p : ℝ^2) :
    (symmetricGradientEnergyIntegrand rotationField2 rotationField2).eval p =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (((∂[j]
              (fun q : ℝ^2 ↦ (rotationField2 i).eval q)) p +
            (∂[i]
              (fun q : ℝ^2 ↦ (rotationField2 j).eval q)) p) / 2) *
          (((∂[j]
                (fun q : ℝ^2 ↦ (rotationField2 i).eval q)) p +
              (∂[i]
                (fun q : ℝ^2 ↦ (rotationField2 j).eval q)) p) / 2) := by
  exact symmetricGradientEnergyIntegrand_eval_eq_sum_partialDeriv_average_mul_average
    (u := rotationField2) (v := rotationField2) (x := p)
    (rotationField2_validAt p) (rotationField2_validAt p)

/-- Simplified value of the rigid-rotation symmetric-gradient energy density. -/
theorem rigid_rotation_sym_energy_integrand_eval_eq_zero
    (p : ℝ^2) :
    (symmetricGradientEnergyIntegrand rotationField2 rotationField2).eval p = 0 := by
  rw [rigid_rotation_sym_energy_integrand_eval_eq_euclidean_derivatives p]
  simp [rotationField2_symGrad_entry_zero p]

/-- Euclidean coordinate-partial small-strain energy density for the rigid rotation. -/
def rigidRotationSymEnergyDensity2 (q : ℝ^2) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    (((∂[j]
          (fun r : ℝ^2 ↦ (rotationField2 i).eval r)) q +
        (∂[i]
          (fun r : ℝ^2 ↦ (rotationField2 j).eval r)) q) / 2) *
      (((∂[j]
            (fun r : ℝ^2 ↦ (rotationField2 i).eval r)) q +
          (∂[i]
            (fun r : ℝ^2 ↦ (rotationField2 j).eval r)) q) / 2)

/-- The Euclidean coordinate-partial small-strain energy density of `(-y,x)` is zero. -/
theorem rigidRotationSymEnergyDensity2_eq_zero
    (q : ℝ^2) :
    rigidRotationSymEnergyDensity2 q = 0 := by
  simp [rigidRotationSymEnergyDensity2, rotationField2_symGrad_entry_zero q]

/-- Integrated Euclidean form for the rigid-rotation symmetric energy density. -/
theorem rigid_rotation_sym_energy_integrand_integral_eq_euclidean_derivatives
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, (symmetricGradientEnergyIntegrand rotationField2 rotationField2).eval q) =
      ∫ q in Ω,
        (∑ i : Fin 2, ∑ j : Fin 2,
          (((∂[j]
                (fun r : ℝ^2 ↦ (rotationField2 i).eval r)) q +
              (∂[i]
                (fun r : ℝ^2 ↦ (rotationField2 j).eval r)) q) / 2) *
            (((∂[j]
                  (fun r : ℝ^2 ↦ (rotationField2 i).eval r)) q +
                (∂[i]
                  (fun r : ℝ^2 ↦ (rotationField2 j).eval r)) q) / 2)) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact rigid_rotation_sym_energy_integrand_eval_eq_euclidean_derivatives q

/-- Integrated closed-form zero identity for rigid-rotation symmetric energy. -/
theorem rigid_rotation_sym_energy_integrand_integral_eq_zero
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω,
      (symmetricGradientEnergyIntegrand rotationField2 rotationField2).eval q) =
        0 := by
  calc
    (∫ q in Ω,
      (symmetricGradientEnergyIntegrand rotationField2 rotationField2).eval q) =
        ∫ _q in Ω, (0 : ℝ) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with q
          exact rigid_rotation_sym_energy_integrand_eval_eq_zero q
    _ = 0 := by simp

/-- Euclidean coordinate-partial integral zero for rigid-rotation small-strain energy. -/
theorem rigid_rotation_sym_energy_density_integral_zero
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, rigidRotationSymEnergyDensity2 q) = 0 := by
  calc
    (∫ q in Ω, rigidRotationSymEnergyDensity2 q) =
        ∫ _q in Ω, (0 : ℝ) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with q
          exact rigidRotationSymEnergyDensity2_eq_zero q
    _ = 0 := by simp

/-- Certified residual integral for the rigid-rotation symmetric-energy identity. -/
theorem rigid_rotation_sym_energy_residual_integral_zero
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, rigidRotationSymEnergyIntegrand2.eval q) = 0 := by
  exact integral_eq_zero_of_forall_eq_zero _
    rigid_rotation_sym_energy_integrand2_eval_zero Ω

/-- Zero-error CEGA certificate for the rigid-rotation symmetric-energy residual. -/
theorem rigid_rotation_sym_energy_zero_error :
    ApproxOn
      (fun p : ℝ^2 ↦ rigidRotationSymEnergyIntegrand2.eval p)
      (fun _p ↦ 0)
      Set.univ
      0 := by
  exact rigid_rotation_sym_energy_integrand_zero

/--
Certified residual integral for the Dirichlet-form building block:
after subtracting `2x`, the certified integrand integrates to zero.
-/
theorem quadratic_dirichlet_integrand_x_residual_integral_zero
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, quadraticDirichletIdentityResidualX2.eval q) = 0 := by
  exact integral_eq_zero_of_forall_eq_zero _
    quadratic_dirichlet_identity_residual_x_eval_zero Ω

/-- Zero-error CEGA certificate for the Dirichlet-form building block. -/
theorem quadratic_dirichlet_integrand_x_zero_error :
    ApproxOn
      (fun p : ℝ^2 ↦ quadraticDirichletIdentityResidualX2.eval p)
      (fun _p ↦ 0)
      Set.univ
      0 := by
  exact quadratic_dirichlet_integrand_x

/--
Certified residual integral for the mass-form building block:
after subtracting `x*y`, the certified integrand integrates to zero.
-/
theorem coordinate_mass_integrand_xy_residual_integral_zero
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, coordinateMassIdentityResidualXY.eval q) = 0 := by
  exact integral_eq_zero_of_forall_eq_zero _
    coordinate_mass_identity_residual_xy_eval_zero Ω

/-- Zero-error CEGA certificate for the mass-form building block. -/
theorem coordinate_mass_integrand_xy_zero_error :
    ApproxOn
      (fun p : ℝ^2 ↦ coordinateMassIdentityResidualXY.eval p)
      (fun _p ↦ 0)
      Set.univ
      0 := by
  exact coordinate_mass_integrand_xy

/-! ## Poisson weak-form integrands -/

/--
Checked Poisson weak-form integrand identity:
`∇(x²+y²)·∇x - 4x = -2x`.
-/
theorem quadratic_poisson_weak_integrand_x :
    ResidualBound
      (fun p : ℝ^2 ↦ quadraticPoissonWeakIdentityResidualX2.eval p) Set.univ 0 := by
  exact residualBound_univ_zero_of_forall_eq_zero _
    quadratic_poisson_weak_identity_residual_x_eval_zero

/-- Public equality theorem for the sample Poisson weak-form integrand. -/
theorem quadratic_poisson_weak_integrand_x_symbolic_eq :
    Set.EqOn
      (fun p : ℝ^2 ↦ quadraticPoissonWeakResidualX2.eval p)
      (fun p : ℝ^2 ↦ (-(2 * x) : Verified.Expr (Fin 2)).eval p)
      Set.univ := by
  intro p _hp
  apply sub_eq_zero.mp
  simpa [quadraticPoissonWeakIdentityResidualX2, Verified.Expr.eval] using
    quadratic_poisson_weak_identity_residual_x_eval_zero p

/--
Euclidean derivative form of the same Poisson weak-form integrand.

The integrand `∇u · ∇v - f v` is that of the weak formulation (9) of Evans's §6.1.2 for
`-Δu = f`. The `cas` tactic proves its closed form, and the theorem restates it with the
Euclidean `partialDeriv` gradients.
-/
theorem quadratic_poisson_weak_integrand_x_eval_eq_euclidean_derivatives
    (p : ℝ^2) :
    quadraticPoissonWeakResidualX2.eval p =
      (∑ i : Fin 2,
        (∂[i]
          (fun q : ℝ^2 ↦ quadraticTrial2.eval q)) p *
          (∂[i]
            (fun q : ℝ^2 ↦ coordinateTestX2.eval q)) p) -
        constantSource4_2.eval p * coordinateTestX2.eval p := by
  exact poissonWeakResidualIntegrand_eval_eq_sum_partialDeriv_mul_sub
    (u := quadraticTrial2) (f := constantSource4_2) (v := coordinateTestX2) (x := p)
    (by symbolic_assumptions) (by symbolic_assumptions)

/--
Fully simplified Euclidean weak-form value for the sample Poisson integrand:
`∇(x²+y²)·∇x - 4x = -2x`.
-/
theorem quadratic_poisson_weak_integrand_x_eval_eq_expected
    (p : ℝ^2) :
    quadraticPoissonWeakResidualX2.eval p = (-(2 * x) : Verified.Expr (Fin 2)).eval p := by
  exact quadratic_poisson_weak_integrand_x_symbolic_eq trivial

/--
Integrated weak-form identity for the sample Poisson integrand.

The `cas` tactic proves the integrand identity pointwise, and integration gives it over
every set `Ω`.
-/
theorem quadratic_poisson_weak_integrand_x_integral_eq_expected
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, quadraticPoissonWeakResidualX2.eval q) =
      ∫ q in Ω, (-(2 * x) : Verified.Expr (Fin 2)).eval q := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact quadratic_poisson_weak_integrand_x_eval_eq_expected q

/--
Integrated Euclidean derivative form of the same weak-form identity.
-/
theorem quadratic_poisson_weak_integrand_x_integral_eq_euclidean_derivatives
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, quadraticPoissonWeakResidualX2.eval q) =
      ∫ q in Ω,
        ((∑ i : Fin 2,
          (∂[i]
            (fun r : ℝ^2 ↦ quadraticTrial2.eval r)) q *
            (∂[i]
            (fun r : ℝ^2 ↦ coordinateTestX2.eval r)) q) -
          constantSource4_2.eval q * coordinateTestX2.eval q) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact quadratic_poisson_weak_integrand_x_eval_eq_euclidean_derivatives q

/--
Certified residual integral: after subtracting the expected closed form,
the CAS-certified Poisson weak-form residual integrates to zero over any domain.
-/
theorem quadratic_poisson_weak_integrand_x_residual_integral_zero
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, quadraticPoissonWeakIdentityResidualX2.eval q) = 0 := by
  exact integral_eq_zero_of_forall_eq_zero _
    quadratic_poisson_weak_identity_residual_x_eval_zero Ω

/--
Zero-error CEGA certificate for the same weak-form integrand residual.
A quadrature or Galerkin proof can use it in this form.
-/
theorem quadratic_poisson_weak_integrand_x_zero_error :
    ApproxOn
      (fun p : ℝ^2 ↦ quadraticPoissonWeakIdentityResidualX2.eval p)
      (fun _p ↦ 0)
      Set.univ
      0 := by
  exact quadratic_poisson_weak_integrand_x

/-! ## Modified Helmholtz weak-form integrands -/

/-- Modified Helmholtz integrand for `κ=1`, `u=x`, `f=0`, and `v=y`. -/
def linearModifiedHelmholtzWeakIntegrandXY : Verified.Expr (Fin 2) :=
  modifiedHelmholtzWeakResidualIntegrand
    (1 : Verified.Expr (Fin 2)) (x : Verified.Expr (Fin 2))
    (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2))

/-- Difference residual for the sample modified Helmholtz integrand identity. -/
def linearModifiedHelmholtzWeakIdentityResidualXY : Verified.Expr (Fin 2) :=
  linearModifiedHelmholtzWeakIntegrandXY - (x * y : Verified.Expr (Fin 2))

private theorem linear_modified_helmholtz_weak_integrand_xy_eval_eq_expected_aux
    (p : ℝ^2) :
    linearModifiedHelmholtzWeakIntegrandXY.eval p =
      (x * y : Verified.Expr (Fin 2)).eval p := by
  unfold linearModifiedHelmholtzWeakIntegrandXY
  rw [modifiedHelmholtzWeakResidualIntegrand_eval_eq_sum_partialDeriv_mul_add_sub
    (κ := (1 : Verified.Expr (Fin 2))) (u := (x : Verified.Expr (Fin 2)))
    (f := (0 : Verified.Expr (Fin 2))) (v := (y : Verified.Expr (Fin 2))) (x := p)
    (by symbolic_assumptions) (by symbolic_assumptions)]
  have hxx := Verified.Expr.partialDeriv_eval_eq
    (expr := (x : Verified.Expr (Fin 2))) (x := p) (i := (0 : Fin 2))
    (by symbolic_assumptions)
  have hxy := Verified.Expr.partialDeriv_eval_eq
    (expr := (x : Verified.Expr (Fin 2))) (x := p) (i := (1 : Fin 2))
    (by symbolic_assumptions)
  have hyx := Verified.Expr.partialDeriv_eval_eq
    (expr := (y : Verified.Expr (Fin 2))) (x := p) (i := (0 : Fin 2))
    (by symbolic_assumptions)
  have hyy := Verified.Expr.partialDeriv_eval_eq
    (expr := (y : Verified.Expr (Fin 2))) (x := p) (i := (1 : Fin 2))
    (by symbolic_assumptions)
  rw [Fin.sum_univ_two, hxx, hxy, hyx, hyy]
  cas [Verified.Expr.diff, Verified.Expr.eval, Verified.Expr.SymVar.expr]

private theorem linear_modified_helmholtz_weak_identity_residual_xy_eval_zero
    (p : ℝ^2) : linearModifiedHelmholtzWeakIdentityResidualXY.eval p = 0 := by
  change
    linearModifiedHelmholtzWeakIntegrandXY.eval p -
      (x * y : Verified.Expr (Fin 2)).eval p = 0
  rw [linear_modified_helmholtz_weak_integrand_xy_eval_eq_expected_aux]
  simp

/--
Checked modified Helmholtz weak-form integrand identity:
for `κ=1`, `u=x`, `f=0`, and test `v=y`, the integrand is `x*y`.
-/
theorem linear_modified_helmholtz_weak_integrand_xy :
    ResidualBound
      (fun p : ℝ^2 ↦ linearModifiedHelmholtzWeakIdentityResidualXY.eval p)
      Set.univ 0 := by
  exact residualBound_univ_zero_of_forall_eq_zero _
    linear_modified_helmholtz_weak_identity_residual_xy_eval_zero

/-- Public equality theorem for the sample modified Helmholtz weak-form integrand. -/
theorem linear_modified_helmholtz_weak_integrand_xy_symbolic_eq :
    Set.EqOn
      (fun p : ℝ^2 ↦
        (modifiedHelmholtzWeakResidualIntegrand
          (1 : Verified.Expr (Fin 2)) (x : Verified.Expr (Fin 2))
          (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2))).eval p)
      (fun p : ℝ^2 ↦ (x * y : Verified.Expr (Fin 2)).eval p)
      Set.univ := by
  intro p _hp
  simpa [linearModifiedHelmholtzWeakIntegrandXY] using
    linear_modified_helmholtz_weak_integrand_xy_eval_eq_expected_aux p

/-- Euclidean derivative form of the sample modified Helmholtz weak-form integrand. -/
theorem linear_modified_helmholtz_weak_integrand_xy_eval_eq_euclidean_derivatives
    (p : ℝ^2) :
    (modifiedHelmholtzWeakResidualIntegrand
        (1 : Verified.Expr (Fin 2)) (x : Verified.Expr (Fin 2))
        (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2))).eval p =
      (∑ i : Fin 2,
        (∂[i] (fun q : ℝ^2 ↦ (x : Verified.Expr (Fin 2)).eval q)) p *
          (∂[i]
            (fun q : ℝ^2 ↦ (y : Verified.Expr (Fin 2)).eval q)) p) +
        (1 : Verified.Expr (Fin 2)).eval p * (x : Verified.Expr (Fin 2)).eval p *
          (y : Verified.Expr (Fin 2)).eval p -
        (0 : Verified.Expr (Fin 2)).eval p * (y : Verified.Expr (Fin 2)).eval p := by
  exact modifiedHelmholtzWeakResidualIntegrand_eval_eq_sum_partialDeriv_mul_add_sub
    (κ := (1 : Verified.Expr (Fin 2))) (u := (x : Verified.Expr (Fin 2)))
    (f := (0 : Verified.Expr (Fin 2)))
    (v := (y : Verified.Expr (Fin 2))) (x := p) (by symbolic_assumptions) (by symbolic_assumptions)

/-- Fully simplified Euclidean weak-form value for the sample Helmholtz integrand. -/
theorem linear_modified_helmholtz_weak_integrand_xy_eval_eq_expected
    (p : ℝ^2) :
    (modifiedHelmholtzWeakResidualIntegrand
        (1 : Verified.Expr (Fin 2)) (x : Verified.Expr (Fin 2))
        (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2))).eval p =
      (x * y : Verified.Expr (Fin 2)).eval p := by
  exact linear_modified_helmholtz_weak_integrand_xy_symbolic_eq trivial

/-- Integrated weak-form identity for the sample Helmholtz integrand. -/
theorem linear_modified_helmholtz_weak_integrand_xy_integral_eq_expected
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω,
      (modifiedHelmholtzWeakResidualIntegrand
        (1 : Verified.Expr (Fin 2)) (x : Verified.Expr (Fin 2))
        (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2))).eval q) =
      ∫ q in Ω, (x * y : Verified.Expr (Fin 2)).eval q := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact linear_modified_helmholtz_weak_integrand_xy_eval_eq_expected q

/-- Integrated Euclidean derivative form for the sample modified Helmholtz weak integrand. -/
theorem linear_modified_helmholtz_weak_integrand_xy_integral_eq_euclidean_derivatives
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω,
      (modifiedHelmholtzWeakResidualIntegrand
        (1 : Verified.Expr (Fin 2)) (x : Verified.Expr (Fin 2))
        (0 : Verified.Expr (Fin 2)) (y : Verified.Expr (Fin 2))).eval q) =
      ∫ q in Ω,
        ((∑ i : Fin 2,
          (∂[i]
              (fun r : ℝ^2 ↦ (x : Verified.Expr (Fin 2)).eval r)) q *
            (∂[i]
              (fun r : ℝ^2 ↦ (y : Verified.Expr (Fin 2)).eval r)) q) +
          (1 : Verified.Expr (Fin 2)).eval q * (x : Verified.Expr (Fin 2)).eval q *
            (y : Verified.Expr (Fin 2)).eval q -
          (0 : Verified.Expr (Fin 2)).eval q * (y : Verified.Expr (Fin 2)).eval q) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  exact linear_modified_helmholtz_weak_integrand_xy_eval_eq_euclidean_derivatives q

/--
Certified residual integral: after subtracting the expected closed form,
the CAS-certified modified Helmholtz weak-form residual integrates to zero over any domain.
-/
theorem linear_modified_helmholtz_weak_integrand_xy_residual_integral_zero
    (Ω : Set (ℝ^2)) :
    (∫ q in Ω, linearModifiedHelmholtzWeakIdentityResidualXY.eval q) = 0 := by
  exact integral_eq_zero_of_forall_eq_zero _
    linear_modified_helmholtz_weak_identity_residual_xy_eval_zero Ω

/-- Zero-error CEGA certificate for the sample modified Helmholtz weak-form residual. -/
theorem linear_modified_helmholtz_weak_integrand_xy_zero_error :
    ApproxOn
      (fun p : ℝ^2 ↦ linearModifiedHelmholtzWeakIdentityResidualXY.eval p)
      (fun _p ↦ 0)
      Set.univ
      0 := by
  exact linear_modified_helmholtz_weak_integrand_xy

end

end VariationalEquation.Symbolic
