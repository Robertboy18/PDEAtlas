/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.Viscosity
public import PDE.Hyperbolic.HamiltonJacobi.Equation
public import PDE.Problem.Equation.Satisfaction
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Affine solutions for the quadratic Hamiltonian

For the Hamiltonian `H(p, t, x) = ‖p‖²`, the affine family

`u(t, x) = ⟪a, x⟫ - t ‖a‖²`

solves the general Hamilton–Jacobi equation. We also treat the
one-dimensional profile `u(t, x) = x - t` and its viscosity-solution
and PDE statements.

Plane-wave data `⟪a, x⟫` never break for a Hamiltonian that depends only on the momentum:
`Du = a` is constant, so `u_t = -H(a)`. The equation is (1) of Evans, §3.3. The viscosity
statement is the observation opening §10.1.2 that a classical solution satisfies the touching
inequalities (16)-(17) of §10.1.1. The partial derivatives of the one-dimensional profile are
computed by the SymLean `cas` tactic.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3, equation (1); §10.1.1, definition of viscosity
  solution, (16)-(17); §10.1.2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv SatisfiesPDEProblem spatialGradient)

namespace NonlinearFirstOrder

open PDE.Common
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Quadratic Hamiltonian: `H(p, t, x) = ‖p‖²`. -/
noncomputable def squaredNormHamiltonian (n : ℕ) :
    ℝ^n → ℝ → ℝ^n → ℝ :=
  fun p _t _x ↦ ‖p‖ ^ 2

/-- The affine Hamilton–Jacobi solution `(t, x) ↦ ⟪a, x⟫ - t ‖a‖²` as a continuous linear map on
spacetime, the form in which its Fréchet derivative is read off directly. -/
noncomputable def hjLinearCLM (a : ℝ^n) : ℝ^(n + 1) →L[ℝ] ℝ :=
  (innerSL ℝ a).comp (spatialPartCLM n) -
    (EuclideanSpace.proj (0 : Fin (n + 1))).smulRight (‖a‖ ^ 2)

/-- The affine Hamilton–Jacobi solution `u(t, x) = ⟪a, x⟫ - t ‖a‖²`. -/
noncomputable def hjLinearSolution (a : ℝ^n) : ℝ^(n + 1) → ℝ :=
  hjLinearCLM (n := n) a

private theorem partialDeriv_time_hjLinearSolution (a : ℝ^n) (xt : ℝ^(n + 1)) :
    (∂[0] (hjLinearSolution (n := n) a)) xt = -(‖a‖ ^ 2) := by
  unfold hjLinearSolution partialDeriv
  have hfderiv : fderiv ℝ (hjLinearCLM (n := n) a) xt = hjLinearCLM (n := n) a :=
    ContinuousLinearMap.fderiv (hjLinearCLM (n := n) a) (x := xt)
  rw [hfderiv]
  unfold hjLinearCLM
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    spatialPartCLM_single_zero n]

private theorem partialDeriv_spatial_hjLinearSolution (a : ℝ^n) (i : Fin n) (xt : ℝ^(n + 1)) :
    (∂[i.succ] (hjLinearSolution (n := n) a)) xt = a i := by
  unfold hjLinearSolution partialDeriv
  have hfderiv : fderiv ℝ (hjLinearCLM (n := n) a) xt = hjLinearCLM (n := n) a :=
    ContinuousLinearMap.fderiv (hjLinearCLM (n := n) a) (x := xt)
  rw [hfderiv]
  unfold hjLinearCLM
  have h0 : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    EuclideanSpace.proj, h0, spatialPartCLM_single_succ n, innerSL_apply_apply,
    EuclideanSpace.inner_single_right]

private theorem spatial_gradient_hjLinearSolution (a : ℝ^n) (xt : ℝ^(n + 1)) :
    spatialGradient (n := n) (hjLinearSolution (n := n) a) xt = a := by
  ext i
  simp [spatialGradient, spatialPartCLM_apply, PDE.gradient_apply_eq_partialDeriv,
    partialDeriv_spatial_hjLinearSolution (n := n) a i xt]

/-- The affine quadratic-Hamiltonian family satisfies the bundled PDE problem. -/
theorem hjLinearSolution_satisfiesPDEProblem (a : ℝ^n) :
    SatisfiesPDEProblem (hamiltonJacobiEquation (n := n) (H := squaredNormHamiltonian n)
      (U := Set.univ)) (hjLinearSolution (n := n) a) := by
  let : Fact (0 < n + 1) := ⟨Nat.succ_pos n⟩
  intro eqn heqn xt hxt
  have heq : eqn =
        { Output := ℝ
          operator := fun u xt ↦ (∂[0] u) xt + squaredNormHamiltonian n
                (spatialGradient (n := n) u xt) (xt 0) (spatialPartCLM n xt)
          rhs := fun _ ↦ 0
          domain := (Set.univ : Set (ℝ^(n + 1))) } := by
    simpa [hamiltonJacobiEquation, squaredNormHamiltonian] using heqn
  subst heq
  simp [squaredNormHamiltonian, partialDeriv_time_hjLinearSolution (n := n) a xt,
    spatial_gradient_hjLinearSolution (n := n) a xt] at *

end NonlinearFirstOrder

namespace HamiltonJacobi1D

open PDE.Common

noncomputable section

/-- The affine spacetime profile `u(t, x) = x - t`. -/
def affineQuadraticSolution : ℝ^2 → ℝ :=
  fun q ↦ q 1 - q 0

private theorem affineQuadraticSolution_residual_zero (p : ℝ^2) :
    (∂[(0 : Fin 2)] affineQuadraticSolution) p +
      ((∂[(1 : Fin 2)] affineQuadraticSolution) p) ^ 2 = 0 := by
  have ht : (∂[(0 : Fin 2)] affineQuadraticSolution) p = -1 := by
    cas
  have hx : (∂[(1 : Fin 2)] affineQuadraticSolution) p = 1 := by
    cas
  rw [ht, hx]
  norm_num

/--
The affine classical solution is a viscosity solution for the Hamiltonian `H(p) = p²`.
-/
theorem affineQuadraticSolution_isDifferentiableTestSolution :
    HamiltonJacobi1D.IsDifferentiableTestSolution (fun p : ℝ ↦ p ^ 2) Set.univ
      affineQuadraticSolution := by
  apply HamiltonJacobi1D.IsAmbientDifferentiableTestSolution.toSpatial isOpen_univ
  exact HamiltonJacobi1D.isAmbientDifferentiableTestSolution_of_classical (H := fun p : ℝ ↦ p ^ 2)
      (U := Set.univ) (u := affineQuadraticSolution)
      (by
        intro p _
        cas)
      (by
        exact fun p _ ↦ affineQuadraticSolution_residual_zero p)

private theorem norm_sq_eq_coord_sq_1 (v : ℝ^1) :
    ‖v‖ ^ 2 = (v 0) ^ 2 := by
  let S : ℝ := ∑ i : Fin 1, ‖v i‖ ^ 2
  have hnorm : ‖v‖ = Real.sqrt S := by
    simpa [S] using (EuclideanSpace.norm_eq (x := v))
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ sq_nonneg ‖v i‖
  calc
    ‖v‖ ^ 2 = (Real.sqrt S) ^ 2 := by rw [hnorm]
    _ = S := Real.sq_sqrt hS_nonneg
    _ = (v 0) ^ 2 := by
      simp [S, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]

/--
The affine solution satisfies the general one-dimensional Hamilton–Jacobi `PDEProblem`.

The proof identifies the squared norm of the one-dimensional spatial gradient with the
square of its only coordinate.
-/
theorem affineQuadraticSolution_satisfiesPDEProblem :
    SatisfiesPDEProblem (NonlinearFirstOrder.hamiltonJacobiEquation (n := 1)
      (H := NonlinearFirstOrder.squaredNormHamiltonian 1)
      (U := Set.univ)) affineQuadraticSolution := by
  unfold SatisfiesPDEProblem
  intro eqn heqn xt hxt
  rw [List.mem_append] at heqn
  cases heqn with
  | inl h_eqn =>
      have h_eqn' : eqn =
            { Output := ℝ
              operator := fun u xt ↦ (∂[0] u) xt + NonlinearFirstOrder.squaredNormHamiltonian 1
                    (spatialGradient (n := 1) u xt) (xt 0) (spatialPartCLM 1 xt)
              rhs := fun _ ↦ 0
              domain := Set.univ } := by
        simpa [NonlinearFirstOrder.hamiltonJacobiEquation] using h_eqn
      rw [h_eqn']
      let u : ℝ^2 → ℝ := affineQuadraticSolution
      have hgrad : (spatialGradient (n := 1) u xt) (0 : Fin 1) = (∂[(1 : Fin 2)] u) xt :=
        PDE.spatialGradient_apply u xt (0 : Fin 1)
      have hnorm : ‖spatialGradient (n := 1) u xt‖ ^ 2 =
            ((∂[(1 : Fin 2)] u) xt) ^ 2 := by
        simpa [hgrad] using norm_sq_eq_coord_sq_1 (spatialGradient (n := 1) u xt)
      have hresU : (∂[(0 : Fin 2)] u) xt + ((∂[(1 : Fin 2)] u) xt) ^ 2 = 0 :=
        affineQuadraticSolution_residual_zero xt
      change (∂[0] u) xt + NonlinearFirstOrder.squaredNormHamiltonian 1
              (spatialGradient (n := 1) u xt) (xt 0) (spatialPartCLM 1 xt) = 0
      simpa [NonlinearFirstOrder.squaredNormHamiltonian, hnorm, partialDeriv] using hresU
  | inr h_init =>
      simp [NonlinearFirstOrder.hamiltonJacobiEquation] at h_init

end

end HamiltonJacobi1D
