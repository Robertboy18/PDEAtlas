/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.InitialValueProblem

public import PDE.Parabolic.Heat.InitialValue
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import PDE.Parabolic.Heat.ApproximateIdentity
import PDE.Parabolic.Heat.ConvolutionSpace.Equation
import PDE.Parabolic.Heat.ConvolutionSpace.JointDifferentiability
import PDE.Parabolic.Heat.ConvolutionSpace.SpatialDerivatives
import PDE.Parabolic.Heat.ConvolutionTime

/-!
# Pointwise heat initial-value solutions

For bounded continuous data, the heat-kernel solution `initialValueSolution g` solves the heat
equation at positive time, attains `g` continuously as `t ↓ 0`, and has the pointwise
differentiability recorded in `IsPointwiseInitialValueSolution`. It also satisfies the `PDEProblem`
form `heatResidualAssignedInitialValueProblem g`.

This is Evans's §2.3.1(b), Theorem 1, with parts (ii) and (iii); in place of the smoothness of part
(i), the structure records the first and second derivatives that the equation uses.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(b), (8)-(9) and Theorem 1 (Solution of initial-value
  problem), p. 47.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian SatisfiesPDEProblem)

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

/-- A pointwise solution of the forced heat Cauchy problem on positive time.

Unlike the residual-and-assigned-value `PDEProblem` interface, this structure
records enough regularity for every derivative in the equation to have its
analytic meaning. It also distinguishes the assigned value at `t = 0` from
the limit `u(x, t) → g(x₀)` as `(x, t) → (x₀, 0)` with `t > 0`. -/
structure IsPointwiseInitialValueSolution
    (f : ℝ^n → ℝ → ℝ) (g : ℝ^n → ℝ) (u : ℝ^n → ℝ → ℝ) : Prop where
  /-- At every positive time, the solution is differentiable in the time variable. -/
  differentiableAt_time : ∀ x t, 0 < t → DifferentiableAt ℝ (u x) t
  /-- At every positive time, the spatial slice of the solution is differentiable. -/
  differentiableAt_space : ∀ x t, 0 < t → DifferentiableAt ℝ (fun y ↦ u y t) x
  /-- Each first spatial partial is spatially differentiable at positive time. -/
  differentiableAt_spatialPartial : ∀ x t, 0 < t → ∀ i : Fin n,
    DifferentiableAt ℝ (fun y ↦ (∂[i] (fun z ↦ u z t)) y) x
  /-- The pointwise forced heat-equation residual vanishes at positive time. -/
  residual_eq : ∀ x t, 0 < t →
    HeatEquation.heatParabolicOperator u x t = f x t
  /-- The explicitly assigned value at time zero is the initial datum. -/
  initial_value : ∀ x, u x 0 = g x
  /-- The spacetime solution extends continuously to each point `(x₀, 0)` of the initial
  boundary, with boundary value `g x₀`. -/
  continuousAt_initialBoundary : ∀ x₀ ε, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x t, ‖x - x₀‖ < δ → 0 < t → t < δ →
      |u x t - g x₀| < ε

/-- The heat-kernel formula satisfies `heatResidualAssignedInitialValueProblem g` as soon as its
positive-time residual vanishes. The time-zero value comes from
`initialValueSolution_timeZero_value`. -/
theorem initialValueSolution_satisfiesPDEProblem_of_positive_residual
    (g : ℝ^n → ℝ)
    (hres : ∀ xt : ℝ^(n + 1), xt 0 > 0 →
      heatOperator (n := n)
        (fun zt : ℝ^(n + 1) ↦
          initialValueSolution (n := n) g (spatialPartCLM n zt) (zt 0)) xt = 0) :
    SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g)
      (fun xt : ℝ^(n + 1) ↦
        initialValueSolution (n := n) g (spatialPartCLM n xt) (xt 0)) :=
  heatResidualAssignedInitialValueProblem.of_residual_initial (n := n)
    (u := fun xt : ℝ^(n + 1) ↦
      initialValueSolution (n := n) g (spatialPartCLM n xt) (xt 0))
    hres
    (fun xt ht ↦ initialValueSolution_timeZero_value (n := n) g xt ht)

/-- For bounded continuous initial data, the heat-kernel formula satisfies
`heatResidualAssignedInitialValueProblem g`. Joint differentiability at positive time
identifies the spacetime derivative `∂[0]` with the one-variable time derivative in
`initialValueSolution_positive_time_residual_zero`. -/
theorem initialValueSolution_satisfiesPDEProblem
    (g : ℝ^n → ℝ)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ x, |g x| ≤ M) :
    SatisfiesPDEProblem (heatResidualAssignedInitialValueProblem (n := n) g)
      (fun xt : ℝ^(n + 1) ↦
        initialValueSolution (n := n) g (spatialPartCLM n xt) (xt 0)) := by
  refine initialValueSolution_satisfiesPDEProblem_of_positive_residual
    (n := n) g ?_
  intro xt hxt
  let U : ℝ^(n + 1) → ℝ := fun zt ↦
    initialValueSolution (n := n) g (spatialPartCLM n zt) (zt 0)
  let t : ℝ := xt 0
  let x : ℝ^n := spatialPartCLM n xt
  have hp : timeSpaceCons (n := n) t x = xt := by
    simp [t, x]
  have hu : DifferentiableAt ℝ U (timeSpaceCons (n := n) t x) := by
    rw [hp]
    exact
      (differentiableAt_initialValueSolution_timeSpace
        (n := n) g (spatialPartCLM n xt) (xt 0) hxt hg_cont hg_bdd).comp xt
        ((EuclideanSpace.proj (0 : Fin (n + 1))).differentiableAt.prodMk
          (spatialPartCLM n).differentiableAt)
  have htime :=
    PDE.partialDeriv_timeSpaceCons_eq_deriv (n := n) U x t hu
  have hspatialCons (s : ℝ) (y : ℝ^n) :
      spatialPartCLM n (timeSpaceCons (n := n) s y) = y := by
    exact spatialPartCLM_timeSpaceCons s y
  have hspatial : spatialPartCLM n (timeSpaceCons (n := n) t x) = x := by
    exact spatialPartCLM_timeSpaceCons t x
  have hslice :
      (fun y : ℝ^n ↦
        U (timeSpaceCons (n := n) t y)) =
        fun y ↦ initialValueSolution (n := n) g y t := by
    funext y
    simp only [U, timeSpaceCons_zero, hspatialCons]
  have hcurve :
      (fun s ↦ U (timeSpaceCons (n := n) s x)) =
        fun s ↦ initialValueSolution (n := n) g x s := by
    funext s
    simp only [U, timeSpaceCons_zero, hspatialCons]
  change (∂[0] U) xt -
    laplacian
      (fun y : ℝ^n ↦
        U (timeSpaceCons (n := n) (xt 0) y))
      (spatialPartCLM n xt) = 0
  rw [← hp, htime]
  simp only [timeSpaceCons_zero]
  rw [hcurve, hslice, hspatial]
  exact initialValueSolution_positive_time_residual_zero
    (n := n) g x t hxt hg_cont hg_bdd

/-- Constant initial data give the constant solution: the heat-kernel formula for `g = c`
satisfies `heatResidualAssignedInitialValueProblem`. This follows from the unit mass of the
kernel, `initialValueSolution_const`. -/
theorem initialValueSolution_const_satisfiesPDEProblem (c : ℝ) :
    SatisfiesPDEProblem
      (heatResidualAssignedInitialValueProblem (n := n)
        (fun _ : ℝ^n ↦ c))
      (fun xt : ℝ^(n + 1) ↦
        initialValueSolution (n := n) (fun _ : ℝ^n ↦ c)
          (spatialPartCLM n xt) (xt 0)) := by
  refine heatResidualAssignedInitialValueProblem.of_residual_initial (n := n) ?hres ?hinit
  · intro xt _ht
    simp [heatOperator, initialValueSolution_const, PDE.partialDeriv_const,
      PDE.laplacian_const]
  · intro xt ht
    simp [initialValueSolution_const, ht]

/-- For bounded continuous initial data, the heat-kernel convolution is a pointwise solution
whose assigned initial value is the continuous spacetime boundary value. -/
theorem initialValueSolution_isPointwiseHomogeneousInitialValueSolution
    (g : ℝ^n → ℝ)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ x, |g x| ≤ M) :
    IsPointwiseInitialValueSolution (fun _ _ ↦ 0) g
      (initialValueSolution (n := n) g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x t ht
    exact
      (hasDerivAt_initialValueSolution_time
        (n := n) g x t ht hg_cont hg_bdd).differentiableAt
  · intro x t ht
    exact differentiableAt_initialValueSolution_space
      (n := n) g x t ht hg_cont hg_bdd
  · intro x t ht i
    exact differentiableAt_partialDeriv_initialValueSolution_space
      (n := n) g x t i ht hg_cont hg_bdd
  · intro x t ht
    exact initialValueSolution_positive_time_residual_zero
      (n := n) g x t ht hg_cont hg_bdd
  · exact initialValueSolution_of_t_eq_zero (n := n) g
  · intro x₀ ε hε
    obtain ⟨δ, hδ, htrace⟩ :=
      initialValueSolution_locally_uniform_initial_trace
        (n := n) g x₀ hg_cont hg_bdd ε hε
    exact ⟨δ, hδ, fun x t hx ht htδ ↦ htrace x t hx ⟨ht, htδ⟩⟩

end HeatEquation
