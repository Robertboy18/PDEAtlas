/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime

/-!
# Pointwise classical nonlinear heat solutions

Nonnegative classical solutions of the superlinear heat equation

`uₜ = Δu + uᵖ`

on an open time domain. This is the equation of the initial-value problem (6) of Evans, §9.4.1,
without the initial condition. The time domain matters in singularity arguments: a solution
defined for `t < T` should say nothing about regularity at the candidate singular time.

The solution predicate is designed for pointwise substitution. It requires the superlinear
exponent condition `1 < p`, joint `C¹` regularity of `(x, t) ↦ u x t` on `ℝ^n × I`, and global
`C²` regularity of the spatial slice `x ↦ u x t` for every `t ∈ I`. These fields do not assert
joint continuity in time of the second spatial derivatives, so they do not amount to
anisotropic `C^{2,1}` regularity.

The structure `IsNonnegativePointwiseClassicalSolutionOn` is stable under restriction to a
smaller open time domain (`mono`) and under pointwise equality (`congr`). Residuals are plain
functions, and reduced profile equations are predicates in the modules that define them.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, (6), p. 549.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime.NonlinearHeat

variable {n : ℕ} (p : ℝ)

/-- The nonlinear heat equation residual, oriented as
`Δu + uᵖ - uₜ`.

This orientation makes a similarity reduction read directly as an elliptic profile residual.
The function is total; regularity and domain assumptions enter the theorems that identify it
with the classical equation. -/
noncomputable def equationResidual
    (u : ℝ^n → ℝ → ℝ) (x : ℝ^n) (t : ℝ) : ℝ :=
  laplacian (fun y ↦ u y t) x + (u x t) ^ p -
    deriv (fun s ↦ u x s) t

/-- Vanishing of the residual is exactly the pointwise nonlinear heat equation. -/
theorem equation_residual_eq_zero_iff
    (u : ℝ^n → ℝ → ℝ) (x : ℝ^n) (t : ℝ) :
    equationResidual p u x t = 0 ↔
      deriv (fun s ↦ u x s) t =
        laplacian (fun y ↦ u y t) x + (u x t) ^ p := by
  simp only [equationResidual, sub_eq_zero]
  exact eq_comm

/-- A nonnegative pointwise classical solution of `uₜ = Δu + uᵖ` on an open time domain `I`,
in the superlinear regime `p > 1`.

The exponent condition excludes negative exponents, where Mathlib's convention `0 ^ p = 0` would
let a zero value satisfy the equation spuriously. Spatial slices are defined on all of
`ℝ^n`; only time is restricted. The regularity fields say
that the spacetime function is jointly `C¹` and that every admitted spatial slice is globally
`C²`. They do not require the spatial Hessian to depend continuously on time and therefore do
not claim joint `C^{2,1}` regularity.

The Fujita blow-up theorems use `HeatEquation.Nonlinear.IsClassicalWholeSpacePowerSolution`
instead: a closed cylinder `[0, T] × ℝⁿ` with initial data and continuity up to `t = 0`. -/
structure IsNonnegativePointwiseClassicalSolutionOn
    (I : Set ℝ) (u : ℝ^n → ℝ → ℝ) : Prop where
  /-- The singularity theory in this namespace concerns the superlinear regime. -/
  exponent_superlinear : 1 < p
  /-- The time domain is open, so ordinary derivatives apply at each admitted time. -/
  time_domain_open : IsOpen I
  /-- Joint spacetime `C¹` regularity on `ℝ^n × I`. -/
  spacetime_contDiffOn :
    ContDiffOn ℝ 1 (fun xt : ℝ^n × ℝ ↦ u xt.1 xt.2) (Set.univ ×ˢ I)
  /-- Spatial `C²` regularity of every admitted time slice. -/
  spatial_slice_contDiff :
    ∀ (t : ℝ), t ∈ I → ContDiff ℝ 2 (fun x ↦ u x t)
  /-- Nonnegativity on the spacetime domain. -/
  nonnegative :
    ∀ (x : ℝ^n) (t : ℝ), t ∈ I → 0 ≤ u x t
  /-- The pointwise nonlinear heat equation on the spacetime domain. -/
  equation :
    ∀ (x : ℝ^n) (t : ℝ), t ∈ I →
      deriv (fun s ↦ u x s) t =
        laplacian (fun y ↦ u y t) x + (u x t) ^ p

/-- Restrict a pointwise classical solution to an open subset of its time domain.

All analytic and equation properties are inherited pointwise; openness of the smaller domain is
supplied separately because it does not follow from set inclusion. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.mono
    {I J : Set ℝ} {u : ℝ^n → ℝ → ℝ}
    (hu : IsNonnegativePointwiseClassicalSolutionOn (n := n) p I u)
    (hJ : IsOpen J) (hJI : J ⊆ I) :
    IsNonnegativePointwiseClassicalSolutionOn (n := n) p J u where
  exponent_superlinear := hu.exponent_superlinear
  time_domain_open := hJ
  spacetime_contDiffOn := hu.spacetime_contDiffOn.mono fun _ hxt ↦
    ⟨hxt.1, hJI hxt.2⟩
  spatial_slice_contDiff := fun t ht ↦
    hu.spatial_slice_contDiff t (hJI ht)
  nonnegative := fun x t ht ↦
    hu.nonnegative x t (hJI ht)
  equation := fun x t ht ↦
    hu.equation x t (hJI ht)

/-- Time differentiability is derived from joint `C¹` regularity and openness of the time
domain; it is not stored as an additional solution law. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.time_differentiable
    {I : Set ℝ} {u : ℝ^n → ℝ → ℝ}
    (hu : IsNonnegativePointwiseClassicalSolutionOn (n := n) p I u)
    (x : ℝ^n) {t : ℝ} (ht : t ∈ I) :
    DifferentiableAt ℝ (fun s ↦ u x s) t := by
  simpa using
    differentiableAt_time_slice_of_contDiffOn
      hu.time_domain_open
      (fun xt : ℝ^n × ℝ ↦ u xt.1 xt.2)
      hu.spacetime_contDiffOn x ht

/-- The residual of a pointwise classical solution vanishes on its spacetime domain. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.equation_residual_eq_zero
    {I : Set ℝ} {u : ℝ^n → ℝ → ℝ}
    (hu : IsNonnegativePointwiseClassicalSolutionOn (n := n) p I u)
    (x : ℝ^n) (t : ℝ) (ht : t ∈ I) :
    equationResidual p u x t = 0 :=
  (equation_residual_eq_zero_iff p u x t).2 (hu.equation x t ht)

/-- A pointwise classical solution is unchanged by equality on its open time domain.

The time derivative only needs equality near the evaluation time. Openness upgrades equality
on `I` to that local equality, while each admitted spatial slice is equal on all of `ℝ^n`. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.congr
    {I : Set ℝ} {u v : ℝ^n → ℝ → ℝ}
    (hu : IsNonnegativePointwiseClassicalSolutionOn (n := n) p I u)
    (huv : ∀ (x : ℝ^n) (t : ℝ), t ∈ I → u x t = v x t) :
    IsNonnegativePointwiseClassicalSolutionOn (n := n) p I v where
  exponent_superlinear := hu.exponent_superlinear
  time_domain_open := hu.time_domain_open
  spacetime_contDiffOn := by
    apply hu.spacetime_contDiffOn.congr
    intro xt hxt
    exact (huv xt.1 xt.2 hxt.2).symm
  spatial_slice_contDiff := by
    intro t ht
    have hslice : (fun x ↦ v x t) = fun x ↦ u x t :=
      funext fun x ↦ (huv x t ht).symm
    rw [hslice]
    exact hu.spatial_slice_contDiff t ht
  nonnegative := by
    intro x t ht
    rw [← huv x t ht]
    exact hu.nonnegative x t ht
  equation := by
    intro x t ht
    have htime : (fun s ↦ v x s) =ᶠ[nhds t] fun s ↦ u x s := by
      filter_upwards [hu.time_domain_open.mem_nhds ht] with s hs
      exact (huv x s hs).symm
    have hslice : (fun y ↦ v y t) = fun y ↦ u y t :=
      funext fun y ↦ (huv y t ht).symm
    rw [htime.deriv_eq, hslice, ← huv x t ht]
    exact hu.equation x t ht

/-- The zero field is a nonnegative pointwise classical solution on every open time domain in the
superlinear regime `p > 1`.

So the solution predicate is inhabited; the zero field does not blow up. -/
theorem zero_is_nonnegative_pointwise_classical_solution_on
    (I : Set ℝ) (hI : IsOpen I) (hp : 1 < p) :
    IsNonnegativePointwiseClassicalSolutionOn (n := n) p I
      (fun _ : ℝ^n ↦ fun _ : ℝ ↦ (0 : ℝ)) where
  exponent_superlinear := hp
  time_domain_open := hI
  spacetime_contDiffOn := by
    fun_prop
  spatial_slice_contDiff := by
    intro t ht
    fun_prop
  nonnegative := by
    intro x t ht
    rfl
  equation := by
    intro x t ht
    have hp0 : (0 : ℝ) ^ p = 0 :=
      Real.zero_rpow (lt_trans zero_lt_one hp).ne'
    simp [PDE.laplacian_const (n := n) 0 x, hp0]

end PDE.Solution.Singularity.FiniteTime.NonlinearHeat
