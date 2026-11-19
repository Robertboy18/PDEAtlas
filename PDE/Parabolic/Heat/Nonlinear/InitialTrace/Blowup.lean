/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Eigenfunction.DirichletProbability.Smooth
public import PDE.Parabolic.Heat.Nonlinear.InitialTrace.Moment

/-!
# Quadratic heat blowup above the initial first-eigenfunction threshold

Let `Ω` be a bounded open set with `C¹` graph boundary, and let `w > 0` be a Dirichlet eigenfunction
of `-Δ` in `Ω` with eigenvalue `λ > 0`, normalized by `∫ w = 1`, that is `C²` in `Ω`, `C¹` up to the
boundary and zero on the boundary. If `g ≥ 0` and `∫ w g > λ`, there is no solution of
`uₜ - Δu = u²` for all positive times that is `C²` in the open cylinder, continuous on the initial
face in `Ω` and up to the lateral boundary at positive times, zero on the lateral boundary and equal
to `g` at time zero (`not_global_square_solution_of_separate_traces`). The solution is not assumed
nonnegative, and no bound or joint limit is imposed at the initial/lateral corner. On a connected
domain with smooth graph boundary, `not_global_square_solution_of_initial_first_moment` takes for
`w` the first Dirichlet eigenfunction (`FirstDirichletEigenfunctionWeight`).

This is Evans's §9.4.1, Theorem 1, for nonnegative data and solutions with separate initial and
lateral traces.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.1, Theorem 1 (Blow-up for large data) and its proof,
  (3)-(5), pp. 548-549.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open scoped Topology

namespace HeatEquation.Nonlinear

/-- For nonnegative data, the strict first-eigenfunction moment threshold excludes a global
quadratic heat solution with separate initial and lateral continuity that is not assumed
nonnegative. No bound, value or joint limit is imposed at the initial/lateral corner. -/
theorem not_global_square_solution_of_separate_traces
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {g w : ℝ^n → ℝ} {lambda : ℝ}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hgraph : SobolevSpace.Boundary.HasC1GraphBoundary Ω)
    (hw : ContDiffOn ℝ 2 w Ω)
    (hwup : SobolevSpace.ContDiffUpToBoundary 1 w Ω)
    (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 < w x)
    (hunit : ∫ x in Ω, w x = 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hlambda : 0 < lambda) (hg : ∀ x ∈ Ω, 0 ≤ g x)
    (hlarge : lambda < ∫ x in Ω, w x * g x) :
    ¬ ∃ u : ℝ → ℝ^n → ℝ,
      ContinuousOn u.uncurry (Ici 0 ×ˢ Ω) ∧
      ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω) ∧
      ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω) ∧
      (∀ t > 0, ∀ x ∈ Ω,
        deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2) ∧
      (∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0) ∧
      (∀ x ∈ Ω, u 0 x = g x) := by
  rintro ⟨u, hc0, hc, hs, heq, hboundary, hinit⟩
  have hmoment := integrable_initial_moment_and_le_eigenvalue_of_nonnegative_initial
    hΩ hne hb hgraph hw hwup hwc hwzero hwpos hunit heigen hlambda
    hc0 hc hs heq hboundary (fun x hx ↦ (hinit x hx).symm ▸ hg x hx)
  apply hlarge.not_ge
  convert hmoment.2 using 1
  apply setIntegral_congr_fun hΩ.measurableSet
  intro x hx
  exact congrArg (fun v : ℝ ↦ w x * v) (hinit x hx).symm

open SobolevSpace.GraphSpace
open scoped Sobolev

/-- For nonnegative data, the strict normalized first-eigenfunction threshold excludes a
global classical quadratic heat solution with separate initial and lateral traces.
The weak spectral weight supplies all required classical boundary regularity. -/
theorem not_global_square_solution_of_initial_first_moment
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {g : ℝ^n → ℝ}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hconn : IsPreconnected Ω)
    (hgraph : ∀ k : ℕ, SobolevSpace.Boundary.HasContDiffGraphBoundary k Ω)
    (w : FirstDirichletEigenfunctionWeight Ω)
    (hg : ∀ x ∈ Ω, 0 ≤ g x)
    (hlarge : w.eigenvalue < ∫ x in Ω, g x * baseCoordCLM w.vector x) :
    ¬ ∃ u : ℝ → ℝ^n → ℝ,
      ContinuousOn u.uncurry (Ici 0 ×ˢ Ω) ∧
      ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω) ∧
      ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω) ∧
      (∀ t > 0, ∀ x ∈ Ω,
        deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2) ∧
      (∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0) ∧
      (∀ x ∈ Ω, u 0 x = g x) := by
  obtain ⟨z, hz, hzup, hzae, hzero, hpos, hunit, heigen⟩ :=
    w.exists_smoothRepresentative hΩ hb hconn hgraph
  have hlarge' : w.eigenvalue < ∫ x in Ω, z x * g x := by
    convert hlarge using 1
    apply integral_congr_ae
    filter_upwards [hzae] with x hx
    simp only [hx, mul_comm]
  exact not_global_square_solution_of_separate_traces hΩ hne hb
    ((hgraph 1).hasC1GraphBoundary le_rfl) (hzup 2).contDiffOn (hzup 1)
    hz.continuousOn hzero hpos hunit heigen w.eigenvalue_pos hg hlarge'

end HeatEquation.Nonlinear
