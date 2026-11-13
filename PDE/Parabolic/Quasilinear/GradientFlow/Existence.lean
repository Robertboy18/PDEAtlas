/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Existence.Domain
public import PDE.CalculusOfVariations.GradientEnergy.L2.Domain
public import PDE.Parabolic.Quasilinear.GradientFlow.Solution

/-!
# Global existence for nonlinear gradient diffusion

Let `L` be a `C²` density with `θ |v|² ≤ D²L(x)(v, v)` and `‖D²L(x)‖ ≤ C`, and let `Ω` be a bounded
open set with `C²` graph boundary. Every initial value in `H² ∩ H¹₀` has a global weak solution of
`uₜ = div DL(∇u)` with zero Dirichlet data and bounded `L²` velocity, and every time slice,
including the initial one, lies in `H² ∩ H¹₀` (`exists_weakSolution`).

This is the existence statement of Evans's §9.6.3 for the problem (33), with `L` of class `C²` and a
`C²` boundary in place of smooth ones. Evans also states uniqueness, which follows from the
contraction estimate of `PDE.Parabolic.Quasilinear.GradientFlow.Uniqueness`.

## How it works

As in Evans, we write the problem as the gradient flow `u' ∈ -∂I[u]` of the Dirichlet integral
`I[u] = ∫ L(∇u)`, his (27) and (34). The energy is proper, convex and lower semicontinuous on `L²`
(`isProper_l2DirichletGradientEnergy`, `convex_realEpigraph_l2DirichletGradientEnergy`,
`lowerSemicontinuous_l2DirichletGradientEnergy_of_hessian_bounds`), and the domain of its
subdifferential is `H² ∩ H¹₀` (`subdifferentialDomain_l2DirichletGradientEnergy`), as in Evans's
§9.6.3, Theorem 4. The abstract theorem `exists_unique_subgradientFlow`, Evans's §9.6.2, Theorem 3,
gives the flow, and `isWeakSolution_iff_isSubgradientFlow` turns it into a weak solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.2, Theorem 3 (Solution of gradient flow), (15)-(16),
  p. 566; §9.6.3, (27)-(29) and Theorem 4 (Characterization of ∂I), pp. 571-572, and (33)-(34),
  pp. 572-573.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Quasilinear.GradientFlow

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Convex PDE.Analysis.Evolution PDE.CalculusOfVariations
open scoped ENNReal NNReal Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}

local notation "μ" => domainMeasure n Ω

/-- The nonlinear Dirichlet problem has a global solution from every `H² ∩ H¹₀`
initial value. The weak solution carries the initial trace, distributional
time derivative and spatial equation; the additional conclusion gives `H²`
regularity at every time, including zero. -/
theorem exists_weakSolution
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (u₀ : W^{2,2}(Ω))
    (hboundary : lowerOrderCLM (by omega : 1 ≤ 2) u₀ ∈
      (h10SubmoduleOn (n := n) (Ω := Ω))) :
    ∃ u g : ℝ → (ℝ^n →₂[μ] ℝ),
      u 0 = wkpBaseCoordinateCLM u₀ ∧ IsWeakSolution L u g ∧
        ∀ t, 0 ≤ t → u t ∈ l2H2DirichletDomain n Ω := by
  have hproper := isProper_l2DirichletGradientEnergy (Ω := Ω) L
  have hconvex := convex_realEpigraph_l2DirichletGradientEnergy hΩ
    ((PDE.Analysis.strongConvexOn_of_hessian_bound hL hlower).strictConvexOn hθ).convexOn
    (integrable_gradientDensity_of_hessian_bounds
      hbounded hL hθ C.coe_nonneg hlower hupper)
  have hlsc := lowerSemicontinuous_l2DirichletGradientEnergy_of_hessian_bounds
    (Fact.out : 0 < n) hΩ hbounded hL hθ C.coe_nonneg hlower hupper
  have hdomain := subdifferentialDomain_l2DirichletGradientEnergy
    hΩ hbounded hgraph hL hθ hlower hupper
  have hinit : wkpBaseCoordinateCLM u₀ ∈
      subdifferentialDomain (l2DirichletGradientEnergy (Ω := Ω) L) := by
    rw [hdomain]
    exact ⟨u₀, hboundary, rfl⟩
  obtain ⟨_, _, _, u, g, hu0, hu, _, _, _, _, hregularity, _⟩ :=
    exists_unique_subgradientFlow hproper hconvex hlsc hinit
  refine ⟨u, g, hu0, (isWeakSolution_iff_isSubgradientFlow
    hΩ hbounded hL hθ hlower hupper u g).mpr hu, ?_⟩
  intro t ht
  rw [← hdomain]
  exact hregularity t ht

end PDE.Parabolic.Quasilinear.GradientFlow
