/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.GradientFlow.Solution.Basic
public import PDE.CalculusOfVariations.GradientEnergy.L2.WeakEquation

/-!
# Weak solutions of gradient diffusion

The equation is `uₜ = div DL(∇u)` with zero Dirichlet data. `IsWeakSolution L u g` keeps the
trajectory `u` in `L²`, continuous up to the initial time, with a velocity `g` that is bounded in
`L²` and is the distributional time derivative of `u`, and tests the spatial equation against `H¹₀`
at almost every time. A distributional velocity, rather than an almost-everywhere classical
derivative, rules out singular continuous trajectories.

For a uniformly convex `C²` density with bounded Hessian on a bounded open set,
`isWeakSolution_iff_isSubgradientFlow` identifies these weak solutions with the subgradient flows of
the Dirichlet integral. Evans recasts the initial/boundary-value problem (33) of §9.6.3 as the
abstract gradient flow (34) by his Theorem 4; the equivalence is this step for weak solutions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.3, (27)-(29) and Theorem 4 (Characterization of ∂I),
  pp. 571-572, and (33)-(34), pp. 572-573.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Quasilinear.GradientFlow

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Convex PDE.Analysis.Evolution PDE.CalculusOfVariations
open scoped ENNReal Gradient NNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}

local notation "μ" => domainMeasure n Ω

/-- A weak Dirichlet solution with continuous `L²` initial trace and an
essentially bounded `L²` velocity on the positive half-line. The spatial
Sobolev representative carries both the boundary condition and the flux. -/
structure IsWeakSolution (L : ℝ^n → ℝ) (u g : ℝ → (ℝ^n →₂[μ] ℝ)) : Prop where
  /-- Continuity includes the initial time. -/
  continuousOn : ContinuousOn u (Ici 0)
  /-- The time derivative is uniformly bounded in the ambient `L²` norm. -/
  velocity_memLp : MemLp g ∞ (volume.restrict (Ioi 0))
  /-- Time differentiation is understood distributionally. -/
  weakDerivative : HasWeakTimeDerivativeOn (Ioi 0) u g
  /-- The weak PDE holds with zero spatial boundary values at almost every time. -/
  equation : ∀ᵐ t ∂volume.restrict (Ioi 0), ∃ w : H¹₀(Ω),
    baseCoordCLM w = u t ∧ ∀ v : H¹₀(Ω),
      ⟪g t, baseCoordCLM v⟫ +
        (∫ x, ⟪∇ L (∇ (w : H¹(Ω)) x), ∇ (v : H¹(Ω)) x⟫ ∂μ) = 0

/-- Uniform convexity identifies weak gradient diffusion with the ambient
Dirichlet-energy flow. Neither direction assumes the desired evolution exists. -/
theorem isWeakSolution_iff_isSubgradientFlow
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (u g : ℝ → (ℝ^n →₂[μ] ℝ)) :
    IsWeakSolution L u g ↔ IsSubgradientFlow (l2DirichletGradientEnergy L) u g := by
  constructor
  · intro h
    refine ⟨h.continuousOn, h.velocity_memLp, h.weakDerivative, ?_⟩
    filter_upwards [h.equation] with t ht
    obtain ⟨w, hw, hweak⟩ := ht
    rw [← hw]
    apply (mem_subdifferential_l2DirichletGradientEnergy_iff_integral
      hΩ hbounded hL hθ hlower hupper w (-g t)).mpr
    intro v
    rw [inner_neg_left]
    linarith [hweak v]
  · intro h
    refine ⟨h.continuousOn, h.velocity_memLp, h.weakDerivative, ?_⟩
    filter_upwards [h.inclusion] with t ht
    have hfinite := ne_top_of_mem_subdifferential
      (isProper_l2DirichletGradientEnergy L) ht
    obtain ⟨w, hw⟩ := (l2DirichletGradientEnergy_ne_top_iff hΩ L (u t)).mp hfinite
    have hweak := (mem_subdifferential_l2DirichletGradientEnergy_iff_integral
      hΩ hbounded hL hθ hlower hupper w (-g t)).mp (by simpa only [hw] using ht)
    refine ⟨w, hw, fun v ↦ ?_⟩
    have hv := hweak v
    rw [inner_neg_left] at hv
    linarith

end PDE.Parabolic.Quasilinear.GradientFlow
