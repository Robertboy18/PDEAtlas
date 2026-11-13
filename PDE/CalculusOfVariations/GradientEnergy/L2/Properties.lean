/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.GradientEnergy.L2.Definition
public import PDE.Analysis.Convex.Extended.LinearImage.LowerSemicontinuity
public import PDE.Analysis.Calculus.Gradient.QuadraticGrowth

/-!
# Convexity and L² lower semicontinuity of the signed gradient energy

Quadratic growth makes the Dirichlet integral finite on `H¹₀`. Its weak
lower semicontinuity and bounded sublevels, obtained from Poincaré,
give lower semicontinuity after extension to `L²`. The argument applies
on every bounded open set of positive dimension; boundary smoothness
is needed only for the exact `H²` domain of the subdifferential.
Together with `isProper_l2DirichletGradientEnergy` this is Evans,
§9.6.3, Theorem 4 (i).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.3, Theorem 4 (i).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace Analysis.Convex
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}
  {a b c C : ℝ}

local notation "μ" => domainMeasure n Ω

/-- Convexity of the signed ambient energy follows from convexity of its
integrable density. Infinite-energy competitors are handled by extension. -/
theorem convex_realEpigraph_l2DirichletGradientEnergy
    (hΩ : IsOpen Ω) (hL : ConvexOn ℝ univ L)
    (hint : ∀ u : H¹₀(Ω), Integrable (fun x ↦ L (∇ (u : H¹(Ω)) x)) μ) :
    Convex ℝ (realEpigraph (l2DirichletGradientEnergy (Ω := Ω) L)) := by
  apply convex_realEpigraph_linearImageEnergy _ (baseCoordCLM_injective hΩ)
  exact convexOn_integral_Lp_comp (gradientCLM (n := n) (Ω := Ω)).toLinearMap
    (Filter.Eventually.of_forall fun _ ↦ hL) hint

/-- Positive quadratic growth and convexity give lower semicontinuity in
the ambient `L²` topology, including at points outside `H¹₀`. -/
theorem lowerSemicontinuous_l2DirichletGradientEnergy
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hcont : Continuous L) (hconvex : ConvexOn ℝ univ L)
    (hc : 0 < c) (hC : 0 ≤ C)
    (hlower : ∀ z, c * ‖z‖ ^ 2 - b ≤ L z)
    (hupper : ∀ z, L z ≤ a + C * ‖z‖ ^ 2) :
    LowerSemicontinuous (l2DirichletGradientEnergy (Ω := Ω) L) := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  have hmeas : Measurable (Function.uncurry (fun _ : ℝ^n ↦ L)) :=
    hcont.measurable.comp measurable_snd
  have hlo : ∀ᵐ x ∂μ, ∀ z, c * ‖z‖ ^ 2 - b ≤ L z :=
    Filter.Eventually.of_forall fun _ ↦ hlower
  have hup : ∀ᵐ x ∂μ, ∀ z, L z ≤ a + C * ‖z‖ ^ 2 :=
    Filter.Eventually.of_forall fun _ ↦ hupper
  have hint (u : H¹₀(Ω)) : Integrable (fun x ↦ L (∇ (u : H¹(Ω)) x)) μ :=
    integrable_dirichletGradientIntegralEnergy_density
      (F := fun _ ↦ L) (a := fun _ ↦ a) (b := fun _ ↦ b) (c := c) (C := C) hmeas
      (integrable_const a) (integrable_const b) hc.le hC hlo hup u
  change LowerSemicontinuous (linearImageEnergy (baseCoordCLM (n := n) (Ω := Ω))
    (dirichletGradientIntegralEnergy (fun _ ↦ L)))
  apply lowerSemicontinuous_linearImageEnergy
    (baseCoordCLM (n := n) (Ω := Ω)) (baseCoordCLM_injective hΩ)
    (dirichletGradientIntegralEnergy (fun _ ↦ L))
  · exact lowerSemicontinuous_weakSpace_dirichletGradientIntegralEnergy
      (F := fun _ ↦ L) (a := fun _ ↦ a) (b := fun _ ↦ b) (c := c) (C := C) hmeas
      (Filter.Eventually.of_forall fun _ ↦ hconvex)
      (integrable_const a) (integrable_const b) hc.le hC hlo hup
  · intro r
    have hcoercive := tendsto_dirichletGradientIntegralEnergy_atTop
      (F := fun _ ↦ L) (b := fun _ ↦ b) (c := c)
      hn hbounded hc (integrable_const b) hint hlo
    change ∀ᶠ u in Bornology.cobounded H¹₀(Ω),
      ¬dirichletGradientIntegralEnergy (fun _ ↦ L) u ≤ r
    exact (hcoercive.eventually (eventually_gt_atTop r)).mono fun _ hu ↦ not_le.mpr hu

/-- Hessian bounds imply integrability of every Dirichlet
gradient density, with arbitrary value and derivative at zero. -/
theorem integrable_gradientDensity_of_hessian_bounds
    (hbounded : Bornology.IsBounded Ω) (hL : ContDiff ℝ 2 L)
    {θ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C) (u : H¹₀(Ω)) :
    Integrable (fun x ↦ L (∇ (u : H¹(Ω)) x)) μ := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  exact integrable_dirichletGradientIntegralEnergy_density
    (F := fun _ ↦ L)
    (hL.continuous.measurable.comp measurable_snd)
    (integrable_const (|L 0| + ‖fderiv ℝ L 0‖ ^ 2))
    (integrable_const (|L 0| + ‖fderiv ℝ L 0‖ ^ 2 / θ))
    (by positivity : 0 ≤ θ / 4) (by positivity : 0 ≤ C + 1)
    (Filter.Eventually.of_forall fun _ ↦
      Analysis.quadratic_lower_bound_of_hessian_bound hL hθ hlower)
    (Filter.Eventually.of_forall fun _ ↦
      Analysis.quadratic_upper_bound_of_hessian_bound hL hC hupper) u

/-- Uniform convexity and a bounded Hessian yield the ambient
lower semicontinuity required by Hilbert-space subgradient theory. -/
theorem lowerSemicontinuous_l2DirichletGradientEnergy_of_hessian_bounds
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) (hC : 0 ≤ C)
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C) :
    LowerSemicontinuous (l2DirichletGradientEnergy (Ω := Ω) L) :=
  lowerSemicontinuous_l2DirichletGradientEnergy hn hΩ hbounded hL.continuous
    ((Analysis.strongConvexOn_of_hessian_bound hL hlower).strictConvexOn hθ).convexOn
    (by positivity : 0 < θ / 4) (by positivity : 0 ≤ C + 1)
    (Analysis.quadratic_lower_bound_of_hessian_bound hL hθ hlower)
    (Analysis.quadratic_upper_bound_of_hessian_bound hL hC hupper)

end PDE.CalculusOfVariations
