/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.GradientEnergy.L2.FirstVariation
public import PDE.Spaces.Sobolev.Calculus.Composition.Flux.L2

/-!
# The integral equation for a gradient-energy subgradient

The ambient `L²` subgradient is the weak negative divergence of `DL(∇u)`.
The characterization is written as a spatial integral, so applications
can state the equation without choosing coordinate representatives of the flux.
The bounded Hessian makes that flux square integrable.
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace Analysis.Convex
open scoped ENNReal Gradient NNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}

local notation "μ" => domainMeasure n Ω

/-- The subgradient condition is precisely the weak divergence equation,
tested against every zero-boundary Sobolev function. -/
theorem mem_subdifferential_l2DirichletGradientEnergy_iff_integral
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (u : H¹₀(Ω)) (f : ℝ^n →₂[μ] ℝ) :
    f ∈ subdifferential (l2DirichletGradientEnergy L) (baseCoordCLM u) ↔
      ∀ v : H¹₀(Ω),
        (∫ x, ⟪∇ L (∇ (u : H¹(Ω)) x), ∇ (v : H¹(Ω)) x⟫ ∂μ) =
          ⟪f, baseCoordCLM v⟫ := by
  obtain ⟨q, hq, hpair⟩ := exists_L2_flux_pairing_of_lipschitz hbounded
    (Analysis.lipschitzWith_gradient_of_hessian_bound hL hupper) (u : H¹(Ω))
  have hcoords : ∀ᵐ x ∂μ,
      ∇ L (WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x)) =
        WithLp.toLp 2 (fun i ↦ q i x) := by
    filter_upwards [hq, gradientCLM_apply_ae u, Lp.euclideanTuple_apply_ae q]
      with x hx hu hq'
    have hu' : ∇ (u : H¹(Ω)) x =
        WithLp.toLp 2 (fun i ↦ derivCoordCLM i u x) := PiLp.ext hu
    have hq'' : Lp.euclideanTuple q x =
        WithLp.toLp 2 (fun i ↦ q i x) := PiLp.ext hq'
    rwa [hu', hq''] at hx
  rw [mem_subdifferential_l2DirichletGradientEnergy_iff_weakEquation
    hΩ hbounded hL hθ hlower hupper u f q hcoords]
  exact forall_congr' fun v ↦ by rw [(hpair v).2]

end PDE.CalculusOfVariations
