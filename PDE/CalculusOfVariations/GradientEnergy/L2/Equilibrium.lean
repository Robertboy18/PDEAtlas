/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.GradientEnergy.L2.FirstVariation
import PDE.Spaces.Sobolev.Calculus.IntegrationByParts.Constant

/-!
# Zero equilibrium for an autonomous Dirichlet gradient energy

The flux at zero may be nonzero. Its constant components annihilate
every zero-boundary test, so zero is still an equilibrium of
the ambient L² subdifferential. No normalization of the density or its
first derivative is required.
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace Analysis.Convex
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

variable {n : ℕ} {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}

/-- An arbitrary constant flux at zero contributes nothing to the
Dirichlet first variation. Thus zero is an L² equilibrium. -/
theorem zero_mem_subdifferential_l2DirichletGradientEnergy
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C) :
    (0 : DerivLp n 2 Ω) ∈ subdifferential (l2DirichletGradientEnergy L) 0 := by
  let := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  let q (i : Fin n) : DerivLp n 2 Ω :=
    wkpBaseCoordinateCLM (wkpConstant (∇ L 0 i))
  have hq (i : Fin n) : (q i : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun _ ↦ ∇ L 0 i :=
    wkpConstant_base_ae _
  have hz : ∀ᵐ x ∂domainMeasure n Ω, ∀ i : Fin n,
      derivCoordCLM i (0 : H¹₀(Ω)) x = 0 :=
    ae_all_iff.mpr fun i ↦ by
      filter_upwards [Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hx
      simpa only [map_zero, Pi.zero_apply] using hx
  have hflux : ∀ᵐ x ∂domainMeasure n Ω,
      ∇ L (WithLp.toLp 2 (fun i ↦ derivCoordCLM i (0 : H¹₀(Ω)) x)) =
        WithLp.toLp 2 (fun i ↦ q i x) := by
    filter_upwards [hz, ae_all_iff.mpr hq] with x hx hy
    have hzero : WithLp.toLp 2 (fun i ↦ derivCoordCLM i (0 : H¹₀(Ω)) x) = 0 :=
      PiLp.ext hx
    rw [hzero]
    exact PiLp.ext fun i ↦ (hy i).symm
  have hmem := (mem_subdifferential_l2DirichletGradientEnergy_iff_weakEquation
    hΩ hbounded hL hθ hlower hupper 0 0 q hflux).mpr fun v ↦ by
      simp only [inner_zero_left]
      exact Finset.sum_eq_zero fun i _ ↦
        inner_constant_derivCoordCLM_eq_zero (∇ L 0 i) (q i) (hq i) i v
  simpa only [map_zero] using hmem

end PDE.CalculusOfVariations
