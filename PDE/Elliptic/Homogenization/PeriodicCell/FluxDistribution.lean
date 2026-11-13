/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.Potential
public import PDE.Spaces.Sobolev.Periodic.FluxTesting

/-!
# Distributional equations for the constructed cell fluxes

The cell variational equation gives orthogonality to all periodic Sobolev gradients.
Periodization transfers it to compact Euclidean tests, and dilation preserves the
zero-divergence equation. On bounded domains the rescaled flux satisfies the
weak divergence functional on the canonical zero-boundary Sobolev space.
Compact localization also permits arbitrary canonical H¹ functions as tests.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open PDE.Analysis.PeriodicAveraging SobolevSpace.Periodic
open scoped ENNReal Topology InnerProductSpace Sobolev Gradient Distributions

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
variable {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)

/-- The constructed cell flux is orthogonal to all periodic Sobolev gradients. -/
theorem cellFlux_orthogonal_periodicGradient (ξ : ℝ^n) (u : h1Space n) :
    ⟪coefficientOperator A (correctedField A hα hA ξ), gradientCLM n u⟫_ℝ = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, ⟪A x (correctedField A hα hA ξ x), gradientCLM n u x⟫_ℝ ∂cellMeasure n := by
      apply integral_congr_ae
      filter_upwards [coefficientOperator_ae A (correctedField A hα hA ξ)] with x hx
      rw [hx]
    _ = 0 := correctorPotential_equation A hα hA ξ u

/-- The rescaled coefficient and corrected field satisfy the Euclidean
zero-divergence equation against every compact C¹ test. -/
theorem integral_rescaled_cellFlux_gradient_eq_zero (ξ : ℝ^n)
    (ε : ℝ) (hε : ε ≠ 0) {φ : ℝ^n → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    (∫ x, ⟪A (toTorus n (ε⁻¹ • x))
      (correctedField A hα hA ξ (toTorus n (ε⁻¹ • x))), ∇ φ x⟫_ℝ) = 0 := by
  have he := (quasiMeasurePreserving_toTorus_smul n ε⁻¹ (inv_ne_zero hε)).ae_eq_comp
    (coefficientOperator_ae A (correctedField A hα hA ξ))
  calc
    _ = ∫ x, ⟪coefficientOperator A (correctedField A hα hA ξ)
        (toTorus n (ε⁻¹ • x)), ∇ φ x⟫_ℝ := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      simpa only [Function.comp_apply] using
        congrArg (fun z ↦ ⟪z, ∇ φ x⟫_ℝ) hx.symm
    _ = 0 := integral_inner_gradient_toTorus_smul_eq_zero
      (coefficientOperator A (correctedField A hα hA ξ))
      (cellFlux_orthogonal_periodicGradient A hα hA ξ) ε⁻¹ (inv_ne_zero hε) hφ hφc

/-- The constructed cell flux satisfies the canonical weak divergence equation
on every bounded domain after periodic rescaling. -/
theorem weakDivergenceFunctional_rescaledCellFlux_eq_zero {Ω : Set (ℝ^n)}
    (hΩ : Bornology.IsBounded Ω) (ξ : ℝ^n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    SobolevSpace.GraphSpace.weakDivergenceFunctional
      (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).compLp
        (rescaleLp hΩ ε hε hε1 (coefficientOperator A (correctedField A hα hA ξ)))) 0 = 0 :=
  weakDivergenceFunctional_rescale_eq_zero hΩ
    (coefficientOperator A (correctedField A hα hA ξ))
    (cellFlux_orthogonal_periodicGradient A hα hA ξ) ε hε hε1

/-- Compact localization allows an arbitrary canonical H¹ function as a test
for the constructed rescaled cell flux. -/
theorem inner_rescaledCellFlux_cutoff_gradient_eq_zero {Ω : Set (ℝ^n)}
    (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω) (ξ : ℝ^n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hκ : tsupport κ.toFun ⊆ Ω) (u : H¹(Ω)) :
    ⟪rescaleLp hΩ ε hε hε1 (coefficientOperator A (correctedField A hα hA ξ)),
      SobolevSpace.GraphSpace.wkpGradientCLM
        (SobolevSpace.GraphSpace.cutoffCLM κ u)⟫_ℝ = 0 :=
  inner_rescale_gradient_eq_zero hΩ
    (coefficientOperator A (correctedField A hα hA ξ))
    (cellFlux_orthogonal_periodicGradient A hα hA ξ) ε hε hε1
    (SobolevSpace.GraphSpace.cutoffH1ToH10 hΩo κ hκ u)

end PDE.Elliptic.Homogenization.PeriodicCell
