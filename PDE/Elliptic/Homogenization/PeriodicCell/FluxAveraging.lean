/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.Adjoint
public import PDE.Analysis.Integration.PeriodicAveraging.VectorAveraging

/-!
# Weak limits of the constructed periodic cell fluxes

The flux of each constructed cell corrector is square-integrable. General periodic
L² averaging gives its weak Euclidean limit, and the cell formula identifies that
limit with the effective operator. The same statement for the adjoint medium has
limit equal to the adjoint effective operator.

These are cell-flux limits; the flux of a Dirichlet solution is identified in
`PeriodicCell.FluxConvergence`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
    {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)

/-- Rescaling the cell coefficient operator gives the pointwise microscopic flux. -/
theorem rescale_coefficientOperator_ae (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Lp (ℝ^n) 2 (cellMeasure n)) :
    rescaleLp hΩ ε hε hε1 (coefficientOperator A v) =ᵐ[volume.restrict Ω]
      fun x ↦ A (toTorus n (ε⁻¹ • x)) (v (toTorus n (ε⁻¹ • x))) := by
  exact (rescaleLp_ae hΩ ε hε hε1 (coefficientOperator A v)).trans
    (ae_restrict_of_ae ((quasiMeasurePreserving_toTorus_smul n ε⁻¹
      (inv_ne_zero hε.ne')).ae_eq_comp (coefficientOperator_ae A v)))

variable {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    (hΩm : MeasurableSet Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {ι : Type*} {l : Filter ι}
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0))

include hΩm ht

/-- The flux of a constructed periodic cell corrector converges weakly to the effective flux. -/
theorem tendsto_weak_rescale_cellFlux (ξ : ℝ^n) :
    Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 (volume.restrict Ω))
      (rescaleLp hΩ (ε j) (hε j) (hε1 j)
        (coefficientOperator A (correctedField A hα hA ξ)))) l
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 (volume.restrict Ω))
        (Lp.const 2 (volume.restrict Ω) (effectiveOperator A hα hA ξ)))) := by
  have hmean : (∫ x, coefficientOperator A (correctedField A hα hA ξ) x
      ∂cellMeasure n) = effectiveOperator A hα hA ξ :=
    (integral_congr_ae (coefficientOperator_ae A _)).trans
      (effectiveOperator_eq_mean_flux A hα hA ξ).symm
  simpa only [hmean] using tendsto_weak_rescaleLp_euclidean hΩ hΩm ε hε hε1 ht
    (coefficientOperator A (correctedField A hα hA ξ))

/-- Adjoint cell fluxes converge weakly to the adjoint effective flux. -/
theorem tendsto_weak_rescale_adjointCellFlux (ξ : ℝ^n) :
    Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 (volume.restrict Ω))
      (rescaleLp hΩ (ε j) (hε j) (hε1 j)
        (coefficientOperator (adjointCoefficient A)
          (correctedField (adjointCoefficient A) hα
            (adjointCoefficient_elliptic A hA) ξ)))) l
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 (volume.restrict Ω))
        (Lp.const 2 (volume.restrict Ω) ((effectiveOperator A hα hA).adjoint ξ)))) := by
  simpa only [effectiveOperator_adjoint A hα hA] using
    tendsto_weak_rescale_cellFlux (adjointCoefficient A) hΩ hα
      (adjointCoefficient_elliptic A hA) hΩm ε hε hε1 ht ξ

end PDE.Elliptic.Homogenization.PeriodicCell
