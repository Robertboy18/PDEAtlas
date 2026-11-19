/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.Potential
public import PDE.Spaces.Sobolev.Periodic.RescaledConvergence

/-!
# Rescaled cell correctors and their Sobolev limits

For a bounded measurable periodic uniformly elliptic coefficient, the constructed
cell potential produces canonical Euclidean Sobolev correctors. Their values tend
strongly to zero and their gradients weakly to zero on bounded open domains.
Thus the corrected test gradients converge weakly to the imposed constant gradient.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace
open PDE.Analysis.PeriodicAveraging SobolevSpace.Periodic
open scoped ENNReal Topology InnerProductSpace Sobolev

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))
variable {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)
    {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ)
    (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1) (ht : Tendsto ε l (𝓝 0))

include hΩo ht

/-- The cell potentials define Sobolev correctors with strong value and weak graph limits. -/
theorem exists_rescaledCorrector (ξ : ℝ^n) :
    ∃ U : ι → W^{1,2}(Ω),
      (∀ j, GraphSpace.wkpBaseCoordinateCLM (U j) =
        ε j • rescaleLp hΩ (ε j) (hε j) (hε1 j)
          (valueCLM n (correctorPotential A hα hA ξ).val) ∧
        ∇ (U j) = rescaleLp hΩ (ε j) (hε j) (hε1 j)
          (correctorGradient A hα hA ξ : Lp (ℝ^n) 2 (cellMeasure n))) ∧
      Bornology.IsBounded (range U) ∧
      Tendsto (fun j ↦ GraphSpace.wkpBaseCoordinateCLM (U j)) l (𝓝 0) ∧
      Tendsto (fun j ↦ toWeakSpace ℝ (W^{1,2}(Ω)) (U j)) l
        (𝓝 (toWeakSpace ℝ (W^{1,2}(Ω)) 0)) := by
  let u := (correctorPotential A hα hA ξ).val
  refine ⟨fun j ↦ scaledPotential hΩ hΩo.measurableSet u (ε j) (hε j) (hε1 j),
    fun j ↦ ⟨base_scaledPotential hΩ hΩo.measurableSet u _ _ _, ?_⟩,
    isBounded_range_scaledPotential hΩ u ε hε hε1 hΩo.measurableSet,
    tendsto_base_scaledPotential hΩ u ε hε hε1 hΩo.measurableSet ht,
    tendsto_weak_scaledPotential hΩ u ε hε hε1 hΩo ht⟩
  rw [gradient_scaledPotential]
  change rescaleLp hΩ (ε j) (hε j) (hε1 j)
    (meanZeroGradientCLM n (correctorPotential A hα hA ξ)) = _
  rw [meanZeroGradientCLM_correctorPotential]

/-- The rescaled cell correction converges weakly to zero in local `L²`. -/
theorem tendsto_weak_rescale_correctorGradient (ξ : ℝ^n) :
    Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω))
      (rescaleLp hΩ (ε j) (hε j) (hε1 j)
        (correctorGradient A hα hA ξ : Lp (ℝ^n) 2 (cellMeasure n)))) l
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω)) 0)) := by
  have h := tendsto_weak_rescale_gradient hΩ
    (correctorPotential A hα hA ξ).val ε hε hε1 hΩo ht
  change Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω))
    (rescaleLp hΩ (ε j) (hε j) (hε1 j)
      (meanZeroGradientCLM n (correctorPotential A hα hA ξ)))) l _ at h
  simpa only [meanZeroGradientCLM_correctorPotential] using h

/-- The corrected cell fields converge weakly to the imposed constant gradient. -/
theorem tendsto_weak_rescale_correctedField [IsFiniteMeasure (domainMeasure n Ω)]
    (ξ : ℝ^n) :
    Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω))
      (rescaleLp hΩ (ε j) (hε j) (hε1 j) (correctedField A hα hA ξ))) l
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω))
        (Lp.const 2 (domainMeasure n Ω) ξ))) := by
  have he (j : ι) : rescaleLp hΩ (ε j) (hε j) (hε1 j) (correctedField A hα hA ξ) =
      Lp.const 2 (domainMeasure n Ω) ξ + rescaleLp hΩ (ε j) (hε j) (hε1 j)
        (correctorGradient A hα hA ξ : Lp (ℝ^n) 2 (cellMeasure n)) := by
    change rescaleLp hΩ (ε j) (hε j) (hε1 j)
      (Lp.const 2 (cellMeasure n) ξ +
        (correctorGradient A hα hA ξ : Lp (ℝ^n) 2 (cellMeasure n))) = _
    rw [map_add, rescaleLp_const]
  simp only [he, map_add]
  simpa only [map_zero, add_zero] using
    (tendsto_const_nhds (x := toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω))
      (Lp.const 2 (domainMeasure n Ω) ξ))).add
        (tendsto_weak_rescale_correctorGradient A hα hA hΩ hΩo ε hε hε1 ht ξ)

end PDE.Elliptic.Homogenization.PeriodicCell
