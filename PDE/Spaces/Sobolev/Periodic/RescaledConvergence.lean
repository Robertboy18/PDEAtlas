/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.RescaledPotential
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WeakConvergence

/-!
# Convergence of rescaled periodic Sobolev potentials

The base of `ε u(x/ε)` tends strongly to zero in local `L²`, while its Sobolev norm
stays bounded. The weak compactness and base-coordinate identification
theorem gives weak `H¹` convergence to zero on every bounded open domain.
Consequently the rescaled periodic gradient converges weakly to zero in local `L²`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.Periodic

variable {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : Bornology.IsBounded Ω)
    {ι : Type*} {l : Filter ι}
    (u : h1Space n) (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)

/-- The rescaled Sobolev potentials are uniformly bounded in the canonical graph space. -/
theorem isBounded_range_scaledPotential (hΩm : MeasurableSet Ω) :
    Bornology.IsBounded (range (fun j ↦ scaledPotential hΩ hΩm u (ε j) (hε j) (hε1 j))) := by
  obtain ⟨C, hC⟩ := exists_norm_scaledPotential_le hΩ hΩm u
  apply isBounded_iff_forall_norm_le.mpr
  exact ⟨C, fun _ ⟨j, hj⟩ ↦ hj ▸ hC (ε j) (hε j) (hε1 j)⟩

/-- The base of the rescaled potential converges strongly to zero in local `L²`. -/
theorem tendsto_base_scaledPotential (hΩm : MeasurableSet Ω)
    (ht : Tendsto ε l (𝓝 0)) :
    Tendsto (fun j ↦ GraphSpace.wkpBaseCoordinateCLM
      (scaledPotential hΩ hΩm u (ε j) (hε j) (hε1 j))) l (𝓝 0) := by
  simp only [base_scaledPotential]
  exact tendsto_smul_rescaleLp hΩ ε hε hε1 ht (valueCLM n u)

/-- Periodically rescaled potentials converge weakly to zero in the Euclidean Sobolev space. -/
theorem tendsto_weak_scaledPotential (hΩo : IsOpen Ω) (ht : Tendsto ε l (𝓝 0)) :
    Tendsto (fun j ↦ toWeakSpace ℝ (W^{1,2}(Ω))
      (scaledPotential hΩ hΩo.measurableSet u (ε j) (hε j) (hε1 j))) l
      (𝓝 (toWeakSpace ℝ (W^{1,2}(Ω)) 0)) := by
  apply GraphSpace.tendsto_weak_hk_of_base hΩo _ 0
    (isBounded_range_scaledPotential hΩ u ε hε hε1 hΩo.measurableSet)
  convert!
    ((toWeakSpaceCLM ℝ (GraphSpace.DerivLp n 2 Ω)).continuous.tendsto 0).comp
      (tendsto_base_scaledPotential hΩ u ε hε hε1 hΩo.measurableSet ht) using 1

/-- The rescaled gradient of a periodic Sobolev function has weak local `L²` limit zero. -/
theorem tendsto_weak_rescale_gradient (hΩo : IsOpen Ω) (ht : Tendsto ε l (𝓝 0)) :
    Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω))
      (rescaleLp hΩ (ε j) (hε j) (hε1 j) (gradientCLM n u))) l
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω)) 0)) := by
  have h := (WeakSpace.map
    (GraphSpace.wkpGradientCLM (n := n) (p := 2) (Ω := Ω))).continuous.tendsto
      (toWeakSpace ℝ (W^{1,2}(Ω)) 0) |>.comp
      (tendsto_weak_scaledPotential hΩ u ε hε hε1 hΩo ht)
  change Tendsto (fun j ↦ toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω))
    (∇ (scaledPotential hΩ hΩo.measurableSet u (ε j) (hε j) (hε1 j)))) l
      (𝓝 (toWeakSpace ℝ (Lp (ℝ^n) 2 (domainMeasure n Ω)) (∇ (0 : W^{1,2}(Ω))))) at h
  simpa only [gradient_scaledPotential, map_zero] using h

end SobolevSpace.Periodic
