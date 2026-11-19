/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.HigherForcing

/-!
# Restricting higher wave trajectories to a lower energy level

Forgetting derivatives commutes with the constructed wave semigroups and their
Duhamel integrals, in every dimension. The bounds for restricted trajectories that
follow from this are in
`PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiveDimensional.Restriction`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

/-- Forget spatial derivatives in both components of higher wave data. -/
def higherWaveRestrictionCLM (n : ℕ) {r k : ℕ} (h : r ≤ k) :
    (W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) →L[ℝ]
      (W^{r + 1,2}(ℝ^n) × W^{r,2}(ℝ^n)) :=
  (lowerOrderCLM (Nat.add_le_add_right h 1)).prodMap (lowerOrderCLM h)

/-- Restriction between higher wave levels preserves the energy coordinates. -/
theorem higherEnergyInclusionCLM_higherWaveRestrictionCLM
    (n : ℕ) {r k : ℕ} (h : r ≤ k) (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    higherEnergyInclusionCLM n r (higherWaveRestrictionCLM n h x) =
      higherEnergyInclusionCLM n k x := by
  apply (Hyperbolic.Variational.WaveEnergySpace.coordinates
    (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric).injective
  rw [coordinates_higherEnergyInclusionCLM, coordinates_higherEnergyInclusionCLM]
  change (lowerOrderCLM _ (lowerOrderCLM _ x.1), wkpBaseCoordinateCLM (lowerOrderCLM h x.2)) = _
  rw [lowerOrderCLM_trans_apply]
  rfl

/-- The constructed wave semigroups commute with restriction of Sobolev order. -/
theorem higherWaveRestrictionCLM_semigroup (n : ℕ) {r k : ℕ} (h : r ≤ k) (t : ℝ≥0)
    (x : W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)) :
    higherWaveRestrictionCLM n h (higherLinearSemigroup n k t x) =
      higherLinearSemigroup n r t (higherWaveRestrictionCLM n h x) := by
  apply higherEnergyInclusionCLM_injective n r
  rw [higherEnergyInclusionCLM_higherWaveRestrictionCLM,
    higherEnergyInclusionCLM_higherLinearSemigroup, higherEnergyInclusionCLM_higherLinearSemigroup,
    higherEnergyInclusionCLM_higherWaveRestrictionCLM]

/-- Restriction of Sobolev order commutes with the wave Duhamel integral. -/
theorem higherWaveRestrictionCLM_duhamel (n : ℕ) {r k : ℕ} (h : r ≤ k)
    {F : ℝ → W^{k + 1,2}(ℝ^n) × W^{k,2}(ℝ^n)} (hF : Continuous F) (t : ℝ) :
    higherWaveRestrictionCLM n h ((higherLinearSemigroup n k).duhamel F t) =
      (higherLinearSemigroup n r).duhamel (fun s ↦ higherWaveRestrictionCLM n h (F s)) t := by
  unfold StronglyContinuousSemigroup.duhamel
  rw [← (higherWaveRestrictionCLM n h).intervalIntegral_comp_comm
    (((higherLinearSemigroup n k).continuous_duhamelIntegrand hF t).intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  exact higherWaveRestrictionCLM_semigroup n h (t - s).toNNReal (F s)

end PDE.Hyperbolic.NonlinearWave.Cauchy
