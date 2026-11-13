/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.SmoothBounds
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.Observation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.WeakImage

/-!
# Uniform Sobolev composition bounds

Smooth compact density and weak compactness transfer the explicit smooth
composition estimates to arbitrary Sobolev inputs. This proves boundedness on
norm balls without assuming strong continuity of the nonlinear composition.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]

/-- On smooth compact inputs the constructed reaction lift is the classical
composition graph. -/
theorem higherComposition_smoothGraph (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {u : ℝ^n → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport u) :
    higherComposition hk hf hf0 (mkWkpSpaceOnOfContDiff u hu hc) =
      mkWkpSpaceOnOfContDiff (f ∘ u) (hf.comp hu) (hc.comp_left hf0) := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ _ _
  have he := higherComposition_ae hk hf hf0 (mkWkpSpaceOnOfContDiff u hu hc)
  have hu' := wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae (k := k) (Ω := univ) hu hc
  have hf' := wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae
    (k := k) (Ω := univ) (hf.comp hu) (hc.comp_left hf0)
  simp only [baseRepresentative, domainMeasure, Measure.restrict_univ] at he hu' hf' ⊢
  filter_upwards [he, hu', hf'] with x hx hu hf using hx.trans ((congrArg f hu).trans hf.symm)

/-- Smooth scalar composition fixing zero maps every Sobolev norm ball to
a bounded set. The bound is derived from finite scalar derivative bounds on
the value range furnished by the Sobolev embedding. -/
theorem exists_norm_higherComposition_bound (hk : (n : ℝ) < 2 * ((k : ℝ) - 1)) {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) {R : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : W^{k,2}(ℝ^n), ‖u‖ ≤ R → ‖higherComposition hk hf hf0 u‖ ≤ C := by
  by_cases hR : 0 ≤ R
  swap
  · exact ⟨0, le_rfl, fun u hu ↦ absurd ((norm_nonneg u).trans hu) hR⟩
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_smooth_composition_bound hk hf hf0 (by linarith : 0 ≤ R + 1)
  refine ⟨C, hC, fun u hur ↦ ?_⟩
  obtain ⟨v, hv, hc, hlim⟩ := globalApproximation_WkpSpace
    (Approximation.standardMollifier n) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) k u
  let V (j : ℕ) : W^{k,2}(ℝ^n) := mkWkpSpaceOnOfContDiff (v j) (hv j) (hc j)
  have hV : Tendsto V atTop (𝓝 u) := tendsto_iff_norm_sub_tendsto_zero.mpr hlim
  have hevent : ∀ᶠ j in atTop, ‖V j‖ ≤ R + 1 := by
    have hlt : ‖u‖ < R + 1 := by linarith
    filter_upwards [hV.norm.eventually (gt_mem_nhds hlt)] with j hj using hj.le
  obtain ⟨N, hN⟩ := hevent.exists_forall_of_atTop
  let W (j : ℕ) := higherComposition hk hf hf0 (V (j + N))
  have hW (j : ℕ) : ‖W j‖ ≤ C := by
    dsimp [W, V]
    rw [higherComposition_smoothGraph]
    exact hbound _ _ _ (hN (j + N) (by omega))
  have hobs : Tendsto (fun j ↦ classicalRepresentativeCLM hk (W j)) atTop
      (𝓝 (classicalRepresentativeCLM hk (higherComposition hk hf hf0 u))) :=
    ((locallyLipschitz_observed_composition hk hf hf0).continuous.tendsto u).comp
      (hV.comp (tendsto_add_atTop_nat N))
  obtain ⟨w, hw, he⟩ := exists_lift_of_tendsto_observation
    (classicalRepresentativeCLM hk) W _ hW hobs
  have he' : w = higherComposition hk hf hf0 u := classicalRepresentativeCLM_injective hk he
  exact he' ▸ hw

end PDE.Hyperbolic.NonlinearWave.Cauchy
