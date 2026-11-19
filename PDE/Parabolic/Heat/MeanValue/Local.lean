/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.Localization
public import PDE.Parabolic.Heat.MeanValue
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import PDE.Parabolic.Heat.MeanValue.Topology

/-!
# Local heat-ball mean values

A compactly contained heat ball admits a smooth cutoff equal to one near its
closure. The cutoff product retains joint C¹ regularity and spatial C² slices,
so the global scale and flux calculation applies. Equality on neighborhoods
transfers the heat equation and the mean-value identity back to the
original function.
-/

@[expose] public section

open PDE (SpaceTime laplacian time)

namespace HeatEquation

open Filter MeasureTheory Set
open PDE.Common
open scoped Topology

variable {n : ℕ}

/-- A field continuous on the closed heat ball is integrable against Watson's
weight, including the integrable singularity at the pole. -/
theorem integrableOn_heatBallWeight_mul
    (hn : 0 < n) {u : SpaceTime n → ℝ} {x : ℝ^n} {t r : ℝ} (hr : 0 < r)
    (hu : ContinuousOn u (closure (heatBall x t r))) :
    IntegrableOn (fun p ↦ heatBallWeight x t p * u p) (heatBall x t r) := by
  have hK : IsCompact (closure (heatBall x t r)) := isCompact_closure_heatBall hn hr
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu
  apply (integrableOn_heatBallWeight hn x t hr).mul_bdd (c := C)
    (hu.aestronglyMeasurable_of_subset_isCompact hK
      (measurableSet_heatBall x t r) subset_closure)
  filter_upwards [self_mem_ae_restrict (measurableSet_heatBall x t r)] with p hp
  exact hC p (subset_closure hp)

/-- The heat-ball mean-value formula from local joint C¹ and spatial C² regularity
on an open neighborhood of the closed heat ball. -/
theorem heatBall_meanValue_of_contDiffOn
    (hn : 0 < n) {u : SpaceTime n → ℝ} {Ω : Set (SpaceTime n)}
    (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 1 u Ω)
    (huSpace : ∀ s, ContDiffOn ℝ 2 (fun y ↦ u (timeSpaceCons s y))
      ((timeSpaceCons s) ⁻¹' Ω))
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r)
    (hclosure : closure (heatBall x t r) ⊆ Ω)
    (hcaloric : ∀ p ∈ heatBall x t r, heatOperator u p = 0) :
    (∫ p in heatBall x t r, heatBallWeight x t p * u p) =
      4 * r ^ n * u (timeSpaceCons t x) := by
  obtain ⟨v, hv, hvSpace, _, heq⟩ :=
    PDE.Analysis.exists_contDiff_compactSupport_eventuallyEq_of_contDiffOn_slices
      hΩ (isCompact_closure_heatBall hn hr) hclosure hu huSpace
  have hcaloricV : ∀ p ∈ heatBall x t r, heatOperator v p = 0 := by
    intro p hp
    have hnear := heq p (subset_closure hp)
    have hslice :
        (fun y ↦ v (timeSpaceCons (time p) y)) =ᶠ[𝓝 (spatialPart p)]
          (fun y ↦ u (timeSpaceCons (time p) y)) := by
      apply hnear.comp_tendsto
      simpa only [ContinuousAt, time, timeSpaceCons_spatialPart] using
        (contDiff_timeSpaceCons_spatial n (time p) (m := 1)).continuous.continuousAt
          (x := spatialPart p)
    have hresidual : heatOperator v p = heatOperator u p := by
      simp only [heatOperator, spatialPartCLM_eq_spatialPart]
      change (∂[0] v) p -
          laplacian (fun y ↦ v (timeSpaceCons (time p) y)) (spatialPart p) =
        (∂[0] u) p -
          laplacian (fun y ↦ u (timeSpaceCons (time p) y)) (spatialPart p)
      rw [(hnear.partialDeriv 0).self_of_nhds,
        EuclideanLaplacian.laplacian_congr_nhds hslice]
    exact hresidual.trans (hcaloric p hp)
  calc
    (∫ p in heatBall x t r, heatBallWeight x t p * u p) =
        ∫ p in heatBall x t r, heatBallWeight x t p * v p := by
      apply setIntegral_congr_fun (measurableSet_heatBall x t r)
      intro p hp
      exact congrArg (fun a ↦ heatBallWeight x t p * a)
        (heq p (subset_closure hp)).self_of_nhds.symm
    _ = 4 * r ^ n * v (timeSpaceCons t x) :=
      heatBall_meanValue hn v hv hvSpace x t hr hcaloricV
    _ = 4 * r ^ n * u (timeSpaceCons t x) := by
      rw [(heq _ (pole_mem_closure_heatBall hn)).self_of_nhds]

end HeatEquation
