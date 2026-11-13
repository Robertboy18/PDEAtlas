/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.MeanValue.Local
import PDE.Parabolic.Heat.Equation.Translation
import PDE.Parabolic.Heat.MeanValue.Topology

/-!
# Heat-ball mean values at a terminal time

Backward translation places a compact heat ball inside the open time interval.
The weighted integrals converge on the fixed heat ball by continuity on a compact
time collar and integrability of Watson's weight. Regularity of the field after
the terminal time is not used.
-/

@[expose] public section

open PDE (SpaceTime time)

namespace HeatEquation

open Filter MeasureTheory Set
open PDE.Common
open scoped Topology

variable {n : ℕ}

private theorem continuousOn_heatBallWeighted_integral
    (hn : 0 < n) {x : ℝ^n} {t r : ℝ} (hr : 0 < r)
    {S : Set ℝ} (hS : IsCompact S) {v : ℝ → SpaceTime n → ℝ}
    (hv : ContinuousOn (Function.uncurry v) (S ×ˢ closure (heatBall x t r))) :
    ContinuousOn (fun δ ↦ ∫ p in heatBall x t r, heatBallWeight x t p * v δ p) S := by
  have hK : IsCompact (closure (heatBall x t r)) := isCompact_closure_heatBall hn hr
  have hW := integrableOn_heatBallWeight hn x t hr
  obtain ⟨C, hC⟩ := (hS.prod hK).exists_bound_of_continuousOn hv
  refine continuousOn_of_dominated (bound := fun p ↦ ‖heatBallWeight x t p‖ * C)
    (fun δ hδ ↦ hW.aestronglyMeasurable.mul ?_) (fun δ hδ ↦ ?_) (hW.norm.mul_const C) ?_
  · exact (hv.comp (continuous_const.prodMk continuous_id).continuousOn fun p hp ↦ ⟨hδ, hp⟩)
      |>.aestronglyMeasurable_of_subset_isCompact hK (measurableSet_heatBall x t r) subset_closure
  · filter_upwards [self_mem_ae_restrict (measurableSet_heatBall x t r)] with p hp
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC (δ, p) ⟨hδ, subset_closure hp⟩) (norm_nonneg _)
  · filter_upwards [self_mem_ae_restrict (measurableSet_heatBall x t r)] with p hp
    exact continuousOn_const.mul (hv.comp (continuous_id.prodMk continuous_const).continuousOn
      fun δ hδ ↦ ⟨hδ, subset_closure hp⟩)

/-- The local heat-ball identity on a time cylinder, including its terminal slice.
Only joint continuity is needed at the terminal time. Joint C¹, spatial C² and
the native heat equation are required on the open time interval. -/
theorem heatBall_meanValue_on_cylinder
    (hn : 0 < n) {U : Set (ℝ^n)} (hU : IsOpen U) {T : ℝ}
    {u : SpaceTime n → ℝ}
    (huContinuous : ContinuousOn u {p | spatialPart p ∈ U ∧ time p ∈ Ioc 0 T})
    (hu : ContDiffOn ℝ 1 u {p | spatialPart p ∈ U ∧ time p ∈ Ioo 0 T})
    (huSpace : ∀ s ∈ Ioo 0 T, ContDiffOn ℝ 2 (fun y ↦ u (timeSpaceCons s y)) U)
    (hcaloric : ∀ p, spatialPart p ∈ U → time p ∈ Ioo 0 T → heatOperator u p = 0)
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r)
    (hclosure : closure (heatBall x t r) ⊆
      {p | spatialPart p ∈ U ∧ time p ∈ Ioc 0 T}) :
    (∫ p in heatBall x t r, heatBallWeight x t p * u p) =
      4 * r ^ n * u (timeSpaceCons t x) := by
  let K := closure (heatBall x t r)
  let O := {p : SpaceTime n | spatialPart p ∈ U ∧ time p ∈ Ioo 0 T}
  let v := fun δ (p : SpaceTime n) ↦ u (p - timeSpaceCons δ 0)
  have hK : IsCompact K := isCompact_closure_heatBall hn hr
  have hO : IsOpen O := by
    change IsOpen ((spaceTimeContinuousLinearEquiv n) ⁻¹' (U ×ˢ Ioo 0 T))
    exact (hU.prod isOpen_Ioo).preimage (spaceTimeContinuousLinearEquiv n).continuous
  have htime (δ : ℝ) (p : SpaceTime n) : time (p - timeSpaceCons δ 0) = time p - δ := by
    simp [time]
  have hspace (δ : ℝ) (p : SpaceTime n) :
      spatialPart (p - timeSpaceCons δ 0) = spatialPart p := by
    simp only [← spatialPartCLM_eq_spatialPart, map_sub, spatialPartCLM_timeSpaceCons, sub_zero]
  have hslice (δ s : ℝ) (y : ℝ^n) :
      timeSpaceCons s y - timeSpaceCons δ 0 = timeSpaceCons (s - δ) y := by
    ext i
    cases i using Fin.cases <;> simp
  obtain ⟨a, ha, hmargin⟩ := hK.exists_forall_le'
    (timeCLM n).continuous.continuousOn (fun p hp ↦ (hclosure hp).2.1)
  obtain ⟨ε, hε, hεa⟩ : ∃ ε, 0 < ε ∧ ε < a := ⟨a / 2, half_pos ha, half_lt_self ha⟩
  have hcollar (δ : ℝ) (hδ : δ ∈ Icc 0 ε) (p : SpaceTime n) (hp : p ∈ K) :
      spatialPart (p - timeSpaceCons δ 0) ∈ U ∧ time (p - timeSpaceCons δ 0) ∈ Ioc 0 T := by
    have hmin : a ≤ time p := hmargin p hp
    rw [hspace, htime]
    exact ⟨(hclosure hp).1, by linarith [hδ.2], by linarith [(hclosure hp).2.2, hδ.1]⟩
  have hcons : Continuous fun δ : ℝ ↦ timeSpaceCons δ (0 : ℝ^n) := by
    simpa only [Function.comp_def, id_eq, timeSpaceContinuousLinearEquiv_symm_apply] using
      (timeSpaceContinuousLinearEquiv n).symm.continuous.comp
        (continuous_id.prodMk (continuous_const (y := (0 : ℝ^n))))
  have hv : ContinuousOn (Function.uncurry v) (Icc 0 ε ×ˢ K) :=
    huContinuous.comp (continuous_snd.sub (hcons.comp continuous_fst)).continuousOn
      fun q hq ↦ hcollar q.1 hq.1 q.2 hq.2
  have hidentity (δ : ℝ) (hδ : δ ∈ Ioo 0 ε) :
      (∫ p in heatBall x t r, heatBallWeight x t p * v δ p) =
        4 * r ^ n * v δ (timeSpaceCons t x) := by
    let Ω := (fun p : SpaceTime n ↦ p - timeSpaceCons δ 0) ⁻¹' O
    have hshift (p : SpaceTime n) (hp : p ∈ K) : p ∈ Ω := by
      have hcol := hcollar δ ⟨hδ.1.le, hδ.2.le⟩ p hp
      refine ⟨hcol.1, hcol.2.1, ?_⟩
      rw [htime]
      linarith [(hclosure hp).2.2, hδ.1]
    have hvSpace (s : ℝ) : ContDiffOn ℝ 2 (fun y ↦ v δ (timeSpaceCons s y))
        ((timeSpaceCons s) ⁻¹' Ω) := by
      intro y hy
      have hs : time (timeSpaceCons s y - timeSpaceCons δ 0) ∈ Ioo 0 T := hy.2
      have hsub : (timeSpaceCons s) ⁻¹' Ω ⊆ U := fun z hz ↦ by
        simpa only [hspace, spatialPart_timeSpaceCons] using hz.1
      rw [htime] at hs
      simpa only [v, hslice] using ((huSpace (s - δ)
        (by simpa only [time, timeSpaceCons_zero] using hs)) y (hsub hy)).mono hsub
    refine heatBall_meanValue_of_contDiffOn hn (hO.preimage (continuous_id.sub continuous_const))
      (hu.comp (contDiff_id.sub contDiff_const).contDiffOn fun _ hp ↦ hp) hvSpace x t hr hshift
      fun p hp ↦ ?_
    change heatOperator (fun q ↦ u (q - timeSpaceCons δ 0)) p = 0
    rw [heatOperator_comp_sub_time]
    exact hcaloric _ (hshift p (subset_closure hp)).1 (hshift p (subset_closure hp)).2
  have hF := continuousOn_heatBallWeighted_integral hn hr isCompact_Icc hv
  have hG : ContinuousOn (fun δ ↦ 4 * r ^ n * v δ (timeSpaceCons t x)) (Icc 0 ε) :=
    continuousOn_const.mul (hv.comp (continuous_id.prodMk continuous_const).continuousOn
      fun δ hδ ↦ ⟨hδ, pole_mem_closure_heatBall hn⟩)
  have := left_nhdsWithin_Ioo_neBot hε
  have hlimit : (∫ p in heatBall x t r, heatBallWeight x t p * v 0 p) =
      4 * r ^ n * v 0 (timeSpaceCons t x) := by
    refine tendsto_nhds_unique ((hF 0 ⟨le_rfl, hε.le⟩).mono Ioo_subset_Icc_self)
      (((hG 0 ⟨le_rfl, hε.le⟩).mono Ioo_subset_Icc_self).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact (hidentity δ hδ).symm
  have hzero : timeSpaceCons 0 (0 : ℝ^n) = 0 := by
    ext i
    cases i using Fin.cases <;> simp
  simpa only [v, hzero, sub_zero] using hlimit

end HeatEquation
