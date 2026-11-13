/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cone.Coarea
import PDE.FDeriv.SpaceTime

/-!
# Continuous fluxes evaluated at the radial normal

A continuous function of a point and a unit normal gives an integrable cone
trace even though the radial normal is undefined at the vertex. The angular
parametrization retains the normal there and is continuous in time.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common WaveEquation

namespace PDE.Analysis

variable {n : ℕ}

/-- Evaluation of a flux at the outward spatial radial normal. -/
def coneNormalTrace (H : ℝ^(n + 1) × ℝ^n → ℝ) (c : ℝ^n) (p : ℝ^(n + 1)) : ℝ :=
  H (p, NormedSpace.normalize (spatialPart p - c))

/-- The radial-normal trace is measurable, including at the vertex. -/
theorem measurable_coneNormalTrace {H : ℝ^(n + 1) × ℝ^n → ℝ}
    (hH : Continuous H) (c : ℝ^n) : Measurable (coneNormalTrace H c) := by
  have hm : Measurable (fun p : ℝ^(n + 1) ↦ NormedSpace.normalize (spatialPart p - c)) := by
    unfold NormedSpace.normalize
    have hx : Measurable (fun p : ℝ^(n + 1) ↦ spatialPart p - c) :=
      (spatialPartCLM n).continuous.measurable.sub measurable_const
    exact hx.norm.inv.smul hx
  exact hH.measurable.comp (measurable_id.prodMk hm)

/-- The pullback of a continuous normal-dependent flux is integrable on every finite ball. -/
theorem integrableOn_coneNormalTrace_graph {H : ℝ^(n + 1) × ℝ^n → ℝ}
    (hH : Continuous H) (c : ℝ^n) (T R : ℝ) :
    IntegrableOn (fun x ↦ coneNormalTrace H c (backwardConeGraph c T x))
      (Metric.ball c R) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_backwardConeGraph c T
  let S := (backwardConeGraph c T '' Metric.closedBall c R) ×ˢ
    Metric.closedBall (0 : ℝ^n) 1
  have hS : IsCompact S := ((isCompact_closedBall c R).image hK.continuous).prod
    (isCompact_closedBall (0 : ℝ^n) 1)
  obtain ⟨M, hM⟩ := hS.bddAbove_image hH.norm.continuousOn
  have hbound (x : ℝ^n) (hx : x ∈ Metric.ball c R) :
      ‖coneNormalTrace H c (backwardConeGraph c T x)‖ ≤ M := by
    apply hM
    apply mem_image_of_mem
    refine ⟨mem_image_of_mem _ (Metric.ball_subset_closedBall hx), ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases h : spatialPart (backwardConeGraph c T x) - c = 0
    · simp [h]
    · exact (NormedSpace.norm_normalize h).le
  have hm := (measurable_coneNormalTrace hH c).comp hK.continuous.measurable
  have hi : IntegrableOn (fun _ : ℝ^n ↦ M) (Metric.ball c R) volume :=
    (integrableOn_const (μ := volume) (C := M)
      (isCompact_closedBall c R).measure_ne_top).mono_set Metric.ball_subset_closedBall
  exact hi.mono' hm.aestronglyMeasurable.restrict
    ((ae_restrict_mem measurableSet_ball).mono hbound)

/-- The angular integral retains an independent unit normal at the cone vertex. -/
def coneAngularIntegral (H : ℝ^(n + 1) × ℝ^n → ℝ) (c : ℝ^n) (T t : ℝ) : ℝ :=
  |T - t| ^ (n - 1) * ∫ ω : Metric.sphere (0 : ℝ^n) 1,
    H (timeSpaceCons t (c + (T - t) • (ω : ℝ^n)), ω)
      ∂((volume : Measure (ℝ^n)).toSphere)

/-- A continuous normal-dependent flux has a continuous angular integral through the vertex. -/
theorem continuous_coneAngularIntegral {H : ℝ^(n + 1) × ℝ^n → ℝ}
    (hH : Continuous H) (c : ℝ^n) (T : ℝ) :
    Continuous (coneAngularIntegral H c T) := by
  let f (t : ℝ) (ω : Metric.sphere (0 : ℝ^n) 1) : ℝ :=
    H (timeSpaceCons t (c + (T - t) • (ω : ℝ^n)), ω)
  have hω : Continuous (fun p : ℝ × Metric.sphere (0 : ℝ^n) 1 ↦ (p.2 : ℝ^n)) :=
    continuous_subtype_val.comp continuous_snd
  have hp : Continuous (fun p : ℝ × Metric.sphere (0 : ℝ^n) 1 ↦
      timeSpaceCons p.1 (c + (T - p.1) • (p.2 : ℝ^n))) :=
    (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
      (continuous_fst.prodMk
        (continuous_const.add ((continuous_const.sub continuous_fst).smul hω)))
  have hf : Continuous (Function.uncurry f) := hH.comp (hp.prodMk hω)
  have hi : Continuous (fun t ↦ ∫ ω, f t ω
      ∂((volume : Measure (ℝ^n)).toSphere)) := by
    simpa only [Measure.restrict_univ] using continuous_parametric_integral_of_continuous
      (μ := (volume : Measure (ℝ^n)).toSphere) hf isCompact_univ
  exact (((continuous_const.sub continuous_id).abs).pow (n - 1)).mul hi

/-- Away from the vertex, the angular and radial-normal expressions coincide. -/
theorem sphereIntegral_coneNormalTrace_eq_angular
    (H : ℝ^(n + 1) × ℝ^n → ℝ) (c : ℝ^n) (T : ℝ)
    {t : ℝ} (ht : t < T) :
    sphereIntegral n (fun x ↦ coneNormalTrace H c (timeSpaceCons t x)) c (T - t) =
      coneAngularIntegral H c T t := by
  unfold sphereIntegral coneAngularIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards with ω
  unfold coneNormalTrace
  rw [spatialPart_timeSpaceCons, add_sub_cancel_left,
    NormedSpace.normalize_smul_of_pos (sub_pos.mpr ht),
    NormedSpace.normalize_eq_self_of_norm_eq_one (mem_sphere_zero_iff_norm.mp ω.property)]

/-- Cone flux is integrable in time up to the vertex, also in one spatial dimension. -/
theorem intervalIntegrable_sphereIntegral_coneNormalTrace
    {H : ℝ^(n + 1) × ℝ^n → ℝ} (hH : Continuous H) (c : ℝ^n)
    {s τ T : ℝ} (hsτ : s ≤ τ) (hτ : τ ≤ T) :
    IntervalIntegrable (fun t ↦ sphereIntegral n
      (fun x ↦ coneNormalTrace H c (timeSpaceCons t x)) c (T - t)) volume s τ := by
  apply ((continuous_coneAngularIntegral hH c T).intervalIntegrable s τ).congr_uIoo
  intro t ht
  rw [uIoo_of_le hsτ] at ht
  exact (sphereIntegral_coneNormalTrace_eq_angular H c T (ht.2.trans_le hτ)).symm

/-- Radial sections of the graph pullback are the angular sections at complementary times. -/
theorem sphereIntegral_coneNormalTrace_graph
    (H : ℝ^(n + 1) × ℝ^n → ℝ) (c : ℝ^n) (T : ℝ)
    {r : ℝ} (hr : 0 < r) :
    sphereIntegral n (fun x ↦ coneNormalTrace H c (backwardConeGraph c T x)) c r =
      coneAngularIntegral H c T (T - r) := by
  rw [← sphereIntegral_coneNormalTrace_eq_angular H c T (by linarith), sub_sub_cancel]
  apply sphereIntegral_congr_on_sphere hr
  intro x hx
  have hx' : ‖x - c‖ = r := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
  simp only [backwardConeGraph, hx']

/-- Radial sections of a continuous normal flux are integrable on every finite radial interval. -/
theorem integrableOn_sphereIntegral_coneNormalTrace_graph
    {H : ℝ^(n + 1) × ℝ^n → ℝ} (hH : Continuous H) (c : ℝ^n) (T : ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun r ↦ sphereIntegral n
      (fun x ↦ coneNormalTrace H c (backwardConeGraph c T x)) c r) (Icc 0 R) := by
  have hi : IntervalIntegrable (fun r : ℝ ↦ coneAngularIntegral H c T (T - r)) volume 0 R :=
    ((continuous_coneAngularIntegral hH c T).comp
      (continuous_const.sub continuous_id)).intervalIntegrable 0 R
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hR).1
  apply hi.congr_uIoo
  intro r hr
  rw [uIoo_of_le hR] at hr
  exact (sphereIntegral_coneNormalTrace_graph H c T hr.1).symm

end PDE.Analysis
