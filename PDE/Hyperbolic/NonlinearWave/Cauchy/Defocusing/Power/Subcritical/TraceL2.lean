/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedTrace
public import PDE.Analysis.MeasureTheory.Lp.FiniteMeasureIntegral
import PDE.FDeriv.SpaceTime
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# Time integration controls the retarded trace in L²

Integrating the time derivative up to the cone graph bounds the change from
initial displacement by `T` times the uniform spatial L² velocity bound.
Together with the initial displacement this controls the full H¹ trace,
without a zero boundary trace.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric PDE PDE.Common PDE.Analysis
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The change from the initial slice to a retarded slice has L² norm at most
elapsed time times the uniform velocity norm. -/
theorem lpNorm_retardedTrace_sub_initial_le {u : ℝ^4 → ℝ} (hu : ContDiff ℝ 1 u) (c : ℝ^3) {T E : ℝ}
    (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hvelocity : ∀ t ∈ Icc 0 T, lpNorm (fun x ↦ (∂[0] u) (timeSpaceCons t x)) 2
      (domainMeasure 3 (ball c T)) ≤ E) :
    lpNorm (fun x ↦ retardedTrace u c T x - u (timeSpaceCons 0 x)) 2 (domainMeasure 3 (ball c T)) ≤
      T * E := by
  let μ := domainMeasure 3 (ball c T)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let η := (volume : Measure ℝ).restrict (Icc 0 T)
  let F : ℝ × ℝ^3 → ℝ := fun z ↦
    if z.1 ∈ Icc 0 T ∧ z.1 ≤ T - ‖z.2 - c‖ then (∂[0] u) (timeSpaceCons z.1 z.2) else 0
  have hc : Continuous (fun z : ℝ × ℝ^3 ↦ (∂[0] u) (timeSpaceCons z.1 z.2)) :=
    (hu.continuous_partialDeriv 0).comp (contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous
  have hcut : MeasurableSet {z : ℝ × ℝ^3 | z.1 ∈ Icc 0 T ∧ z.1 ≤ T - ‖z.2 - c‖} :=
    (measurable_fst measurableSet_Icc).inter (measurableSet_le measurable_fst (measurable_const.sub
        (measurable_snd.sub measurable_const).norm))
  have hF : Measurable F := hc.measurable.ite hcut measurable_const
  have hmem (t : ℝ) : MemLp (fun x ↦ (∂[0] u) (timeSpaceCons t x)) 2 μ := by
    have ht : Continuous (fun x : ℝ^3 ↦ (∂[0] u) (timeSpaceCons t x)) :=
      hc.comp (continuous_const.prodMk continuous_id)
    obtain ⟨C, hC⟩ := ((isCompact_closedBall c T).image ht).isBounded.exists_norm_le
    apply MemLp.of_bound ht.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hC _ (mem_image_of_mem _ (ball_subset_closedBall hx))
  have hdom (t : ℝ) (x : ℝ^3) : ‖F (t, x)‖ ≤ ‖(∂[0] u) (timeSpaceCons t x)‖ := by
    dsimp only [F]
    split_ifs
    · exact le_rfl
    · simp
  have hFmem (t : ℝ) : MemLp (fun x ↦ F (t, x)) 2 μ :=
    (hmem t).mono ((hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (hdom t))
  have hbound (t : ℝ) : lpNorm (fun x ↦ F (t, x)) 2 μ ≤ E := by
    by_cases ht : t ∈ Icc 0 T
    · have hn := lpNorm_mono_real (hmem t).norm (hdom t)
      rw [lpNorm_norm (hmem t).aestronglyMeasurable] at hn
      exact hn.trans (hvelocity t ht)
    · have he : (fun x ↦ F (t, x)) = 0 := by
        funext x
        exact ite_eq_right (fun h ↦ ht h.1)
      simpa only [he, lpNorm_zero] using hE
  obtain ⟨_, hnorm⟩ := memLp_integral_of_uniform_bound η μ F hF.aestronglyMeasurable hE hFmem hbound
  have heq : (fun x ↦ ∫ t, F (t, x) ∂η) =ᵐ[μ]
      fun x ↦ retardedTrace u c T x - u (timeSpaceCons 0 x) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hxT : ‖x - c‖ < T := by simpa only [mem_ball, dist_eq_norm] using hx
    have hτ : 0 ≤ T - ‖x - c‖ := (sub_pos.mpr hxT).le
    have hτT : T - ‖x - c‖ ≤ T := sub_le_self T (norm_nonneg _)
    have he : (fun t ↦ F (t, x)) = (Icc 0 (T - ‖x - c‖)).indicator
        (fun t ↦ (∂[0] u) (timeSpaceCons t x)) := by
      funext t
      have hiff : t ∈ Icc 0 T ∧ t ≤ T - ‖x - c‖ ↔ t ∈ Icc 0 (T - ‖x - c‖) := by
        constructor
        · exact fun h ↦ ⟨h.1.1, h.2⟩
        · exact fun h ↦ ⟨⟨h.1, h.2.trans hτT⟩, h.2⟩
      simp only [F, indicator_apply, hiff]
    rw [he, integral_indicator measurableSet_Icc]
    change (∫ t, (∂[0] u) (timeSpaceCons t x)
      ∂((volume.restrict (Icc 0 T)).restrict (Icc 0 (T - ‖x - c‖)))) = _
    rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc le_rfl hτT),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_timeSpaceCons u t x (hu.differentiable one_ne_zero _))
      ((hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  change (eLpNorm _ 2 μ).toReal ≤ _
  rw [← eLpNorm_congr_ae heq]
  have hmass : η.real univ = T := by
    simp [η, measureReal_def, Real.volume_Icc, hT]
  simpa only [hmass, toReal_eLpNorm] using hnorm

/-- The base coordinate of the H¹ retarded trace is bounded by the
initial L² norm plus time times the velocity bound. -/
theorem norm_base_retardedTrace_le {u : ℝ^4 → ℝ} (hu : ContDiff ℝ 1 u) (c : ℝ^3) {T E : ℝ}
    (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hvelocity : ∀ t ∈ Icc 0 T, lpNorm (fun x ↦ (∂[0] u) (timeSpaceCons t x)) 2
      (domainMeasure 3 (ball c T)) ≤ E)
    (U : H¹(ball c T))
    (hbase : baseRepresentative U =ᵐ[domainMeasure 3 (ball c T)] retardedTrace u c T) :
    ‖wkpBaseCoordinateCLM U‖ ≤ lpNorm (fun x ↦ u (timeSpaceCons 0 x)) 2
      (domainMeasure 3 (ball c T)) + T * E := by
  let μ := domainMeasure 3 (ball c T)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hc : Continuous (fun x : ℝ^3 ↦ u (timeSpaceCons 0 x)) :=
    hu.continuous.comp (contDiff_timeSpaceCons_spatial 3 0 (m := 1)).continuous
  obtain ⟨C, hC⟩ := ((isCompact_closedBall c T).image hc).isBounded.exists_norm_le
  have hmem : MemLp (fun x ↦ u (timeSpaceCons 0 x)) 2 μ := by
    apply MemLp.of_bound hc.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hC _ (mem_image_of_mem _ (ball_subset_closedBall hx))
  have hnorm : ‖wkpBaseCoordinateCLM U‖ = lpNorm (retardedTrace u c T) 2 μ := by
    rw [Lp.norm_def]
    change (eLpNorm (baseRepresentative U) 2 μ).toReal = _
    rw [eLpNorm_congr_ae hbase]
    rfl
  rw [hnorm]
  exact (lpNorm_le_lpNorm_add_lpNorm_sub' hmem (by norm_num)).trans
    (add_le_add_right (lpNorm_retardedTrace_sub_initial_le hu c hT hE hvelocity) _)

/-- A bounded initial displacement has uniformly bounded scaled L² norm on
all balls with radius at most `T`. The dimensional factor is the unit-ball volume. -/
theorem lpNorm_initial_div_radius_le {g : ℝ^3 → ℝ} {G r T : ℝ} (hG : 0 ≤ G) (hg : ∀ x, ‖g x‖ ≤ G)
    (c : ℝ^3) (hr : 0 < r) (hrT : r ≤ T) :
    lpNorm g 2 (domainMeasure 3 (ball c r)) / r ≤ G * √(T * volume.real (ball (0 : ℝ^3) 1)) := by
  have : IsFiniteMeasure (domainMeasure 3 (ball c r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hn := lpNorm_mono_real (memLp_const G (μ := domainMeasure 3 (ball c r)) (p := 2)) hg
  rw [lpNorm_const' (by norm_num) (by norm_num), Real.norm_of_nonneg hG] at hn
  have hvol : volume.real (ball c r) = r ^ 3 * volume.real (ball (0 : ℝ^3) 1) := by
    simp only [measureReal_def, Measure.addHaar_ball_of_pos volume c hr,
      finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le 3)]
  have hroot : √(volume.real (ball c r)) ≤
      r * √(T * volume.real (ball (0 : ℝ^3) 1)) := by
    rw [hvol, show r ^ 3 * volume.real (ball (0 : ℝ^3) 1) =
      r ^ 2 * (r * volume.real (ball (0 : ℝ^3) 1)) by ring,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_right hrT ENNReal.toReal_nonneg)) hr.le
  have hn' : lpNorm g 2 (domainMeasure 3 (ball c r)) ≤ G * √(volume.real (ball c r)) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [ENNReal.toReal_ofNat, domainMeasure,
      measureReal_restrict_apply_univ, one_div] using hn
  apply (div_le_iff₀ hr).mpr
  calc
    _ ≤ G * √(volume.real (ball c r)) := hn'
    _ ≤ G * (r * √(T * volume.real (ball (0 : ℝ^3) 1))) := mul_le_mul_of_nonneg_left hroot hG
    _ = _ := by ring

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
