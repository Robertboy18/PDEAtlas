/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Hyperbolic.Models.Wave.Fourier.Lp.Evolution
public import PDE.Analysis.MeasureTheory.Integral.OperatorFamily

/-!
# The physical causal L2 Duhamel operator

Unitary Fourier conjugation gives joint continuity of the physical sine
propagator. Its causal integral is a continuous linear operator on L1L2 forcing
confined to a finite time interval, with a Lipschitz displacement trajectory.
Compact continuous dual tests commute with this integral: the required product
integrability is derived from the forcing norm and the sine displacement bound.
-/

@[expose] public section

open MeasureTheory FourierTransform Filter Set
open scoped ENNReal Topology

namespace WaveEquation.Fourier

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Unitary Fourier conjugation preserves the sine trajectory's Lipschitz bound. -/
theorem lipschitzWith_sineEvolution_apply (u : Lp F 2 (volume : Measure V)) :
    LipschitzWith ‖u‖₊ (fun t ↦ sineEvolution t u) := by
  have hi : LipschitzWith 1 (fun v : Lp F 2 (volume : Measure V) ↦ 𝓕⁻ v) :=
    (Lp.fourierTransformₗᵢ V F).symm.isometry.lipschitzWith
  have hn : ‖𝓕 u‖₊ = ‖u‖₊ := NNReal.eq (Lp.norm_fourier_eq u)
  refine LipschitzWith.of_dist_le_mul fun t r ↦ ?_
  change dist (𝓕⁻ (sinePropagator _ t (𝓕 u))) (𝓕⁻ (sinePropagator _ r (𝓕 u))) ≤ _
  have he := (hi.comp (lipschitzWith_sinePropagator_apply
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (ω := fun ξ : V ↦ 2 * Real.pi * ‖ξ‖)
    (continuous_const.mul continuous_norm).measurable (𝓕 u))).dist_le_mul t r
  simpa only [Function.comp_apply, one_mul, hn] using he

/-- The physical sine propagator is Lipschitz even in operator norm. -/
theorem lipschitzWith_sineEvolution :
    LipschitzWith 1 (sineEvolution (V := V) (F := F)) := by
  refine LipschitzWith.of_dist_le_mul fun t r ↦ ?_
  rw [dist_eq_norm, NNReal.coe_one, one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (dist_nonneg : 0 ≤ dist t r) fun u ↦ ?_
  simpa only [sub_apply, dist_eq_norm, coe_nnnorm,
    mul_comm] using (lipschitzWith_sineEvolution_apply u).dist_le_mul t r

/-- Joint continuity of the Fourier sine evolution. -/
theorem continuous_sineEvolution :
    Continuous (fun z : ℝ × Lp F 2 (volume : Measure V) ↦ sineEvolution z.1 z.2) :=
  ((lipschitzWith_sineEvolution (V := V) (F := F)).continuous.comp
    continuous_fst).clm_apply continuous_snd

/-- The causal sine trajectory keeps the same Lipschitz constant at time zero. -/
theorem lipschitzWith_causalSineEvolution_apply (u : Lp F 2 (volume : Measure V)) (s : ℝ) :
    LipschitzWith ‖u‖₊ (fun t ↦ sineEvolution (max (t - s) 0) u) := by
  have hs : LipschitzWith 1 (fun t : ℝ ↦ max (t - s) 0) :=
    (show LipschitzWith 1 (fun t : ℝ ↦ t - s) from
      LipschitzWith.of_dist_le_mul fun t r ↦ by simp).max_const 0
  refine LipschitzWith.of_dist_le_mul fun t r ↦ ?_
  simpa only [Function.comp_apply, mul_one] using
    ((lipschitzWith_sineEvolution_apply u).comp hs).dist_le_mul t r

/-- On a bounded forcing interval the causal propagator has a uniform L2 bound. -/
theorem ae_norm_causalSineEvolution_le (a b t : ℝ) :
    ∀ᵐ s ∂(volume.restrict (Icc a b)), ∀ u : Lp F 2 (volume : Measure V),
      ‖sineEvolution (max (t - s) 0) u‖ ≤ max (t - a) 0 * ‖u‖ := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  intro u
  refine (norm_sineEvolution_apply_le _ u).trans ?_
  rw [abs_of_nonneg (le_max_right _ _)]
  exact mul_le_mul_of_nonneg_right (max_le_max_right 0 (sub_le_sub_left hs.1 t)) (norm_nonneg u)

/-- The causal physical sine family is integrable for L1L2 forcing on a finite time interval. -/
theorem integrable_causalSineEvolution {a b : ℝ} {f : ℝ → Lp F 2 (volume : Measure V)}
    (hf : Integrable f (volume.restrict (Icc a b))) (t : ℝ) :
    Integrable (fun s ↦ sineEvolution (max (t - s) 0) (f s)) (volume.restrict (Icc a b)) :=
  hf.apply_operatorFamily (fun s ↦ sineEvolution (max (t - s) 0))
    (fun u ↦ ((continuous_sineEvolution_apply u).comp
      ((continuous_const.sub continuous_id).max continuous_const)).aestronglyMeasurable)
    (ae_norm_causalSineEvolution_le a b t)

/-- The physical Duhamel operator for forcing confined to a finite interval.
Causality is part of its Fourier sine integrand. -/
noncomputable def duhamelL2 (a b t : ℝ) :
    Lp (Lp F 2 (volume : Measure V)) 1 (volume.restrict (Icc a b)) →L[ℝ]
      Lp F 2 (volume : Measure V) :=
  Lp.integralOperator (fun s ↦ sineEvolution (max (t - s) 0))
    (fun u ↦ ((continuous_sineEvolution_apply u).comp
      ((continuous_const.sub continuous_id).max continuous_const)).aestronglyMeasurable)
    (ae_norm_causalSineEvolution_le a b t)

/-- Duhamel is the Bochner integral of the physical causal sine evolution. -/
theorem duhamelL2_apply (a b t : ℝ)
    (f : Lp (Lp F 2 (volume : Measure V)) 1 (volume.restrict (Icc a b))) :
    duhamelL2 a b t f = ∫ s in Icc a b, sineEvolution (max (t - s) 0) (f s) := rfl

/-- The displacement estimate for finite-interval L1L2 forcing. -/
theorem norm_duhamelL2_apply_le (a b t : ℝ)
    (f : Lp (Lp F 2 (volume : Measure V)) 1 (volume.restrict (Icc a b))) :
    ‖duhamelL2 a b t f‖ ≤ max (t - a) 0 * ‖f‖ := by
  rw [duhamelL2_apply]
  exact norm_integral_operatorFamily_le
    (E := Lp F 2 (volume : Measure V)) (F := Lp F 2 (volume : Measure V))
    (μ := volume.restrict (Icc a b)) (fun s ↦ sineEvolution (V := V) (F := F) (max (t - s) 0))
    (ae_norm_causalSineEvolution_le a b t) f

/-- The physical Duhamel field vanishes through the initial time. -/
theorem duhamelL2_eq_zero_of_le {a b t : ℝ} (ht : t ≤ a)
    (f : Lp (Lp F 2 (volume : Measure V)) 1 (volume.restrict (Icc a b))) :
    duhamelL2 a b t f = 0 := by
  apply norm_le_zero_iff.mp
  simpa only [max_eq_right (sub_nonpos.mpr ht), zero_mul] using norm_duhamelL2_apply_le a b t f

/-- The physical Duhamel trajectory is Lipschitz, with constant equal
to the L1L2 forcing norm. -/
theorem lipschitzWith_duhamelL2 (a b : ℝ)
    (f : Lp (Lp F 2 (volume : Measure V)) 1 (volume.restrict (Icc a b))) :
    LipschitzWith ‖f‖₊ (fun t ↦ duhamelL2 a b t f) := by
  refine LipschitzWith.of_dist_le_mul fun t r ↦ ?_
  rw [dist_eq_norm, duhamelL2_apply, duhamelL2_apply,
    ← integral_sub (integrable_causalSineEvolution (L1.integrable_coeFn f) t)
      (integrable_causalSineEvolution (L1.integrable_coeFn f) r)]
  let R : ℝ → Lp F 2 (volume : Measure V) →L[ℝ] Lp F 2 (volume : Measure V) :=
    fun s ↦ sineEvolution (V := V) (F := F) (max (t - s) 0) -
      sineEvolution (V := V) (F := F) (max (r - s) 0)
  have hb : ∀ᵐ s ∂(volume.restrict (Icc a b)), ∀ u : Lp F 2 (volume : Measure V),
      ‖R s u‖ ≤ dist t r * ‖u‖ := by
    filter_upwards with s
    intro u
    simpa only [R, sub_apply, dist_eq_norm, coe_nnnorm,
      mul_comm] using (lipschitzWith_causalSineEvolution_apply u s).dist_le_mul t r
  simpa only [R, sub_apply, coe_nnnorm, mul_comm] using norm_integral_operatorFamily_le R hb f

/-- Compact continuous dual tests may be interchanged with the causal
Duhamel integral. The product integrability required by Fubini is derived from
L1 forcing and the sine displacement bound. -/
theorem integral_test_duhamelL2_eq (a b : ℝ)
    (f : Lp (Lp F 2 (volume : Measure V)) 1 (volume.restrict (Icc a b)))
    (q : ℝ → Lp F 2 (volume : Measure V) →L[ℝ] ℝ) (hq : Continuous q) (hqc : HasCompactSupport q) :
    (∫ t, q t (duhamelL2 a b t f)) =
      ∫ s in Icc a b, ∫ t, q t (sineEvolution (max (t - s) 0) (f s)) := by
  let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
  have hn : Continuous (fun t : ℝ ↦ ‖q t‖) := hq.norm
  have ht : Continuous (fun t : ℝ ↦ max (t - a) 0) :=
    (continuous_id.sub continuous_const).max continuous_const
  have hkc : Continuous (fun t : ℝ ↦ ‖q t‖ * max (t - a) 0) := hn.mul ht
  have hkcs : HasCompactSupport (fun t : ℝ ↦ ‖q t‖ * max (t - a) 0) := hqc.norm.mul_right
  have hk : Integrable (fun t : ℝ ↦ ‖q t‖ * max (t - a) 0) volume :=
    hkc.integrable_of_hasCompactSupport hkcs
  have hm : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ q z.2 (sineEvolution (max (z.2 - z.1) 0) (f z.1)))
        ((volume.restrict (Icc a b)).prod volume) := by
    have hc : Continuous (fun z : ℝ × ℝ ↦ max (z.2 - z.1) 0) :=
      (continuous_snd.sub continuous_fst).max continuous_const
    have hp : AEStronglyMeasurable (fun z : ℝ × ℝ ↦ (max (z.2 - z.1) 0, f z.1))
        ((volume.restrict (Icc a b)).prod volume) :=
      hc.aestronglyMeasurable.prodMk (Lp.aestronglyMeasurable f).comp_fst
    have hs := continuous_sineEvolution.comp_aestronglyMeasurable hp
    exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (((hq.comp continuous_snd).aestronglyMeasurable).prodMk hs)
  have hi : Integrable (fun z : ℝ × ℝ ↦ q z.2 (sineEvolution (max (z.2 - z.1) 0) (f z.1)))
        ((volume.restrict (Icc a b)).prod volume) := by
    apply ((L1.integrable_coeFn f).norm.mul_prod hk).mono' hm
    have ha : ∀ᵐ (z : ℝ × ℝ) ∂((volume.restrict (Icc a b)).prod volume), z.1 ∈ Icc a b := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs using .of_forall fun _ ↦ hs
    filter_upwards [ha] with z hz
    calc
      _ ≤ ‖q z.2‖ * ‖sineEvolution (max (z.2 - z.1) 0) (f z.1)‖ := (q z.2).le_opNorm _
      _ ≤ ‖q z.2‖ * (max (z.2 - a) 0 * ‖f z.1‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        refine (norm_sineEvolution_apply_le _ _).trans ?_
        rw [abs_of_nonneg (le_max_right _ _)]
        exact mul_le_mul_of_nonneg_right
          (max_le_max_right 0 (sub_le_sub_left hz.1 z.2)) (norm_nonneg _)
      _ = _ := by ac_rfl
  calc
    _ = ∫ t, ∫ s in Icc a b, q t (sineEvolution (max (t - s) 0) (f s)) := by
      apply integral_congr_ae
      filter_upwards with t
      exact ((q t).integral_comp_comm
        (integrable_causalSineEvolution (L1.integrable_coeFn f) t)).symm
    _ = _ := (integral_integral_swap hi).symm

end WaveEquation.Fourier
