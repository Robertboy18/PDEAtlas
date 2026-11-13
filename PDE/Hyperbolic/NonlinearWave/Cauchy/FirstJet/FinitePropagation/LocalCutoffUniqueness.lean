/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalCutoffError
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.ForcedInteriorAgreement

/-!
# Interior uniqueness for local weak waves

Compact localization gives continuous forced representatives. Their common
initial term cancels, and the forcing errors vanish where the cutoff is one.
The exterior-forcing estimate then gives equality of the original local
energy states almost everywhere in time on every smaller ball.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {Ω : Set (ℝ^n)} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- Two local Bochner weak waves with common data agree on an interior ball
until the relative-gradient travel bound reaches its surrounding cutoff. -/
theorem IsLocalBochnerWeakCurveOn.restrict_eq_ae (hΩ : IsOpen Ω) {R c T : ℝ} (hR : 0 < R)
    (hball : Metric.ball 0 (3 * R) ⊆ Ω) (η : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hη : tsupport η.toFun ⊆ Ω)
    (hone : ∀ y ∈ Metric.ball 0 (3 * R), η y = 1) {hf : LipschitzWith L f} {hf0 : f 0 = 0}
    {x : H¹(Ω) × DerivLp n 2 Ω} {u v : ℝ → H¹(Ω) × DerivLp n 2 Ω}
    (hu : IsLocalBochnerWeakCurveOn hf hf0 x T u) (hv : IsLocalBochnerWeakCurveOn hf hf0 x T v)
    (hc : 0 ≤ c)
    (hgrad : ∀ (i : Fin n) (z : ℝ^n), |(∂[i] (SobolevSpace.Approximation.cutoff R)) z| ≤ c / R)
    (hspeed : (n : ℝ) * (c / R) * T < 1) :
    let hsub : Metric.ball 0 R ⊆ Ω :=
      (Metric.ball_subset_ball (by linarith : R ≤ 3 * R)).trans hball
    (fun t ↦ (restrictCLM Metric.isOpen_ball.measurableSet hsub (u t).1,
      restrictDerivLp hsub (u t).2)) =ᵐ[volume.restrict (Ioc 0 T)]
    (fun t ↦ (restrictCLM Metric.isOpen_ball.measurableSet hsub (v t).1,
      restrictDerivLp hsub (v t).2)) := by
  intro hsub
  let Fu := (Ioc 0 T).indicator (fun t ↦ localCutoffForcing hΩ η hη hf hf0 (u t))
  let Fv := (Ioc 0 T).indicator (fun t ↦ localCutoffForcing hΩ η hη hf hf0 (v t))
  obtain ⟨U, hU, hrepU⟩ := hu.exists_continuous_cutoff hΩ η hη
  obtain ⟨V, hV, hrepV⟩ := hv.exists_continuous_cutoff hΩ η hη
  have hFu : Integrable Fu volume := IntegrableOn.integrable_indicator
      ((memLp_localCutoffForcing hΩ η hη hf hf0 hu.integrable).integrable (by norm_num))
      measurableSet_Ioc
  have hFv : Integrable Fv volume := IntegrableOn.integrable_indicator
      ((memLp_localCutoffForcing hΩ η hη hf hf0 hv.integrable).integrable (by norm_num))
      measurableSet_Ioc
  let F := fun t ↦ Fu t - Fv t
  let r := fun t ↦ F t - (source hf hf0 (U t) - source hf hf0 (V t))
  have hF : IntervalIntegrable F volume 0 T := (hFu.sub hFv).intervalIntegrable
  have hr : IntervalIntegrable r volume 0 T := hF.sub
    ((((source_lipschitz hf hf0).continuous.comp U.continuous).sub
      ((source_lipschitz hf hf0).continuous.comp V.continuous)).intervalIntegrable 0 T)
  have herr : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      F t = (source hf hf0 (U t) - source hf hf0 (V t)) + r t :=
    .of_forall (fun t ↦ by dsimp only [r]; abel)
  have hzero : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      ∀ᵐ y ∂(domainMeasure n univ).restrict (Metric.closedBall 0 (2 * R)), r t y = 0 := by
    filter_upwards [hU, hV, ae_restrict_mem measurableSet_Ioc] with t htU htV ht
    have he : r t = localCutoffError hΩ η hη hf hf0 (u t) -
        localCutoffError hΩ η hη hf hf0 (v t) := by
      dsimp only [r, F, Fu, Fv]
      rw [indicator_of_mem ht, indicator_of_mem ht, ← htU, ← htV]
      unfold localCutoffError
      abel
    have hz : restrictDerivLp (subset_univ (Metric.ball 0 (3 * R))) (r t) = 0 := by
      rw [he, map_sub, restrict_localCutoffError hΩ Metric.isOpen_ball hball η hη hone,
        restrict_localCutoffError hΩ Metric.isOpen_ball hball η hη hone, sub_self]
    have hae := ae_zero_of_restrictDerivLp_eq_zero (r t) hz
    have hclosed : Metric.closedBall (0 : ℝ^n) (2 * R) ⊆ Metric.ball 0 (3 * R) :=
      Metric.closedBall_subset_ball (by linarith)
    simpa only [domainMeasure, Measure.restrict_univ] using
      hae.filter_mono (ae_mono (domainMeasure_le hclosed))
  have hS : ∀ r, ‖linearSemigroup n r‖ ≤ 1 :=
    waveContractionSemigroup_isContraction (energyTriple n) (massForm n)
      (massForm_coercive n) massForm_symmetric
  let J : DerivLp n 2 univ →L[ℝ] EnergyState n := (C).symm.toContinuousLinearMap.comp
      ((0 : DerivLp n 2 univ →L[ℝ] H¹(ℝ^n)).prod (.id ℝ _))
  have hrep (t : ℝ) : U t - V t =
      C ((linearSemigroup n).duhamel (fun s ↦ (C).symm (0, F s)) t) := by
    have hJu : IntervalIntegrable (fun s ↦ (C).symm (0, Fu s)) volume 0 t :=
      (J.integrable_comp hFu).intervalIntegrable
    have hJv : IntervalIntegrable (fun s ↦ (C).symm (0, Fv s)) volume 0 t :=
      (J.integrable_comp hFv).intervalIntegrable
    rw [hrepU, hrepV, ← map_sub, add_sub_add_left_eq_sub,
      duhamel_sub_of_intervalIntegrable (linearSemigroup n) hS hJu hJv]
    congr 1
    congr 1
    funext s
    change J (Fu s) - J (Fv s) = J (Fu s - Fv s)
    exact (map_sub J _ _).symm
  have hUV (t : ℝ) (ht : t ∈ Icc 0 T) :
      restrictStateCLM (Ω := Metric.ball (0 : ℝ^n) R) Metric.isOpen_ball.measurableSet (U t) =
        restrictStateCLM Metric.isOpen_ball.measurableSet (V t) := by
    have hinterval : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc 0 T := by
      simpa only [uIcc_of_le ht.1, uIcc_of_le hu.interval_nonempty.le] using
        Icc_subset_Icc_right ht.2
    have htime : volume.restrict (Ioc 0 t) ≤ volume.restrict (Ioc 0 T) :=
      Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl
    have hz := energyDensity_sub_eq_zero_on_ball_of_exterior_forcing hf hf0 U V ht.1 hR
      (hF.mono_set hinterval) (hr.mono_set hinterval) (fun s _ ↦ hrep s)
      (herr.filter_mono (ae_mono htime)) (hzero.filter_mono (ae_mono htime)) hc hgrad
      ((mul_le_mul_of_nonneg_left ht.2
        (mul_nonneg (Nat.cast_nonneg n) (div_nonneg hc hR.le))).trans_lt hspeed)
    apply (restrictStateCLM_eq_iff_energyDensity Metric.isOpen_ball _ _).mpr
    simpa only [domainMeasure, Measure.restrict_univ] using
      ae_restrict_of_ae_restrict_of_subset Metric.ball_subset_closedBall hz
  filter_upwards [hU, hV, ae_restrict_mem measurableSet_Ioc] with t htU htV ht
  have hone' : ∀ y ∈ Metric.ball 0 R, η y = 1 :=
    fun y hy ↦ hone y (Metric.ball_subset_ball (by linarith) hy)
  have he := hUV t (Ioc_subset_Icc_self ht)
  rw [← htU, ← htV, restrict_localCutoffStateCLM hΩ Metric.isOpen_ball hsub η hη hone',
    restrict_localCutoffStateCLM hΩ Metric.isOpen_ball hsub η hη hone'] at he
  exact he

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
