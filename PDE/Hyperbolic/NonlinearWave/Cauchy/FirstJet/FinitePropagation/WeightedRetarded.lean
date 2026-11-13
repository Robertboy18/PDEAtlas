/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedDuhamel
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedForcing
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.RetardedGronwall
import CAS.ExactTactic

/-!
# Stability with integrable exterior forcing

The retarded Duhamel bound and the pointwise first-jet Lipschitz estimate
control a continuous energy difference by its integrable forcing error.
The exponent depends linearly on the relative gradient of the spatial weight.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- Integrable forcing errors give a weighted stability bound for continuous
energy trajectories with a common linear initial term. -/
theorem sqrt_weightedEnergyForm_sub_le_of_forcing (hf : LipschitzWith L f) (hf0 : f 0 = 0)
    (u v : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)) {F r : ℝ → DerivLp n 2 univ} {T : ℝ} (hT : 0 ≤ T)
    (hF : IntervalIntegrable F volume 0 T) (hr : IntervalIntegrable r volume 0 T)
    (hrep : ∀ t ∈ Icc 0 T, u t - v t =
      C ((linearSemigroup n).duhamel (fun s ↦ (C).symm (0, F s)) t))
    (herr : ∀ᵐ s ∂volume.restrict (Ioc 0 T), F s =
      (source hf hf0 (u s) - source hf hf0 (v s)) + r s)
    (χ : W^{1,∞}(ℝ^n)) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ha : ∀ᵐ y ∂domainMeasure n univ, 0 ≤ (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    (hd : ∀ i : Fin n, ∀ᵐ y ∂domainMeasure n univ, |(χ : WkpAmbientOn n 1 ∞ univ)
      (singleDerivIndex n i) y| ≤ ρ * (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1) y)
    {c : ℝ} (hc : 0 ≤ c)
    (hsmall : ∀ᵐ s ∂volume.restrict (Ioc 0 T), Real.sqrt (weightedEnergyForm
      ((χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (0, r s) (0, r s)) ≤ c * ‖r s‖) :
    ∀ t ∈ Icc 0 T,
      Real.sqrt (weightedEnergyForm
        ((χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) (u t - v t) (u t - v t)) ≤
      Real.exp (((3 + (n : ℝ) * ρ) / 2 + Real.sqrt (2 + 2 * (L : ℝ) ^ 2)) * t) *
        (c * ∫ s in (0 : ℝ)..T, ‖r s‖) := by
  let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  let B := weightedEnergyForm a
  let e : ℝ → ℝ := fun t ↦ Real.sqrt (B (u t - v t) (u t - v t))
  let K : ℝ := Real.sqrt (2 + 2 * (L : ℝ) ^ 2)
  let ω : ℝ := (3 + (n : ℝ) * ρ) / 2
  have he : Continuous e := Real.continuous_sqrt.comp
    ((B.continuous.comp (u.continuous.sub v.continuous)).clm_apply (u.continuous.sub v.continuous))
  have hforce : ∀ᵐ s ∂volume.restrict (Ioc 0 T),
      Real.sqrt (B (0, F s) (0, F s)) ≤ K * e s + c * ‖r s‖ := by
    filter_upwards [herr, hsmall] with s hs hrsmall
    have hpair : ((0 : H¹(ℝ^n)), F s) =
        (0, source hf hf0 (u s) - source hf hf0 (v s)) + (0, r s) := by
      simp only [hs, Prod.mk_add_mk, zero_add]
    rw [hpair]
    exact (sqrt_bilinear_add_le B (weightedEnergyForm_symmetric a)
      (weightedEnergyForm_nonneg a ha) _ _).trans
        (add_le_add (sqrt_weightedEnergyForm_source_sub_le hf hf0 a ha (u s) (v s)) hrsmall)
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) :
      e t ≤ ∫ s in (0 : ℝ)..t, Real.exp (ω * (t - s)) * (K * e s + c * ‖r s‖) := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
    have hFt : IntervalIntegrable F volume 0 t := hF.mono_set (by
      simpa only [uIcc_of_le ht.1, uIcc_of_le hT] using hsub)
    have hrt : IntervalIntegrable r volume 0 t := hr.mono_set (by
      simpa only [uIcc_of_le ht.1, uIcc_of_le hT] using hsub)
    have hei : IntervalIntegrable e volume 0 t := he.intervalIntegrable _ _
    have hker : Continuous (fun s : ℝ ↦ Real.exp (ω * (t - s))) := by fun_prop
    let J : DerivLp n 2 univ →L[ℝ] (H¹(ℝ^n) × DerivLp n 2 univ) :=
      (0 : DerivLp n 2 univ →L[ℝ] H¹(ℝ^n)).prod (.id ℝ _)
    have hFi : IntervalIntegrable (fun s ↦ Real.sqrt (B (0, F s) (0, F s))) volume 0 t :=
      intervalIntegrable_iff.mpr (integrable_sqrt_bilinear_self B (J.integrable_comp hFt.def'))
    have hleft := hFi.continuousOn_mul hker.continuousOn
    have hright := ((hei.const_mul K).add (hrt.norm.const_mul c)).continuousOn_mul hker.continuousOn
    have hmono : (∫ s in (0 : ℝ)..t, Real.exp (ω * (t - s)) * Real.sqrt (B (0, F s) (0, F s))) ≤
        ∫ s in (0 : ℝ)..t, Real.exp (ω * (t - s)) * (K * e s + c * ‖r s‖) := by
      rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
      apply integral_mono_ae hleft.1 hright.1
      filter_upwards [hforce.filter_mono
        (ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right ht.2) le_rfl))] with s hs
      exact mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
    have hduh := sqrt_weightedEnergyForm_duhamel_le χ hρ ha hd ht.1 hFt
    have hrate : ∀ s : ℝ, (3 + (n : ℝ) * ρ) * (t - s) / 2 = ω * (t - s) := by
      intro s
      dsimp only [ω]
      cas
    simp_rw [hrate] at hduh
    exact (show e t ≤ _ by simpa only [e, B, a, hrep t ht] using hduh).trans hmono
  have hω : 0 ≤ ω := by positivity
  have h := le_exp_mul_integral_of_retarded_bound hT hω (Real.sqrt_nonneg _)
    he.continuousOn (hr.norm.const_mul c) (fun s _ ↦ mul_nonneg hc (norm_nonneg _)) hbound
  simpa only [intervalIntegral.integral_const_mul] using h

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
