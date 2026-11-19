/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedRetarded
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.ExponentialWeight
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalEnergy
import CAS.ExactTactic

/-!
# Interior agreement with exterior forcing

A locally integrable forcing error supported outside the outer ball cannot
change the solution in the inner ball before the relative-gradient travel
bound is reached. Exponential localization removes the exterior error without
assuming a time derivative or a continuous forcing.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution Hyperbolic.Variational

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}

local notation "C" => WaveEnergySpace.coordinates
  (H := DerivLp n 2 univ) (massForm n) (massForm_coercive n) massForm_symmetric

/-- A forced energy difference vanishes in the inner ball when its error is
supported beyond the outer ball and the initial linear terms agree. -/
theorem energyDensity_sub_eq_zero_on_ball_of_exterior_forcing (hf : LipschitzWith L f)
    (hf0 : f 0 = 0) (u v : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)) {F r : ℝ → DerivLp n 2 univ}
    {T R c : ℝ} (hT : 0 ≤ T) (hR : 0 < R) (hF : IntervalIntegrable F volume 0 T)
    (hr : IntervalIntegrable r volume 0 T)
    (hrep : ∀ t ∈ Icc 0 T, u t - v t =
      C ((linearSemigroup n).duhamel (fun s ↦ (C).symm (0, F s)) t))
    (herr : ∀ᵐ s ∂volume.restrict (Ioc 0 T), F s =
      (source hf hf0 (u s) - source hf hf0 (v s)) + r s)
    (hzero : ∀ᵐ s ∂volume.restrict (Ioc 0 T),
      ∀ᵐ y ∂(domainMeasure n univ).restrict (Metric.closedBall 0 (2 * R)), r s y = 0)
    (hc : 0 ≤ c)
    (hgrad : ∀ (i : Fin n) (z : ℝ^n), |(∂[i] (SobolevSpace.Approximation.cutoff R)) z| ≤ c / R)
    (hspeed : (n : ℝ) * (c / R) * T < 1) :
    ∀ᵐ y ∂(domainMeasure n univ).restrict (Metric.closedBall 0 R),
      energyDensity (u T - v T) y = 0 := by
  let E := ∫ y in Metric.closedBall 0 R, energyDensity (u T - v T) y ∂domainMeasure n univ
  let M := ∫ s in (0 : ℝ)..T, ‖r s‖
  let A := (3 / 2 + Real.sqrt (2 + 2 * (L : ℝ) ^ 2)) * T
  let b := ((n : ℝ) * (c / R) * T - 1) / 2
  have hbound (σ : ℝ) (hσ : 0 ≤ σ) :
      Real.sqrt E ≤ (M * Real.exp A) * Real.exp (σ * b) := by
    obtain ⟨χ, hbase, ha, hd⟩ := exists_exponentialCutoff_multiplier hc hR hσ hgrad
    let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
    have hone : ∀ᵐ y ∂(domainMeasure n univ).restrict (Metric.closedBall 0 R), a y = 1 := by
      filter_upwards [hbase.restrict, ae_restrict_mem Metric.isClosed_closedBall.measurableSet]
        with y hy hyR
      exact hy.trans (exponentialCutoff_eq_one hR σ hyR)
    have hout : ∀ᵐ y ∂domainMeasure n univ,
        y ∉ Metric.closedBall 0 (2 * R) → a y = Real.exp (-σ) := by
      filter_upwards [hbase] with y hy hnot using hy.trans (exponentialCutoff_eq_exp_neg hR σ hnot)
    have hsmall : ∀ᵐ s ∂volume.restrict (Ioc 0 T),
        Real.sqrt (weightedEnergyForm a (0, r s) (0, r s)) ≤
          Real.exp (-σ / 2) * ‖r s‖ := by
      filter_upwards [hzero] with s hs
      rw [sqrt_weightedEnergyForm_zero_pair_of_vanishing a (r s)
        Metric.isClosed_closedBall.measurableSet (Real.exp_pos _).le hs hout, ← Real.exp_half]
    have hE := (Real.sqrt_le_sqrt
      (setIntegral_energyDensity_le_weightedEnergyForm (u T - v T) a ha hone)).trans
      (sqrt_weightedEnergyForm_sub_le_of_forcing hf hf0 u v hT hF hr hrep herr χ
        (mul_nonneg hσ (div_nonneg hc hR.le)) ha hd (Real.exp_pos _).le hsmall T ⟨hT, le_rfl⟩)
    refine hE.trans_eq ?_
    have he : ((3 + (n : ℝ) * (σ * (c / R))) / 2 +
        Real.sqrt (2 + 2 * (L : ℝ) ^ 2)) * T + (-σ / 2) = A + σ * b := by
      dsimp only [A, b]
      cas using hR.ne'
    calc
      Real.exp (((3 + (n : ℝ) * (σ * (c / R))) / 2 +
          Real.sqrt (2 + 2 * (L : ℝ) ^ 2)) * T) * (Real.exp (-σ / 2) * M) =
          M * (Real.exp (((3 + (n : ℝ) * (σ * (c / R))) / 2 +
            Real.sqrt (2 + 2 * (L : ℝ) ^ 2)) * T) * Real.exp (-σ / 2)) := by ac_rfl
      _ = M * Real.exp (A + σ * b) := by rw [← Real.exp_add, he]
      _ = (M * Real.exp A) * Real.exp (σ * b) := by rw [Real.exp_add, mul_assoc]
  have hb : b < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hspeed) (by norm_num)
  have hlim : Tendsto (fun σ : ℝ ↦ (M * Real.exp A) * Real.exp (σ * b)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, mul_zero] using
      (Real.tendsto_exp_atBot.comp (Tendsto.atTop_mul_const_of_neg hb tendsto_id)).const_mul
        (M * Real.exp A)
  have hsqrt : Real.sqrt E ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    ((eventually_ge_atTop (0 : ℝ)).mono hbound)
  have hE : E = 0 := le_antisymm (Real.sqrt_eq_zero'.mp (le_antisymm hsqrt (Real.sqrt_nonneg _)))
    (integral_nonneg fun y ↦ energyDensity_nonneg (u T - v T) y)
  exact (integral_eq_zero_iff_of_nonneg (fun y ↦ energyDensity_nonneg (u T - v T) y)
    (integrable_energyDensity (u T - v T)).integrableOn).mp hE

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
