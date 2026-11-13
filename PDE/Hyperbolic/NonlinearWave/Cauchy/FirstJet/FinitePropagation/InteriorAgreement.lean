/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.WeightedStability
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.ExponentialWeight
public import PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet.FinitePropagation.LocalEnergy
import CAS.ExactTactic

/-!
# Interior agreement for first-jet energy solutions

If the initial energy difference vanishes on a sufficiently large ball,
weighted stability forces the difference to vanish on the inner ball for a
prescribed finite time. Exponential localization and a limit of its parameter
avoid any smoothness assumption on the reaction or the solution. The speed bound is sufficient for
local-data patching.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet

open SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {f : (ℝ^n × ℝ × ℝ) → ℝ} {L : NNReal}
variable {hf : LipschitzWith L f} {hf0 : f 0 = 0}

/-- Vanishing initial energy on the outer ball forces vanishing energy on the
inner ball as long as the relative-gradient travel bound is less than one. -/
theorem IsEnergySolution.energyDensity_sub_eq_zero_on_ball {x y : H¹(ℝ^n) × DerivLp n 2 univ}
    {u v : C(ℝ, H¹(ℝ^n) × DerivLp n 2 univ)} (hu : IsEnergySolution hf hf0 x u)
    (hv : IsEnergySolution hf hf0 y v) {C R T : ℝ} (hC : 0 ≤ C) (hR : 0 < R) (hT : 0 ≤ T)
    (hgrad : ∀ (i : Fin n) (z : ℝ^n), |(∂[i] (SobolevSpace.Approximation.cutoff R)) z| ≤ C / R)
    (hspeed : (n : ℝ) * (C / R) * T < 1)
    (hinit : ∀ᵐ z ∂(domainMeasure n univ).restrict (Metric.closedBall 0 (2 * R)),
      energyDensity (x - y) z = 0) :
    ∀ᵐ z ∂(domainMeasure n univ).restrict (Metric.closedBall 0 R),
      energyDensity (u T - v T) z = 0 := by
  let E := ∫ z in Metric.closedBall 0 R, energyDensity (u T - v T) z ∂domainMeasure n univ
  let E₀ := ∫ z, energyDensity (x - y) z ∂domainMeasure n univ
  let A := (2 + (L : ℝ) ^ 2) * T
  let b := (n : ℝ) * (C / R) * T - 1
  have hbound (σ : ℝ) (hσ : 0 ≤ σ) : E ≤ (E₀ * Real.exp A) * Real.exp (σ * b) := by
    obtain ⟨χ, hbase, ha, hd⟩ := exists_exponentialCutoff_multiplier hC hR hσ hgrad
    let a := (χ : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
    have hone : ∀ᵐ z ∂(domainMeasure n univ).restrict (Metric.closedBall 0 R), a z = 1 := by
      filter_upwards [hbase.restrict, ae_restrict_mem Metric.isClosed_closedBall.measurableSet]
        with z hz hzR
      exact hz.trans (exponentialCutoff_eq_one hR σ hzR)
    have hstart : weightedEnergyForm a (x - y) (x - y) = Real.exp (-σ) * E₀ := by
      apply weightedEnergyForm_eq_mul_integral_of_vanishing (x - y) a
        Metric.isClosed_closedBall.measurableSet hinit
      filter_upwards [hbase] with z hz hout using hz.trans (exponentialCutoff_eq_exp_neg hR σ hout)
    have hE := (setIntegral_energyDensity_le_weightedEnergyForm (u T - v T) a ha hone).trans
      (hu.weighted_sub_le_exp hv χ (mul_nonneg hσ (div_nonneg hC hR.le)) ha hd hT)
    dsimp only at hE
    rw [hstart] at hE
    refine hE.trans_eq ?_
    have he : -σ + (2 + (L : ℝ) ^ 2 + (n : ℝ) * (σ * (C / R))) * T = A + σ * b := by
      dsimp only [A, b]
      cas using hR.ne'
    calc
      Real.exp (-σ) * E₀ * Real.exp ((2 + (L : ℝ) ^ 2 + (n : ℝ) * (σ * (C / R))) * T) =
          E₀ * (Real.exp (-σ) *
            Real.exp ((2 + (L : ℝ) ^ 2 + (n : ℝ) * (σ * (C / R))) * T)) := by ac_rfl
      _ = E₀ * Real.exp (A + σ * b) := by rw [← Real.exp_add, he]
      _ = (E₀ * Real.exp A) * Real.exp (σ * b) := by rw [Real.exp_add, mul_assoc]
  have hb : b < 0 := sub_neg.mpr hspeed
  have hlim : Tendsto (fun σ : ℝ ↦ (E₀ * Real.exp A) * Real.exp (σ * b)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, mul_zero] using
      (Real.tendsto_exp_atBot.comp (Tendsto.atTop_mul_const_of_neg hb tendsto_id)).const_mul
        (E₀ * Real.exp A)
  have hE : E ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    ((eventually_ge_atTop (0 : ℝ)).mono hbound)
  have hzero : E = 0 := le_antisymm hE (integral_nonneg fun z ↦ energyDensity_nonneg (u T - v T) z)
  exact (integral_eq_zero_iff_of_nonneg (fun z ↦ energyDensity_nonneg (u T - v T) z)
    (integrable_energyDensity (u T - v T)).integrableOn).mp hzero

end PDE.Hyperbolic.NonlinearWave.Cauchy.FirstJet
