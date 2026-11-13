/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Kernel.Integrability
public import PDE.Parabolic.Heat.MeanValue.ChangeOfVariables
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import PDE.Analysis.MeasureTheory.SpaceTime
import CAS.ExactTactic

/-!
# Normalization of Watson's heat-ball weight

For positive spatial dimension, Watson's weight has the exact mass

`∫_{E(x,t;r)} |x-y|² / (t-s)² dy ds = 4 rⁿ`.

Evans uses this value at the end of the proof of Theorem 3 in §2.3.2 and omits the
computation, so we carry it out. Writing the backward time lag as `τ > 0` and substituting
`y = √τ z` turns the strict heat-ball condition into

`0 < τ < Γ(z,1)^(2/n)`.

The interval is open because LeanPDE defines heat balls by the strict
superlevel condition `Γ > r⁻ⁿ`.  Integrating first in `τ` gives
`(2/n) ‖z‖² Γ(z,1)`; the time-one Gaussian second moment
`integral_norm_sq_mul_fundamentalSolutionHeat_one` then gives the constant `4`.
Parabolic change of variables supplies the factor `rⁿ`
for a general pole and radius.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, last step of the proof of Theorem 3, where the
  value 4 is stated and the computation omitted.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime time)

noncomputable section

namespace HeatEquation

open PDE.Common
open MeasureTheory

variable {n : ℕ}

/-- The upper endpoint of the transformed backward-time interval. -/
private def watsonTimeCap (n : ℕ) (z : ℝ^n) : ℝ :=
  fundamentalSolutionHeat (n := n) z 1 ^ (2 / (n : ℝ))

/-- The strict product region obtained from the unit heat ball by
`(τ,z) ↦ (-τ, √τ z)`. -/
private def watsonProductRegion (n : ℕ) : Set (ℝ × ℝ^n) :=
  {q | q.1 ∈ Set.Ioo 0 (watsonTimeCap n q.2)}

/-- The unit heat-ball weight after the square-root spatial substitution,
including its spatial Jacobian. -/
private def watsonProductIntegrand (n : ℕ) (q : ℝ × ℝ^n) : ℝ :=
  (watsonProductRegion n).indicator
    (fun q ↦ ‖q.2‖ ^ 2 * q.1 ^ ((n : ℝ) / 2 - 1)) q

/-- The unit heat-ball weight in backward-time product coordinates. -/
private def unitHeatBallLagIntegrand (n : ℕ) (q : ℝ × ℝ^n) : ℝ :=
  (heatBall (0 : ℝ^n) 0 1).indicator
    (heatBallWeight (0 : ℝ^n) 0)
    (timeSpaceCons (-q.1) q.2)

private theorem continuous_fundamentalSolutionHeat_one :
    Continuous (fun z : ℝ^n ↦ fundamentalSolutionHeat (n := n) z 1) := by
  simp only [fundamentalSolutionHeat,
    show ¬(1 : ℝ) ≤ 0 by norm_num, ite_false]
  fun_prop

private theorem continuous_watsonTimeCap :
    Continuous (watsonTimeCap n) := by
  unfold watsonTimeCap
  exact continuous_fundamentalSolutionHeat_one.rpow_const fun z ↦
    Or.inl (fundamentalSolutionHeat_pos (n := n) z 1 (by norm_num)).ne'

private theorem watsonTimeCap_pos (z : ℝ^n) :
    0 < watsonTimeCap n z := by
  unfold watsonTimeCap
  exact Real.rpow_pos_of_pos
    (fundamentalSolutionHeat_pos (n := n) z 1 (by norm_num)) _

private theorem measurableSet_watsonProductRegion :
    MeasurableSet (watsonProductRegion n) := by
  unfold watsonProductRegion
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst
      (continuous_watsonTimeCap.measurable.comp measurable_snd))

private theorem measurable_watsonProductIntegrand :
    Measurable (watsonProductIntegrand n) := by
  unfold watsonProductIntegrand
  apply Measurable.indicator _ measurableSet_watsonProductRegion
  fun_prop

private theorem measurable_timeSpaceCons_neg :
    Measurable
      (fun q : ℝ × ℝ^n ↦ timeSpaceCons (-q.1) q.2) := by
  change Measurable
    (fun q : ℝ × ℝ^n ↦
      (timeSpaceContinuousLinearEquiv n).symm (-q.1, q.2))
  exact (timeSpaceContinuousLinearEquiv n).symm.continuous.measurable.comp
    (measurable_fst.neg.prodMk measurable_snd)

private theorem measurable_unitHeatBallLagIntegrand :
    Measurable (unitHeatBallLagIntegrand n) := by
  unfold unitHeatBallLagIntegrand
  apply Measurable.indicator
  · exact (measurable_heatBallWeight (n := n) (0 : ℝ^n) 0).comp
      measurable_timeSpaceCons_neg
  · exact (measurableSet_heatBall (n := n) (0 : ℝ^n) 0 1).preimage
      measurable_timeSpaceCons_neg

private theorem watsonProductIntegrand_nonneg (q : ℝ × ℝ^n) :
    0 ≤ watsonProductIntegrand n q := by
  by_cases hq : q ∈ watsonProductRegion n
  · rw [watsonProductIntegrand, Set.indicator_of_mem hq]
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hq.1.le _)
  · simp [watsonProductIntegrand, hq]

private theorem unitHeatBallLagIntegrand_nonneg (q : ℝ × ℝ^n) :
    0 ≤ unitHeatBallLagIntegrand n q := by
  by_cases hq :
      timeSpaceCons (-q.1) q.2 ∈ heatBall (0 : ℝ^n) 0 1
  · rw [unitHeatBallLagIntegrand, Set.indicator_of_mem hq]
    exact heatBallWeight_nonneg _ _ _
  · simp [unitHeatBallLagIntegrand, hq]

private theorem integral_watson_time_slice
    (hn : 0 < n) (z : ℝ^n) :
    (∫ τ : ℝ, watsonProductIntegrand n (τ, z)) =
      (2 / (n : ℝ)) *
        (‖z‖ ^ 2 * fundamentalSolutionHeat (n := n) z 1) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc := watsonTimeCap_pos (n := n) z
  have hslice : (fun τ : ℝ ↦ watsonProductIntegrand n (τ, z)) =
      (Set.Ioo 0 (watsonTimeCap n z)).indicator fun τ ↦ ‖z‖ ^ 2 * τ ^ ((n : ℝ) / 2 - 1) := rfl
  rw [hslice, integral_indicator measurableSet_Ioo, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc.le,
    integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.zero_rpow (by positivity),
    watsonTimeCap, ← Real.rpow_mul (fundamentalSolutionHeat_pos (n := n) z 1 one_pos).le,
    show 2 / (n : ℝ) * ((n : ℝ) / 2) = 1 by field_simp, Real.rpow_one]
  field_simp
  ring

private theorem integrable_watson_time_slice
    (hn : 0 < n) (z : ℝ^n) :
    Integrable (fun τ : ℝ ↦ watsonProductIntegrand n (τ, z)) := by
  by_cases hz : z = 0
  · subst z
    have hzero :
        (fun τ : ℝ ↦ watsonProductIntegrand n (τ, (0 : ℝ^n))) = 0 := by
      funext τ
      simp [watsonProductIntegrand]
    rw [hzero]
    exact integrable_zero _ _ _
  · apply Integrable.of_integral_ne_zero
    rw [integral_watson_time_slice hn z]
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast hn
    have hnorm : 0 < ‖z‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hz)
    have hkernel :
        0 < fundamentalSolutionHeat (n := n) z 1 :=
      fundamentalSolutionHeat_pos (n := n) z 1 (by norm_num)
    positivity

private theorem integral_norm_watson_time_slice
    (hn : 0 < n) (z : ℝ^n) :
    (∫ τ : ℝ, ‖watsonProductIntegrand n (τ, z)‖) =
      (2 / (n : ℝ)) *
        (‖z‖ ^ 2 * fundamentalSolutionHeat (n := n) z 1) := by
  calc
    (∫ τ : ℝ, ‖watsonProductIntegrand n (τ, z)‖) =
        ∫ τ : ℝ, watsonProductIntegrand n (τ, z) := by
      apply integral_congr_ae
      filter_upwards [] with τ
      rw [Real.norm_eq_abs,
        abs_of_nonneg (watsonProductIntegrand_nonneg (n := n) (τ, z))]
    _ = (2 / (n : ℝ)) *
        (‖z‖ ^ 2 * fundamentalSolutionHeat (n := n) z 1) :=
      integral_watson_time_slice hn z

private theorem integrable_watson_outer (hn : 0 < n) :
    Integrable
      (fun z : ℝ^n ↦
        ∫ τ : ℝ, ‖watsonProductIntegrand n (τ, z)‖) := by
  have hmoment :
      Integrable
        (fun z : ℝ^n ↦
          ‖z‖ ^ 2 * fundamentalSolutionHeat (n := n) z 1) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_norm_sq_mul_fundamentalSolutionHeat_one]
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast hn
    positivity
  refine (hmoment.const_mul (2 / (n : ℝ))).congr ?_
  filter_upwards [] with z
  exact (integral_norm_watson_time_slice hn z).symm

private theorem integrable_watsonProductIntegrand (hn : 0 < n) :
    Integrable (watsonProductIntegrand n)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ^n))) := by
  apply (integrable_prod_iff'
    measurable_watsonProductIntegrand.aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall (integrable_watson_time_slice hn),
    integrable_watson_outer hn⟩

private theorem integral_watsonProductIntegrand (hn : 0 < n) :
    (∫ q : ℝ × ℝ^n, watsonProductIntegrand n q) = 4 := by
  have hF := integrable_watsonProductIntegrand (n := n) hn
  rw [Measure.volume_eq_prod ℝ (ℝ^n),
    integral_prod_symm _ hF]
  calc
    (∫ z : ℝ^n, ∫ τ : ℝ, watsonProductIntegrand n (τ, z)) =
        ∫ z : ℝ^n,
          (2 / (n : ℝ)) *
            (‖z‖ ^ 2 * fundamentalSolutionHeat (n := n) z 1) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact integral_watson_time_slice hn z
    _ = (2 / (n : ℝ)) *
        ∫ z : ℝ^n,
          ‖z‖ ^ 2 * fundamentalSolutionHeat (n := n) z 1 := by
      rw [integral_const_mul]
    _ = 4 := by
      rw [integral_norm_sq_mul_fundamentalSolutionHeat_one]
      have hnR : (n : ℝ) ≠ 0 := by
        exact_mod_cast hn.ne'
      field_simp [hnR]
      ring

private theorem sqrt_pow_eq_rpow_half
    {τ : ℝ} (hτ : 0 < τ) :
    Real.sqrt τ ^ n = τ ^ ((n : ℝ) / 2) := by
  cas

private theorem unit_heatBall_sqrt_slice_mem_iff
    (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (z : ℝ^n) :
    timeSpaceCons (-τ) (Real.sqrt τ • z) ∈
        heatBall (0 : ℝ^n) 0 1 ↔
      τ < watsonTimeCap n z := by
  let a : ℝ := Real.sqrt τ
  let γ : ℝ := fundamentalSolutionHeat (n := n) z 1
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ha : 0 < a := Real.sqrt_pos.2 hτ
  have haSq : a ^ 2 = τ := Real.sq_sqrt hτ.le
  have hγ : 0 < γ := fundamentalSolutionHeat_pos (n := n) z 1 one_pos
  have hscale : fundamentalSolutionHeat (n := n) (-(a • z)) τ = a ^ (-(n : ℝ)) * γ := by
    have hγneg : fundamentalSolutionHeat (n := n) (-z) 1 = γ := by
      simp [γ, fundamentalSolutionHeat]
    simpa [haSq, smul_neg, hγneg] using
      fundamentalSolutionHeat_scaling (n := n) (-z) 1 a (by norm_num) ha
  have hthreshold : timeSpaceCons (-τ) (a • z) ∈ heatBall (0 : ℝ^n) 0 1 ↔ a ^ n < γ := by
    rw [mem_heatBall_iff]
    simp only [spatialPart_timeSpaceCons, time, timeSpaceCons_zero,
      one_pow, inv_one, shiftedFundamentalSolutionHeat, zero_sub,
      sub_neg_eq_add, zero_add]
    rw [hscale, Real.rpow_neg ha.le, Real.rpow_natCast]
    simpa [div_eq_mul_inv, mul_comm] using
      (lt_div_iff₀ (pow_pos ha n) : (1 : ℝ) < γ / a ^ n ↔ 1 * a ^ n < γ)
  rw [show Real.sqrt τ = a by rfl, hthreshold]
  constructor
  · intro h
    have hleft : (a ^ n : ℝ) ^ (2 / (n : ℝ)) = τ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le,
        show (n : ℝ) * (2 / (n : ℝ)) = 2 by field_simp, Real.rpow_two, haSq]
    simpa [watsonTimeCap, γ, hleft] using
      Real.rpow_lt_rpow (pow_nonneg ha.le n) h (show 0 < 2 / (n : ℝ) by positivity)
  · intro h
    have hleft : τ ^ ((n : ℝ) / 2) = a ^ n := (sqrt_pow_eq_rpow_half (n := n) hτ).symm
    have hright : watsonTimeCap n z ^ ((n : ℝ) / 2) = γ := by
      rw [watsonTimeCap, ← Real.rpow_mul hγ.le,
        show 2 / (n : ℝ) * ((n : ℝ) / 2) = 1 by field_simp, Real.rpow_one]
    simpa [hleft, hright] using
      Real.rpow_lt_rpow hτ.le h (show 0 < (n : ℝ) / 2 by positivity)

private theorem unit_heatBall_weight_sqrt_slice
    {τ : ℝ} (hτ : 0 < τ) (z : ℝ^n) :
    Real.sqrt τ ^ n *
        heatBallWeight (0 : ℝ^n) 0
          (timeSpaceCons (-τ) (Real.sqrt τ • z)) =
      ‖z‖ ^ 2 * τ ^ ((n : ℝ) / 2 - 1) := by
  have hsqrt : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
  have hsqrtSq : Real.sqrt τ ^ 2 = τ :=
    Real.sq_sqrt hτ.le
  have hnorm :
      ‖Real.sqrt τ • z‖ ^ 2 = τ * ‖z‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt]
    nlinarith
  have hweight :
      heatBallWeight (0 : ℝ^n) 0
          (timeSpaceCons (-τ) (Real.sqrt τ • z)) =
        ‖z‖ ^ 2 / τ := by
    unfold heatBallWeight
    simp only [spatialPart_timeSpaceCons, time, timeSpaceCons_zero,
      zero_sub, sub_neg_eq_add, zero_add, norm_neg]
    rw [hnorm]
    field_simp [hτ.ne']
  rw [hweight, sqrt_pow_eq_rpow_half (n := n) hτ,
    Real.rpow_sub_one hτ.ne']
  field_simp [hτ.ne']

private theorem watsonProductIntegrand_eq_scaled_lag
    (hn : 0 < n) {τ : ℝ} (hτ : 0 < τ) (z : ℝ^n) :
    watsonProductIntegrand n (τ, z) =
      Real.sqrt τ ^ n *
        unitHeatBallLagIntegrand n (τ, Real.sqrt τ • z) := by
  have hmem :=
    unit_heatBall_sqrt_slice_mem_iff (n := n) hn hτ z
  by_cases hz : τ < watsonTimeCap n z
  · have hball := hmem.2 hz
    rw [watsonProductIntegrand, Set.indicator_of_mem,
      unitHeatBallLagIntegrand, Set.indicator_of_mem hball]
    · exact (unit_heatBall_weight_sqrt_slice (n := n) hτ z).symm
    · exact ⟨hτ, hz⟩
  · have hball : timeSpaceCons (-τ) (Real.sqrt τ • z) ∉
        heatBall (0 : ℝ^n) 0 1 := by
      exact fun h ↦ hz (hmem.1 h)
    simp [watsonProductIntegrand, watsonProductRegion,
      unitHeatBallLagIntegrand, hτ, hz, hball]

/-- At a nonpositive lag the unit heat ball has an empty slice, so the lag integrand vanishes. -/
private theorem unitHeatBallLagIntegrand_slice_eq_zero {τ : ℝ} (hτ : ¬0 < τ) :
    (fun y : ℝ^n ↦ unitHeatBallLagIntegrand n (τ, y)) = 0 := by
  funext y
  have hnot : timeSpaceCons (-τ) y ∉ heatBall (0 : ℝ^n) 0 1 := fun hy ↦ by
    have htime := time_lt_of_mem_heatBall (n := n) (x := (0 : ℝ^n)) (t := 0) (r := 1)
      zero_lt_one hy
    simp only [time, timeSpaceCons_zero] at htime
    linarith
  simp [unitHeatBallLagIntegrand, hnot]

private theorem integral_unitHeatBallLag_slice_eq_watson
    (hn : 0 < n) (τ : ℝ) :
    (∫ y : ℝ^n, unitHeatBallLagIntegrand n (τ, y)) =
      ∫ z : ℝ^n, watsonProductIntegrand n (τ, z) := by
  by_cases hτ : 0 < τ
  · have ha : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
    have hscale : (∫ z : ℝ^n, unitHeatBallLagIntegrand n (τ, Real.sqrt τ • z)) =
        (Real.sqrt τ ^ n)⁻¹ * ∫ y : ℝ^n, unitHeatBallLagIntegrand n (τ, y) := by
      simpa [abs_inv, abs_pow, smul_eq_mul, abs_of_pos ha] using
        Measure.integral_comp_smul (μ := (volume : Measure (ℝ^n)))
          (fun y ↦ unitHeatBallLagIntegrand n (τ, y)) (Real.sqrt τ)
    rw [integral_congr_ae (ae_of_all _ fun z ↦ watsonProductIntegrand_eq_scaled_lag hn hτ z),
      integral_const_mul, hscale, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), one_mul]
  · rw [unitHeatBallLagIntegrand_slice_eq_zero hτ,
      show (fun z : ℝ^n ↦ watsonProductIntegrand n (τ, z)) = 0 from funext fun z ↦ by
        simp [watsonProductIntegrand, watsonProductRegion, hτ]]

private theorem integral_norm_unitHeatBallLag_slice_eq_watson
    (hn : 0 < n) (τ : ℝ) :
    (∫ y : ℝ^n, ‖unitHeatBallLagIntegrand n (τ, y)‖) =
      ∫ z : ℝ^n, ‖watsonProductIntegrand n (τ, z)‖ := by
  calc
    (∫ y : ℝ^n, ‖unitHeatBallLagIntegrand n (τ, y)‖) =
        ∫ y : ℝ^n, unitHeatBallLagIntegrand n (τ, y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (unitHeatBallLagIntegrand_nonneg (n := n) (τ, y))]
    _ = ∫ z : ℝ^n, watsonProductIntegrand n (τ, z) :=
      integral_unitHeatBallLag_slice_eq_watson hn τ
    _ = ∫ z : ℝ^n, ‖watsonProductIntegrand n (τ, z)‖ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [Real.norm_eq_abs,
        abs_of_nonneg (watsonProductIntegrand_nonneg (n := n) (τ, z))]

private theorem integrable_unitHeatBallLag_slice_of_watson
    (hn : 0 < n) {τ : ℝ}
    (hF : Integrable (fun z : ℝ^n ↦
      watsonProductIntegrand n (τ, z))) :
    Integrable (fun y : ℝ^n ↦
      unitHeatBallLagIntegrand n (τ, y)) := by
  by_cases hτ : 0 < τ
  · have ha : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
    refine (integrable_comp_smul_iff (volume : Measure (ℝ^n))
      (fun y ↦ unitHeatBallLagIntegrand n (τ, y)) ha.ne').1
      ((hF.const_mul (Real.sqrt τ ^ n)⁻¹).congr (ae_of_all _ fun z ↦ ?_))
    dsimp only
    rw [watsonProductIntegrand_eq_scaled_lag hn hτ z]
    field_simp [pow_ne_zero n ha.ne']
  · rw [unitHeatBallLagIntegrand_slice_eq_zero hτ]
    exact integrable_zero _ _ _

private theorem integrable_unitHeatBallLagIntegrand (hn : 0 < n) :
    Integrable (unitHeatBallLagIntegrand n)
      ((volume : Measure ℝ).prod (volume : Measure (ℝ^n))) := by
  have hF := integrable_watsonProductIntegrand (n := n) hn
  apply (integrable_prod_iff
    measurable_unitHeatBallLagIntegrand.aestronglyMeasurable).2
  constructor
  · filter_upwards [hF.prod_right_ae] with τ hFτ
    exact integrable_unitHeatBallLag_slice_of_watson hn hFτ
  · refine hF.integral_norm_prod_left.congr ?_
    filter_upwards [] with τ
    exact (integral_norm_unitHeatBallLag_slice_eq_watson hn τ).symm

private theorem setIntegral_heatBallWeight_unit (hn : 0 < n) :
    (∫ p in heatBall (0 : ℝ^n) 0 1,
      heatBallWeight (0 : ℝ^n) 0 p) = 4 := by
  let A := timeSpaceContinuousLinearEquiv n
  let G : SpaceTime n → ℝ := (heatBall (0 : ℝ^n) 0 1).indicator (heatBallWeight (0 : ℝ^n) 0)
  have hA : MeasurePreserving (A : SpaceTime n → ℝ × ℝ^n) volume volume := by
    simpa [A] using (PDE.Common.measurePreserving_timeSpaceContinuousLinearEquiv (n := n))
  let N : (ℝ × ℝ^n) ≃ᵐ (ℝ × ℝ^n) := MeasurableEquiv.prodCongr
    (LinearIsometryEquiv.neg ℝ).toMeasurableEquiv (MeasurableEquiv.refl (ℝ^n))
  have hN : MeasurePreserving N ((volume : Measure ℝ).prod (volume : Measure (ℝ^n)))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ^n))) :=
    (LinearIsometryEquiv.measurePreserving (LinearIsometryEquiv.neg ℝ)).prod
      (MeasurePreserving.id volume)
  calc (∫ p in heatBall (0 : ℝ^n) 0 1, heatBallWeight (0 : ℝ^n) 0 p)
      = ∫ q : ℝ × ℝ^n, G (A.symm q) := by
        rw [← integral_indicator (measurableSet_heatBall (n := n) (0 : ℝ^n) 0 1)]
        exact ((hA.symm A.toHomeomorph.toMeasurableEquiv).integral_comp
          A.symm.toHomeomorph.measurableEmbedding G).symm
    _ = ∫ q : ℝ × ℝ^n, unitHeatBallLagIntegrand n q := by
        rw [Measure.volume_eq_prod ℝ (ℝ^n),
          ← hN.integral_comp N.measurableEmbedding (fun q : ℝ × ℝ^n ↦ G (A.symm q))]
        refine integral_congr_ae (ae_of_all _ fun q ↦ ?_)
        simp [N, A, G, unitHeatBallLagIntegrand, MeasurableEquiv.prodCongr,
          Equiv.prodCongr_apply]
    _ = ∫ τ : ℝ, ∫ z : ℝ^n, watsonProductIntegrand n (τ, z) := by
        rw [Measure.volume_eq_prod ℝ (ℝ^n),
          integral_prod _ (integrable_unitHeatBallLagIntegrand (n := n) hn)]
        exact integral_congr_ae (ae_of_all _ (integral_unitHeatBallLag_slice_eq_watson hn))
    _ = 4 := by
        rw [← integral_watsonProductIntegrand hn, Measure.volume_eq_prod ℝ (ℝ^n)]
        exact (integral_prod _ (integrable_watsonProductIntegrand (n := n) hn)).symm

/-- Watson's heat-ball weight has exact mass `4 rⁿ`, the normalization in
Evans's heat-ball mean-value formula. -/
theorem setIntegral_heatBallWeight
    (hn : 0 < n) (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ p in heatBall x t r, heatBallWeight x t p) =
      4 * r ^ n := by
  have hscale :=
    heatBallWeighted_setIntegral_scaling
      (n := n) (u := fun _ ↦ 1) x t hr
  calc
    (∫ p in heatBall x t r, heatBallWeight x t p) =
        r ^ n *
          ∫ p in heatBall (0 : ℝ^n) 0 1,
            heatBallWeight (0 : ℝ^n) 0 p := by
      simpa using hscale
    _ = 4 * r ^ n := by
      rw [setIntegral_heatBallWeight_unit hn]
      ring

/-- Watson's weight is integrable on every positive-radius heat ball in
positive spatial dimension. -/
theorem integrableOn_heatBallWeight
    (hn : 0 < n) (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (heatBallWeight x t) (heatBall x t r) := by
  apply Integrable.of_integral_ne_zero
  rw [setIntegral_heatBallWeight hn x t hr]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hr.ne')

end HeatEquation
