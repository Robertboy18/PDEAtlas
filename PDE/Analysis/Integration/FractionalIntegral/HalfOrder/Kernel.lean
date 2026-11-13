/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import CAS.ExactTactic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

/-!
# The half-order fractional integral on the real line

Layer cake turns the kernel |x-y|^(-1/2) into interval integrals with radii t^(-2).
The singular point has zero measure, including under the measure with density f.
The kernel, interval Hölder bound and exact near/far power integrals require no
integrability assumption on the measurable nonnegative input.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace MeasureTheory

/-- The half-order fractional integral on the real line, with kernel |x-y|^(-1/2). -/
noncomputable def fractionalIntegralHalf (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (dist y x ^ (-1 / 2 : ℝ)) * f y

/-- Layer cake turns the half-order fractional kernel into integrals over actual intervals. -/
theorem fractionalIntegralHalf_eq_lintegral_ball {f : ℝ → ℝ≥0∞} (hf : Measurable f) (x : ℝ) :
    fractionalIntegralHalf f x = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ y in ball x (t ^ (-2 : ℝ)), f y := by
  have hk : Measurable (fun y : ℝ ↦ dist y x ^ (-1 / 2 : ℝ)) := by fun_prop
  have hnonneg : ∀ y : ℝ, 0 ≤ dist y x ^ (-1 / 2 : ℝ) :=
    fun y ↦ Real.rpow_nonneg dist_nonneg _
  have hlayer := lintegral_eq_lintegral_meas_lt (volume.withDensity f)
    (Filter.Eventually.of_forall hnonneg) hk.aemeasurable
  rw [lintegral_withDensity_eq_lintegral_mul volume hf hk.ennreal_ofReal] at hlayer
  have hnull : ∀ᵐ y ∂volume.withDensity f, y ≠ x := by
    apply (withDensity_absolutelyContinuous volume f).ae_le
    exact volume.ae_ne x
  have hlevel (t : ℝ) (ht : 0 < t) :
      (volume.withDensity f) {y | t < dist y x ^ (-1 / 2 : ℝ)} =
        ∫⁻ y in ball x (t ^ (-2 : ℝ)), f y := by
    rw [← withDensity_apply f measurableSet_ball]
    apply measure_congr
    filter_upwards [hnull] with y hy
    have hdist : 0 < dist y x := dist_pos.mpr hy
    apply propext
    change (t < dist y x ^ (-1 / 2 : ℝ)) ↔ dist y x < t ^ (-2 : ℝ)
    convert Real.lt_rpow_inv_iff_of_neg ht hdist (by norm_num : (-2 : ℝ) < 0) using 2
    norm_num
  calc
    _ = ∫⁻ y, (f * fun y ↦ ENNReal.ofReal (dist y x ^ (-1 / 2 : ℝ))) y := by
      simp only [fractionalIntegralHalf, Pi.mul_apply, mul_comm]
    _ = _ := hlayer.trans (lintegral_congr_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hlevel t ht))

/-- Hölder bounds an interval integral using its length and the global L^(4/3) integral. -/
theorem lintegral_ball_le_volume_quarter_mul {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (x R : ℝ) :
    (∫⁻ y in ball x R, f y) ≤ volume (ball x R) ^ (1 / 4 : ℝ) *
      (∫⁻ y, f y ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) := by
  have hconj : (4 : ℝ).HolderConjugate (4 / 3) := by
    rw [Real.holderConjugate_iff]
    constructor <;> cas
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (ball x R)) hconj
    (f := fun _ : ℝ ↦ (1 : ℝ≥0∞)) (g := f) measurable_const.aemeasurable hf.aemeasurable
  norm_num only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const,
    one_mul, Measure.restrict_apply_univ, one_div_div] at hholder
  calc
    _ ≤ _ := hholder
    _ ≤ _ := by
      gcongr 2
      exact setLIntegral_le_lintegral _ _

/-- The locally integrable inverse square-root kernel has integral 2√R on (0,R]. -/
theorem lintegral_Ioc_neg_half {R : ℝ} (hR : 0 ≤ R) :
    (∫⁻ t in Ioc (0 : ℝ) R, ENNReal.ofReal (t ^ (-1 / 2 : ℝ))) =
      ENNReal.ofReal (2 * R ^ (1 / 2 : ℝ)) := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ t ^ (-1 / 2 : ℝ)) volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  rw [← ofReal_integral_eq_lintegral_ofReal hint.1]
  · rw [← intervalIntegral.integral_of_le hR, integral_rpow (Or.inl (by norm_num))]
    congr 1
    norm_num
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _

/-- The inverse-square kernel has tail integral 1/R on (R,∞). -/
theorem lintegral_Ioi_neg_two {R : ℝ} (hR : 0 < R) :
    (∫⁻ t in Ioi R, ENNReal.ofReal (t ^ (-2 : ℝ))) = ENNReal.ofReal R⁻¹ := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR)]
  · rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR]
    congr 1
    norm_num
    exact Real.rpow_neg_one R
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hR.trans ht).le _

/-- The fractional integral is measurable by parameter integration of its measurable kernel. -/
theorem measurable_fractionalIntegralHalf {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fractionalIntegralHalf f) := by
  have hk : Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal (dist p.2 p.1 ^ (-1 / 2 : ℝ)) * f p.2) := by fun_prop
  exact hk.lintegral_prod_right'

end MeasureTheory
