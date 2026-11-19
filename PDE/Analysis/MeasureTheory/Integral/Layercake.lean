/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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

/-!
# Power layer cake and truncated tails

Mathlib's real-valued power layer-cake identity extends to measurable ENNReal
functions finite almost everywhere. Applying it under the measure with density
f expresses the p-th power integral using the first moments of the superlevels.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace MeasureTheory

/-- Power layer cake for an almost everywhere finite ENNReal function. -/
theorem lintegral_rpow_eq_lintegral_superlevel {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) (hfin : ∀ᵐ x ∂μ, f x < ⊤)
    {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, f x ^ p ∂μ) = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
      μ {x | ENNReal.ofReal t < f x} * ENNReal.ofReal (t ^ (p - 1)) := by
  have hlayer := MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul μ
    (f := fun x ↦ (f x).toReal) (Filter.Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)
    hf.ennreal_toReal.aemeasurable hp
  have hleft : (∫⁻ x, f x ^ p ∂μ) = ∫⁻ x, ENNReal.ofReal ((f x).toReal ^ p) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfin] with x hx
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le,
      ENNReal.ofReal_toReal hx.ne]
  rw [hleft, hlayer]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  congr 1
  apply measure_congr
  filter_upwards [hfin] with x hx
  simp only [ENNReal.ofReal_lt_iff_lt_toReal ht.le hx.ne]

/-- Power layer cake under the measure with density f gives the integral of its truncated tails. -/
theorem lintegral_rpow_eq_lintegral_truncated {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) (hfin : ∀ᵐ x ∂μ, f x < ⊤)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x, f x ^ p ∂μ) = ENNReal.ofReal (p - 1) * ∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x in {x | ENNReal.ofReal t < f x}, f x ∂μ) *
        ENNReal.ofReal (t ^ (p - 2)) := by
  have hfin' : ∀ᵐ x ∂μ.withDensity f, f x < ⊤ :=
    (withDensity_absolutelyContinuous μ f).ae_le hfin
  have hlayer := lintegral_rpow_eq_lintegral_superlevel (μ.withDensity f) hf hfin'
    (sub_pos.mpr hp)
  rw [lintegral_withDensity_eq_lintegral_mul μ hf (hf.pow_const (p - 1))] at hlayer
  have hpow (x : α) : f x * f x ^ (p - 1) = f x ^ p := by
    calc
      _ = f x ^ (1 : ℝ) * f x ^ (p - 1) := by rw [ENNReal.rpow_one]
      _ = f x ^ (1 + (p - 1)) :=
        (ENNReal.rpow_add_of_nonneg 1 (p - 1) (by norm_num) (sub_nonneg.mpr hp.le)).symm
      _ = _ := by congr 1; ring
  simp_rw [Pi.mul_apply, hpow,
    withDensity_apply f (measurableSet_lt measurable_const hf)] at hlayer
  have heq : p - 1 - 1 = p - 2 := by ring
  simpa only [heq] using hlayer

end MeasureTheory
