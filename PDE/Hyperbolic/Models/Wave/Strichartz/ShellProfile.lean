/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
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

/-!
# Differentiation of the integrated Newtonian shell profile

For positive time, the profile t/max(t,r) is bounded by one and locally Lipschitz
in time, uniformly in r. Its derivative is the exterior inverse-radius kernel
off r=t. The characteristic sphere is null, so dominated local Lipschitz
differentiation applies to every integrable spatial datum.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace WaveEquation.Strichartz

/-- On a positive half-line the shell profile is a clipped affine function. -/
theorem shell_profile_eq_min {a s : ℝ} (ha : 0 < a) (hs : a ≤ s) (r : ℝ) :
    s / max s r = min (s / max a r) 1 := by
  have hspos : 0 < s := ha.trans_le hs
  have hmax : 0 < max a r := ha.trans_le (le_max_left _ _)
  by_cases hrs : r ≤ s
  · rw [max_eq_left hrs, div_self hspos.ne', min_eq_right]
    exact (one_le_div hmax).mpr (max_le hs hrs)
  · have hsr : s ≤ r := (lt_of_not_ge hrs).le
    rw [max_eq_right hsr, max_eq_right (hs.trans hsr), min_eq_left]
    exact (div_le_one (hspos.trans_le hsr)).mpr hsr

/-- Away from zero time the shell profile is uniformly Lipschitz in the time parameter. -/
theorem lipschitzOnWith_shell_profile {a : ℝ} (ha : 0 < a) (r : ℝ) :
    LipschitzOnWith (Real.nnabs a⁻¹) (fun s ↦ s / max s r) (Ici a) := by
  have hmax : 0 < max a r := ha.trans_le (le_max_left _ _)
  have hlin : LipschitzWith (Real.nnabs (max a r)⁻¹) (fun s : ℝ ↦ s / max a r) := by
    refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    simp only [Real.dist_eq, Real.coe_nnabs, ← sub_div, abs_div, abs_inv]
    rw [div_eq_mul_inv, mul_comm]
  have hclip := hlin.min_const 1
  have hconst : Real.nnabs (max a r)⁻¹ ≤ Real.nnabs a⁻¹ := by
    rw [← NNReal.coe_le_coe, Real.coe_nnabs, Real.coe_nnabs,
      abs_of_pos (inv_pos.mpr hmax), abs_of_pos (inv_pos.mpr ha)]
    exact inv_anti₀ ha (le_max_left _ _)
  refine LipschitzOnWith.of_dist_le_mul fun s hs t ht ↦ ?_
  rw [shell_profile_eq_min ha hs r, shell_profile_eq_min ha ht r]
  exact (hclip.weaken hconst).dist_le_mul s t

/-- The profile derivative is the exterior inverse-radius kernel away from its moving corner. -/
theorem hasDerivAt_shell_profile {t r : ℝ} (ht : 0 < t) (hrt : r ≠ t) :
    HasDerivAt (fun s ↦ s / max s r) (if t < r then r⁻¹ else 0) t := by
  by_cases htr : t < r
  · rw [ite_eq_left htr]
    have heq : (fun s ↦ s / max s r) =ᶠ[nhds t] (fun s ↦ s / r) := by
      filter_upwards [isOpen_Iio.mem_nhds htr] with s hs
      rw [max_eq_right hs.le]
    simpa only [one_div] using ((hasDerivAt_id t).div_const r).congr_of_eventuallyEq heq
  · rw [ite_eq_right htr]
    have hrt' : r < t := lt_of_le_of_ne (le_of_not_gt htr) hrt
    have heq : (fun s ↦ s / max s r) =ᶠ[nhds t] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds ht, isOpen_Ioi.mem_nhds hrt'] with s hs hsr
      rw [max_eq_left hsr.le, div_self hs.ne']
    exact (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq

/-- A positive-time shell profile lies between zero and one. -/
theorem shell_profile_mem_Icc {t : ℝ} (ht : 0 < t) (r : ℝ) :
    t / max t r ∈ Icc (0 : ℝ) 1 := by
  have hmax := ht.trans_le (le_max_left t r)
  exact ⟨div_nonneg ht.le hmax.le, (div_le_one hmax).mpr (le_max_left _ _)⟩

/-- Differentiation of the integrated shell profile produces the exterior Newtonian convolution. -/
theorem hasDerivAt_integral_shell_profile {n : ℕ} {f : ℝ^n → ℝ}
    (hf : Integrable f) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ ∫ y, (s / max s ‖y‖) * f y)
      (∫ y, (if t < ‖y‖ then ‖y‖⁻¹ else 0) * f y) t := by
  let a := t / 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hat : a < t := by dsimp [a]; linarith
  have hmeas (s : ℝ) : AEStronglyMeasurable (fun y : ℝ^n ↦ (s / max s ‖y‖) * f y) := by
    apply AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact (measurable_const.div (measurable_const.max measurable_norm)).aestronglyMeasurable
  have hint : Integrable (fun y : ℝ^n ↦ (t / max t ‖y‖) * f y) := by
    apply hf.bdd_mul (c := 1)
      ((measurable_const.div (measurable_const.max measurable_norm)).aestronglyMeasurable)
    refine Filter.Eventually.of_forall fun y ↦ ?_
    change |t / max t ‖y‖| ≤ 1
    rw [abs_of_nonneg (shell_profile_mem_Icc ht ‖y‖).1]
    exact (shell_profile_mem_Icc ht ‖y‖).2
  have hDm : AEStronglyMeasurable
      (fun y : ℝ^n ↦ (if t < ‖y‖ then ‖y‖⁻¹ else 0) * f y) := by
    apply AEStronglyMeasurable.mul _ hf.aestronglyMeasurable
    exact (measurable_norm.inv.ite (measurableSet_lt measurable_const measurable_norm)
      measurable_const).aestronglyMeasurable
  have hlip : ∀ᵐ y : ℝ^n, LipschitzOnWith (Real.nnabs (a⁻¹ * ‖f y‖))
      (fun s ↦ (s / max s ‖y‖) * f y) (Ici a) := by
    refine Filter.Eventually.of_forall fun y ↦ ?_
    refine LipschitzOnWith.of_dist_le_mul fun s hs u hu ↦ ?_
    have hb := (lipschitzOnWith_shell_profile ha ‖y‖).dist_le_mul s hs u hu
    simp only [Real.dist_eq, Real.coe_nnabs, abs_of_pos (inv_pos.mpr ha)] at hb
    simp only [Real.dist_eq, ← sub_mul, abs_mul, Real.coe_nnabs,
      abs_of_pos (inv_pos.mpr ha), Real.norm_eq_abs, abs_abs]
    calc
      _ ≤ (a⁻¹ * |s - u|) * |f y| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
      _ = _ := by ring
  have hnull : ∀ᵐ y : ℝ^n, y ∉ Metric.sphere 0 t := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using
      Measure.addHaar_sphere_of_ne_zero (volume : Measure (ℝ^n)) 0 ht.ne'
  have hd : ∀ᵐ y : ℝ^n, HasDerivAt (fun s ↦ (s / max s ‖y‖) * f y)
      ((if t < ‖y‖ then ‖y‖⁻¹ else 0) * f y) t := by
    filter_upwards [hnull] with y hy
    have hyt : ‖y‖ ≠ t := fun h ↦ hy (mem_sphere_zero_iff_norm.mpr h)
    exact (hasDerivAt_shell_profile ht hyt).mul_const (f y)
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    (Ici_mem_nhds hat) (Filter.Eventually.of_forall hmeas) hint hDm hlip
      (hf.norm.const_mul a⁻¹) hd).2

end WaveEquation.Strichartz
