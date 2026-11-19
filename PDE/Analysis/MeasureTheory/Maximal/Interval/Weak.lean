/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
# Maximal averages over intervals

Vitali's disjoint interval selection gives a weak (1,1) bound with constant four.
Truncating the function gives the tail estimate used for strong Lp bounds.
The radius family can be uncountable: Fatou's lemma gives lower semicontinuity.
All integrals and inequalities retain infinite values.
-/

@[expose] public section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace MeasureTheory

/-- A bounded family of intervals with large averages controls the measure of its centers. -/
theorem mul_measure_le_lintegral_of_ball_averages {s : Set ℝ} {r : ℝ → ℝ}
    {R : ℝ} {a : ℝ≥0∞} (f : ℝ → ℝ≥0∞)
    (hr : ∀ x ∈ s, 0 < r x) (hR : ∀ x ∈ s, r x ≤ R)
    (havg : ∀ x ∈ s, a * volume (ball x (r x)) ≤ ∫⁻ y in ball x (r x), f y) :
    a * volume s ≤ 4 * ∫⁻ y, f y := by
  obtain ⟨u, hus, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball s id r R hR 4 (by norm_num)
  have huc : u.Countable := hdisj.countable_of_isOpen (fun _ _ ↦ isOpen_ball)
    (fun x hx ↦ ⟨x, mem_ball_self (hr x (hus hx))⟩)
  have hsub : s ⊆ ⋃ x ∈ u, ball x (4 * r x) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact mem_iUnion₂.mpr ⟨y, hy, hxy (mem_ball_self (hr x hx))⟩
  have hscale (x : ℝ) : volume (ball x (4 * r x)) = 4 * volume (ball x (r x)) := by
    simp only [Real.volume_ball]
    rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  have hsum : (∑' x : u, ∫⁻ y in ball x.val (r x.val), f y) ≤ ∫⁻ y, f y := by
    have heq := lintegral_biUnion (μ := volume) huc
      (fun _ _ ↦ measurableSet_ball) hdisj f
    simpa only [id_eq] using heq.symm.le.trans (setLIntegral_le_lintegral _ f)
  calc
    a * volume s ≤ a * (∑' x : u, volume (ball x.val (4 * r x.val))) := by
      gcongr
      exact (measure_mono hsub).trans (measure_biUnion_le volume huc _)
    _ = 4 * ∑' x : u, a * volume (ball x.val (r x.val)) := by
      simp_rw [hscale]
      rw [ENNReal.tsum_mul_left, ← mul_assoc, mul_comm a, mul_assoc,
        ENNReal.tsum_mul_left]
    _ ≤ 4 * ∑' x : u, ∫⁻ y in ball x.val (r x.val), f y := by
      gcongr with x
      exact havg x.val (hus x.property)
    _ ≤ 4 * ∫⁻ y, f y := by gcongr

/-- The supremum of centered interval averages over the specified radius family. -/
noncomputable def intervalMaximal {ι : Type*} (r : ι → ℝ) (f : ℝ → ℝ≥0∞)
    (x : ℝ) : ℝ≥0∞ :=
  ⨆ i, (∫⁻ y in ball x (r i), f y) / volume (ball x (r i))

/-- The weak (1,1) estimate for arbitrary families of positive interval radii. -/
theorem mul_measure_intervalMaximal_superlevel_le {ι : Type*} (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (f : ℝ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * volume {x | ENNReal.ofReal a < intervalMaximal r f x} ≤
      4 * ∫⁻ y, f y := by
  classical
  by_cases htop : (∫⁻ y, f y) = ⊤
  · simp [htop]
  let s := {x | ENNReal.ofReal a < intervalMaximal r f x}
  have hex (x : ℝ) (hx : x ∈ s) :
      ∃ i, ENNReal.ofReal a < (∫⁻ y in ball x (r i), f y) / volume (ball x (r i)) := by
    exact lt_iSup_iff.mp hx
  let ρ : ℝ → ℝ := fun x ↦ if hx : x ∈ s then r (Classical.choose (hex x hx)) else 1
  have hρ (x : ℝ) (hx : x ∈ s) : 0 < ρ x := by
    dsimp [ρ]
    rw [dite_eq_left hx]
    exact hr _
  have havg (x : ℝ) (hx : x ∈ s) :
      ENNReal.ofReal a * volume (ball x (ρ x)) ≤ ∫⁻ y in ball x (ρ x), f y := by
    have hchoice := Classical.choose_spec (hex x hx)
    have hvol₀ : volume (ball x (r (Classical.choose (hex x hx)))) ≠ 0 := by
      rw [Real.volume_ball]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) (hr _)))
    have hvol_top : volume (ball x (r (Classical.choose (hex x hx)))) ≠ ⊤ := by
      rw [Real.volume_ball]
      exact ENNReal.ofReal_ne_top
    have hmul := (ENNReal.lt_div_iff_mul_lt (Or.inl hvol₀) (Or.inl hvol_top)).mp hchoice
    simpa only [ρ, dite_eq_left hx] using hmul.le
  have hbound (x : ℝ) (hx : x ∈ s) : ρ x ≤ (∫⁻ y, f y).toReal / (2 * a) := by
    have hle := ENNReal.toReal_mono htop ((havg x hx).trans (setLIntegral_le_lintegral _ f))
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le, Real.volume_ball,
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hρ x hx).le)] at hle
    apply (le_div_iff₀ (mul_pos (by norm_num) ha)).mpr
    nlinarith
  exact mul_measure_le_lintegral_of_ball_averages f hρ hbound havg

/-- A countable supremum of interval averages is measurable, with arbitrary real radii. -/
theorem measurable_intervalMaximal {ι : Type*} [Countable ι] (r : ι → ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) : Measurable (intervalMaximal r f) := by
  unfold intervalMaximal
  apply Measurable.iSup
  intro i
  simp only [Real.volume_ball]
  have hkernel : Measurable (fun p : ℝ × ℝ ↦
      {p : ℝ × ℝ | dist p.2 p.1 < r i}.indicator (fun p ↦ f p.2) p) := by
    exact (hf.comp measurable_snd).indicator
      (measurableSet_lt (measurable_snd.dist measurable_fst) measurable_const)
  have hsection (x : ℝ) : (∫⁻ y, {p : ℝ × ℝ | dist p.2 p.1 < r i}.indicator
      (fun p ↦ f p.2) (x, y)) = ∫⁻ y in ball x (r i), f y := by
    change (∫⁻ y, (ball x (r i)).indicator f y) = _
    exact lintegral_indicator measurableSet_ball f
  have hmeas := hkernel.lintegral_prod_right' (ν := volume)
  simp_rw [hsection] at hmeas
  exact hmeas.div_const _

/-- The integral over a translated open interval is lower semicontinuous in its center. -/
theorem lowerSemicontinuous_ball_lintegral {f : ℝ → ℝ≥0∞} (hf : Measurable f) (r : ℝ) :
    LowerSemicontinuous (fun x ↦ ∫⁻ y in ball x r, f y) := by
  classical
  let F : ℝ → ℝ → ℝ≥0∞ := fun x y ↦ (ball x r).indicator f y
  have hFm (x : ℝ) : Measurable (F x) := hf.indicator measurableSet_ball
  have hFl (y : ℝ) : LowerSemicontinuous (fun x ↦ F x y) := by
    have h := (isOpen_ball (x := y) (ε := r)).lowerSemicontinuous_indicator
      (show (0 : ℝ≥0∞) ≤ f y from zero_le)
    convert h using 1
    ext x
    dsimp only [F]
    simp only [indicator_apply, mem_ball, dist_comm]
  have hresult : LowerSemicontinuous (fun x ↦ ∫⁻ y, F x y) := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro x
    calc
      _ ≤ ∫⁻ y, liminf (fun z ↦ F z y) (𝓝 x) :=
        lintegral_mono (fun y ↦ (hFl y).le_liminf x)
      _ ≤ _ := lintegral_liminf_le hFm
  simpa only [F, lintegral_indicator measurableSet_ball] using hresult

/-- Positive interval averages have a lower semicontinuous supremum, even for uncountable
families. -/
theorem lowerSemicontinuous_intervalMaximal {ι : Type*} (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    LowerSemicontinuous (intervalMaximal r f) := by
  unfold intervalMaximal
  apply lowerSemicontinuous_iSup
  intro i
  simp only [Real.volume_ball]
  exact (ENNReal.continuous_div_const _
    (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) (hr i))))).comp_lowerSemicontinuous
      (lowerSemicontinuous_ball_lintegral hf (r i))
      (fun _ _ h ↦ ENNReal.div_le_div_right h _)

/-- Removing the part of the function below a threshold changes maximal averages by at most it. -/
theorem intervalMaximal_le_truncated_add {ι : Type*} (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (f : ℝ → ℝ≥0∞) (c : ℝ≥0∞) (x : ℝ) :
    intervalMaximal r f x ≤ intervalMaximal r ({y | c < f y}.indicator f) x + c := by
  let g := {y | c < f y}.indicator f
  have hfg (y : ℝ) : f y ≤ g y + c := by
    by_cases hy : c < f y
    · simp only [g, indicator_apply, mem_ofPred_eq, hy, ↓reduceIte]
      exact le_add_right le_rfl
    · simp only [g, indicator_apply, mem_ofPred_eq, hy, ↓reduceIte, zero_add]
      exact le_of_not_gt hy
  apply iSup_le
  intro i
  have hvol₀ : volume (ball x (r i)) ≠ 0 := by
    rw [Real.volume_ball]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) (hr i)))
  have hvol_top : volume (ball x (r i)) ≠ ⊤ := by
    rw [Real.volume_ball]
    exact ENNReal.ofReal_ne_top
  calc
    _ ≤ (∫⁻ y in ball x (r i), g y + c) / volume (ball x (r i)) :=
      ENNReal.div_le_div_right (lintegral_mono hfg) _
    _ = (∫⁻ y in ball x (r i), g y) / volume (ball x (r i)) + c := by
      rw [lintegral_add_right g measurable_const]
      simp only [lintegral_const, Measure.restrict_apply_univ]
      rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hvol₀ hvol_top]
    _ ≤ intervalMaximal r g x + c := by
      gcongr
      exact le_iSup (fun j ↦ (∫⁻ y in ball x (r j), g y) / volume (ball x (r j))) i

/-- A maximal superlevel is controlled by the integral of the function above half that level. -/
theorem mul_measure_intervalMaximal_superlevel_le_truncated {ι : Type*} (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (f : ℝ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * volume {x | ENNReal.ofReal (2 * a) < intervalMaximal r f x} ≤
      4 * ∫⁻ y in {y | ENNReal.ofReal a < f y}, f y := by
  let g := {y | ENNReal.ofReal a < f y}.indicator f
  have hsub : {x | ENNReal.ofReal (2 * a) < intervalMaximal r f x} ⊆
      {x | ENNReal.ofReal a < intervalMaximal r g x} := by
    intro x hx
    by_contra hnot
    have hlow : intervalMaximal r g x ≤ ENNReal.ofReal a := le_of_not_gt hnot
    have hle : intervalMaximal r f x ≤ ENNReal.ofReal a + ENNReal.ofReal a := by
      calc
        _ ≤ intervalMaximal r g x + ENNReal.ofReal a :=
          intervalMaximal_le_truncated_add r hr f (ENNReal.ofReal a) x
        _ ≤ _ := by gcongr
    have heq : ENNReal.ofReal a + ENNReal.ofReal a = ENNReal.ofReal (2 * a) := by
      rw [← ENNReal.ofReal_add ha.le ha.le, two_mul]
    rw [heq] at hle
    exact not_lt_of_ge hle hx
  calc
    _ ≤ ENNReal.ofReal a * volume {x | ENNReal.ofReal a < intervalMaximal r g x} := by
      gcongr
    _ ≤ 4 * ∫⁻ y, g y := mul_measure_intervalMaximal_superlevel_le r hr g ha
    _ ≤ _ := by
      gcongr 1
      exact lintegral_indicator_le f _

/-- An integrable nonnegative function has finite maximal averages almost everywhere. -/
theorem ae_intervalMaximal_lt_top {ι : Type*} (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) {f : ℝ → ℝ≥0∞} (hfin : (∫⁻ y, f y) < ⊤) :
    ∀ᵐ x, intervalMaximal r f x < ⊤ := by
  have hbound (n : ℕ) : (n : ℝ≥0∞) * volume {x | intervalMaximal r f x = ⊤} ≤
      4 * ∫⁻ y, f y := by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    have hsub : {x | intervalMaximal r f x = ⊤} ⊆
        {x | ENNReal.ofReal (n : ℝ) < intervalMaximal r f x} := by
      intro x hx
      change intervalMaximal r f x = ⊤ at hx
      change ENNReal.ofReal (n : ℝ) < intervalMaximal r f x
      rw [hx]
      exact ENNReal.ofReal_lt_top
    calc
      _ ≤ ENNReal.ofReal (n : ℝ) *
          volume {x | ENNReal.ofReal (n : ℝ) < intervalMaximal r f x} := by
        have hm := measure_mono (μ := volume) hsub
        simp only [ENNReal.ofReal_natCast] at hm ⊢
        gcongr 1
      _ ≤ _ := mul_measure_intervalMaximal_superlevel_le r hr f (Nat.cast_pos.mpr hn)
  have htop : ⊤ * volume {x | intervalMaximal r f x = ⊤} ≤ 4 * ∫⁻ y, f y := by
    calc
      _ = (⨆ n : ℕ, (n : ℝ≥0∞)) * volume {x | intervalMaximal r f x = ⊤} := by
        rw [ENNReal.iSup_natCast]
      _ ≤ _ := by
        rw [ENNReal.iSup_mul]
        exact iSup_le hbound
  have hzero : volume {x | intervalMaximal r f x = ⊤} = 0 := by
    by_contra hn
    rw [ENNReal.top_mul hn] at htop
    exact (ENNReal.mul_lt_top (by norm_num) hfin).not_ge htop
  simpa only [ae_iff, not_lt_top_iff] using hzero

/-- The centered maximal function over all positive interval radii. -/
noncomputable def centeredMaximal (f : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  intervalMaximal (fun r : Ioi (0 : ℝ) ↦ r.val) f x

/-- Every interval integral is bounded by its length times the centered maximal function. -/
theorem lintegral_ball_le_centeredMaximal (f : ℝ → ℝ≥0∞) (x : ℝ)
    {R : ℝ} (hR : 0 < R) :
    (∫⁻ y in ball x R, f y) ≤ ENNReal.ofReal (2 * R) * centeredMaximal f x := by
  have hvol₀ : volume (ball x R) ≠ 0 := by
    rw [Real.volume_ball]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hvoltop : volume (ball x R) ≠ ⊤ := by
    rw [Real.volume_ball]
    exact ENNReal.ofReal_ne_top
  rw [← Real.volume_ball x R, ← ENNReal.div_le_iff' hvol₀ hvoltop]
  exact le_iSup (fun r : Ioi (0 : ℝ) ↦
    (∫⁻ y in ball x r.val, f y) / volume (ball x r.val)) ⟨R, hR⟩

end MeasureTheory
