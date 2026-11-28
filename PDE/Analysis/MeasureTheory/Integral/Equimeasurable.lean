/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Functions with the same distribution

Two functions `f, g ≥ 0`, possibly on two different measure spaces, have the same distribution
when `{f > t}` and `{g > t}` have the same measure for every level `t`. Such functions have the
same integral and the same `L^p` norms. Conversely, the distribution above `0` of a measurable
real function is determined by the integrals of the continuous functions of its values that
vanish at `0`. The symmetric decreasing rearrangement (`PDE.Analysis.Rearrangement.symmDecr`)
has the distribution of the function, which is how these statements are used. Integrals of
`G ∘ f` for a general increasing `G` are not treated; the powers are what the `L^p` norms need.

## Main results

* `MeasureTheory.ae_measure_le_eq_measure_lt`: for every measure and every `f` with values in
  `[0, ∞]`, `{f ≥ t}` and `{f > t}` have the same measure for almost every `t > 0`. It is
  Mathlib's `MeasureTheory.countable_meas_le_ne_meas_lt` read on the levels `ENNReal.ofReal t`.
  Mathlib's `MeasureTheory.meas_le_ae_eq_meas_lt` is the same fact for a measure on the levels
  themselves.
* `MeasureTheory.lintegral_eq_of_measure_lt_eq`, `MeasureTheory.lintegral_rpow_eq_of_measure_lt_eq`:
  for almost everywhere measurable `f`, `g` with values in `[0, ∞]`, equal distributions give
  equal integrals, also of the `p`-th powers, `p > 0`.
* `MeasureTheory.measure_lt_eq_of_lintegral_comp_eq`: for measurable real `u`, `v` with the same
  integrals of `ofReal (g ∘ u)` and `ofReal (g ∘ v)` for every continuous `g` with `g 0 = 0`,
  `μ {v > t} = μ {u > t}` at every level `t ≥ 0`.

## How it works

By the layer cake formula (`MeasureTheory.lintegral_eq_lintegral_measure_ofReal_le`) the
integral of `f` is the integral over `t > 0` of the measure of `{f ≥ t}`. For all but countably
many `t` this is the measure of `{f > t}`, so two functions with the same distribution have the
same integral. Their `p`-th powers again have the same distribution, because
`{f^p > t} = {f > t^{1/p}}`. For the converse, the measure of `{u > t}` is the increasing limit
of the integrals of the ramps `min(1, k (u - t)⁺)`. For `t ≥ 0` these are continuous functions
of `u` that vanish at `0`, which is why only the levels `t ≥ 0` are reached.

## References

* E. H. Lieb and M. Loss, *Analysis*, 2nd ed., Graduate Studies in Mathematics 14, American
  Mathematical Society, 2001, Chapter 1 (the layer cake representation) and Chapter 3
  (rearrangements).
  <https://doi.org/10.1090/gsm/014>
-/

@[expose] public noncomputable section

open Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {f : α → ℝ≥0∞} {g : β → ℝ≥0∞}

/-- For almost every level `t > 0` the sets `{f ≥ t}` and `{f > t}` have the same measure. -/
theorem ae_measure_le_eq_measure_lt (μ : Measure α) (f : α → ℝ≥0∞) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      μ {x | ENNReal.ofReal t ≤ f x} = μ {x | ENNReal.ofReal t < f x} := by
  have hc := countable_meas_le_ne_meas_lt μ f
  have hc' : (Ioi (0 : ℝ) ∩ ENNReal.ofReal ⁻¹'
      {T | μ {x | T ≤ f x} ≠ μ {x | T < f x}}).Countable :=
    MapsTo.countable_of_injOn (f := ENNReal.ofReal) (fun _ ht ↦ ht.2)
      (by
        intro a ha b hb hab
        exact (ENNReal.ofReal_eq_ofReal_iff (le_of_lt ha.1) (le_of_lt hb.1)).mp hab)
      hc
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hc'.measure_zero volume)] with t ht ht0
  by_contra hne
  exact ht ⟨ht0, hne⟩

/-- **Functions with the same distribution have the same integral**, by the layer cake
formula. The two functions may live on different measure spaces. -/
theorem lintegral_eq_of_measure_lt_eq (hf : AEMeasurable f μ) (hg : AEMeasurable g ν)
    (h : ∀ t : ℝ≥0∞, μ {x | t < f x} = ν {y | t < g y}) : ∫⁻ x, f x ∂μ = ∫⁻ y, g y ∂ν := by
  rw [lintegral_eq_lintegral_measure_ofReal_le μ hf, lintegral_eq_lintegral_measure_ofReal_le ν hg]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_measure_le_eq_measure_lt μ f, ae_measure_le_eq_measure_lt ν g] with t h1 h2
  rw [h1, h2, h]

/-- Functions with the same distribution have the same integral of the `p`-th power, `p > 0`. -/
theorem lintegral_rpow_eq_of_measure_lt_eq (hf : AEMeasurable f μ) (hg : AEMeasurable g ν)
    (h : ∀ t : ℝ≥0∞, μ {x | t < f x} = ν {y | t < g y}) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, f x ^ p ∂μ = ∫⁻ y, g y ^ p ∂ν := by
  refine lintegral_eq_of_measure_lt_eq (hf.pow_const p) (hg.pow_const p) fun t ↦ ?_
  have e1 : {x | t < f x ^ p} = {x | t ^ p⁻¹ < f x} := by
    ext x
    exact (ENNReal.rpow_inv_lt_iff hp).symm
  have e2 : {y | t < g y ^ p} = {y | t ^ p⁻¹ < g y} := by
    ext y
    exact (ENNReal.rpow_inv_lt_iff hp).symm
  rw [e1, e2, h]

/-- If two measurable real functions have the same integrals of `g ∘ ·` for every continuous
`g` that vanishes at `0`, where negative values of `g` count as `0`, then the sets `{v > t}`
and `{u > t}` have the same measure for every level `t ≥ 0`: the indicator of `(t, ∞)` is an
increasing limit of such functions `g`. -/
theorem measure_lt_eq_of_lintegral_comp_eq {u v : α → ℝ} (hu : Measurable u) (hv : Measurable v)
    (h : ∀ g : ℝ → ℝ, Continuous g → g 0 = 0 →
      ∫⁻ x, ENNReal.ofReal (g (v x)) ∂μ = ∫⁻ x, ENNReal.ofReal (g (u x)) ∂μ)
    {t : ℝ} (ht : 0 ≤ t) : μ {x | t < v x} = μ {x | t < u x} := by
  -- the ramps `g k s = min 1 (k (s - t)⁺)`
  have hg (k : ℕ) : Continuous fun s : ℝ ↦ min 1 ((k : ℝ) * max (s - t) 0) :=
    continuous_const.min (continuous_const.mul ((continuous_id.sub continuous_const).max
      continuous_const))
  have hg0 (k : ℕ) : min 1 ((k : ℝ) * max (0 - t) 0) = 0 := by
    rw [max_eq_right (by linarith), mul_zero]
    exact min_eq_right zero_le_one
  have key {w : α → ℝ} (hw : Measurable w) :
      Tendsto (fun k : ℕ ↦ ∫⁻ x, ENNReal.ofReal (min 1 ((k : ℝ) * max (w x - t) 0)) ∂μ) atTop
        (𝓝 (μ {x | t < w x})) := by
    have hs : MeasurableSet {x | t < w x} := measurableSet_lt measurable_const hw
    rw [← lintegral_indicator_one hs]
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun k ↦ ((ENNReal.continuous_ofReal.comp (hg k)).measurable.comp hw).aemeasurable)
      (Eventually.of_forall fun x k l hkl ↦ ENNReal.ofReal_le_ofReal (min_le_min le_rfl
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkl) (le_max_right _ _))))
      (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : t < w x
    · rw [indicator_of_mem (show x ∈ {x | t < w x} from hx), Pi.one_apply]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈1 / (w x - t)⌉₊] with k hk
      have hpos : 0 < w x - t := sub_pos.mpr hx
      have hk' : 1 / (w x - t) ≤ k := (Nat.le_ceil _).trans (Nat.cast_le.mpr hk)
      have h1 : (1 : ℝ) ≤ (k : ℝ) * max (w x - t) 0 := by
        rw [max_eq_left hpos.le]
        exact (div_le_iff₀ hpos).mp hk'
      rw [min_eq_left h1, ENNReal.ofReal_one]
    · rw [indicator_of_notMem (show x ∉ {x | t < w x} from hx)]
      have h0 : max (w x - t) 0 = 0 := max_eq_right (by linarith [not_lt.mp hx])
      simp only [h0, mul_zero]
      rw [min_eq_right zero_le_one, ENNReal.ofReal_zero]
      exact tendsto_const_nhds
  refine tendsto_nhds_unique (key hv) ?_
  have hk (k : ℕ) := h _ (hg k) (hg0 k)
  simp only [hk]
  exact key hu

end MeasureTheory
