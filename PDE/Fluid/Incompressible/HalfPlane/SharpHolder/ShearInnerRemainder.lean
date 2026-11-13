/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.ShearRowCells

/-!
# The remainder of the inner rows

The second part of `C_in`, `2 ∫_0^∞ ∫_{T_y(0, q)}^1 |Δ(p, q)| (2p)^{1/2} dp dq`, is a single
integral: for `0 < p < 1` the rows with `T_y(0, q) = (1 - 3q²)^{1/2} < p` are `q > q_*`,
`q_*² = (1 - p²)/3`, where `Δ ≥ 0`, and `∫_{q_*}^∞ Δ(p, q) dq = 3√3 p / (2 (1 - p²)^{1/2} (4 - p²))`
(`lintegral_shearDifference_rows_eq`). So the remainder is
`∫_0^1 3√6 p^{3/2} / ((4 - p²)(1 - p²)^{1/2}) dp` (`lintegral_shearRowRemainder_eq`). Chen and
Hou, Part I, (B.50), define `C_in` through the two-dimensional integral; the one-dimensional form
is ours. A cell walk bounds the integral over `(0, e]`
(`lintegral_le_shearRemainderWalk`), and the end `(1 - δ, 1)` costs at most `2√6 δ^{1/2}`
(`lintegral_shearRemainderDensity_end_le`).

## Main definitions

* `shearRemainderDensity`: the integrand `G(p) = 3√6 p^{3/2} / ((4 - p²)(1 - p²)^{1/2})`.
* `shearRowRemainder`: the remainder `∫_{T_y(0, q)}^1 |Δ(p, q)| (2p)^{1/2} dp` of the row `q`.
* `shearRemainderCell`: the rounded bound of `∫ G` over a cell `[p₀, p₁]`.
* `shearRemainderWalk`: the walk of cells over `[0, e]`.

## Main results

* `lintegral_shearDifference_rows_eq`:
  `∫_{q_*}^∞ Δ(p, q) dq = 3√3 p / (2 (1 - p²)^{1/2} (4 - p²))`.
* `lintegral_shearRowRemainder_eq`: `∫_0^∞ shearRowRemainder q dq = ∫_0^1 G(p)/2 dp`.
* `lintegral_le_shearRemainderCell`: the cell bound is sound.
* `lintegral_le_shearRemainderWalk`: a walk value `N` bounds `∫_{(0, e]} G` by `N/2⁶⁴`.
* `lintegral_shearRemainderDensity_end_le`: `∫_{1-δ}^1 G ≤ 2√6 δ^{1/2}`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix B.2.1, (B.48)-(B.50),
  pp. 137-138, and (B.67), p. 142.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter PDE.Analysis
open scoped ENNReal Topology

namespace IncompressibleFlow.SharpHolder

/-- The integrand `3√6 p^{3/2} / ((4 - p²)(1 - p²)^{1/2})` of the remainder. -/
def shearRemainderDensity (p : ℝ) : ℝ :=
  3 * Real.sqrt 6 * (p * Real.sqrt p) / ((4 - p ^ 2) * Real.sqrt (1 - p ^ 2))

/-- `T_y(0, q) < p` exactly when `q² > (1 - p²)/3`, for `p > 0`. -/
theorem horizontalShearMap_zero_lt_iff {p q : ℝ} (hp : 0 < p) :
    horizontalShearMap 0 q < p ↔ (1 - p ^ 2) / 3 < q ^ 2 := by
  rw [horizontalShearMap_zero_left, Real.sqrt_lt' hp]
  constructor <;> intro h <;> linarith

/-- `t / (c + t²) → 0`. -/
theorem tendsto_div_add_sq {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun t : ℝ ↦ t / (c + t ^ 2)) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ ↦ c / t + t) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_gt_atTop 0] with t ht
    have := div_nonneg hc ht.le
    simp only [id]
    linarith
  refine h.inv_tendsto_atTop.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Pi.inv_apply]
  have : 0 < c + t ^ 2 := by positivity
  field_simp

/-- The rows above `q_*`: `∫_{q_*}^∞ Δ(p, q) dq = 3√3 p / (2 (1 - p²)^{1/2} (4 - p²))`. -/
theorem lintegral_shearDifference_rows_eq {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∫⁻ q in Ioi (Real.sqrt ((1 - p ^ 2) / 3)), ‖shearDifference p q‖ₑ =
      ENNReal.ofReal (3 * Real.sqrt 3 * p / (2 * Real.sqrt (1 - p ^ 2) * (4 - p ^ 2))) := by
  set w := (1 - p ^ 2) / 3 with hw
  have hw0 : 0 < w := by simp only [w]; nlinarith
  set qs := Real.sqrt w
  have hqs : 0 < qs := Real.sqrt_pos.2 hw0
  have hqs2 : qs ^ 2 = w := Real.sq_sqrt hw0.le
  have hpm : (p - 1) ^ 2 ≠ 0 := by
    have : p - 1 ≠ 0 := by linarith
    positivity
  -- above `q_*` the sign quartic is `≤ 0`
  have hΔ : ∀ q ∈ Ici qs, 0 ≤ shearDifference p q := by
    intro q hq
    have hq0 : 0 < q := hqs.trans_le hq
    refine shearDifference_nonneg_of_shearQuartic_nonpos hp hq0 ?_
    refine (shearQuartic_le_of_le hqs.le hq).trans ?_
    have e : shearQuartic p qs = 4 * p ^ 2 * (p ^ 2 - 1) / 3 := by
      simp only [shearQuartic]
      rw [show qs ^ 4 = (qs ^ 2) ^ 2 by ring, hqs2]
      simp only [w]
      ring
    rw [e]
    have : p ^ 2 - 1 ≤ 0 := by nlinarith
    have : 0 ≤ 4 * p ^ 2 := by positivity
    nlinarith
  have hint := lintegral_Ioi_ofReal_deriv (a := qs) (l := 0) (g := shearPotential p)
    (g' := shearDifference p) (fun q hq ↦ ?_) (fun q hq ↦ hΔ q (le_of_lt hq))
    (tendsto_shearPotential p)
  · rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun q ↦ ENNReal.ofReal
      (shearDifference p q)) fun q hq ↦ by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hΔ q (le_of_lt hq))], hint]
    congr 1
    -- the value of the potential at `q_*`
    set s := Real.sqrt (1 - p ^ 2)
    set r := Real.sqrt 3
    have hs : 0 < s := Real.sqrt_pos.2 (by nlinarith)
    have hr : 0 < r := Real.sqrt_pos.2 (by norm_num)
    have hs2 : s ^ 2 = 1 - p ^ 2 := Real.sq_sqrt (by nlinarith)
    have hr2 : r ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hqsr : qs = s / r := by
      simp only [qs, w, s, r]
      rw [Real.sqrt_div' _ (by norm_num)]
    simp only [shearPotential]
    rw [hqs2]
    have h1 : (p + 1) ^ 2 + w = 2 * (1 + p) * (2 + p) / 3 := by rw [hw]; ring
    have h2 : (p - 1) ^ 2 + w = 2 * (1 - p) * (2 - p) / 3 := by rw [hw]; ring
    rw [h1, h2, hqsr]
    have a1 : (1 : ℝ) - p ≠ 0 := by linarith
    have a2 : (2 : ℝ) - p ≠ 0 := by linarith
    have a3 : (4 : ℝ) - p ^ 2 ≠ 0 := by nlinarith
    have a4 : (1 : ℝ) + p ≠ 0 := by linarith
    have a5 : (2 : ℝ) + p ≠ 0 := by linarith
    have hsn := hs.ne'
    have hrn := hr.ne'
    field_simp
    linear_combination (18 * p * (4 - p ^ 2)) * hs2 - (6 * p * (1 - p ^ 2) * (4 - p ^ 2)) * hr2
  · have hq0 : 0 < q := hqs.trans_le hq
    exact hasDerivAt_shearPotential (by positivity) (by positivity)

/-- The remainder `∫_{T_y(0, q)}^1 |Δ(p, q)| (2p)^{1/2} dp` of the row `q`. -/
def shearRowRemainder (q : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in Ioo (horizontalShearMap 0 q) 1,
    ‖shearDifference p q‖ₑ * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ))

/-- `q ↦ T_y(0, q)` is measurable. -/
theorem measurable_horizontalShearMap_zero : Measurable fun q ↦ horizontalShearMap 0 q := by
  simp only [horizontalShearMap_zero_left]
  fun_prop

/-- **The remainder as a single integral.** -/
theorem lintegral_shearRowRemainder_eq :
    ∫⁻ q in Ioi 0, shearRowRemainder q =
      ∫⁻ p in Ioo 0 1, ENNReal.ofReal (shearRemainderDensity p / 2) := by
  set F : ℝ → ℝ → ℝ≥0∞ := fun q p ↦ {x : ℝ × ℝ | horizontalShearMap 0 x.1 < x.2}.indicator
    (fun x ↦ ‖shearDifference x.2 x.1‖ₑ * ENNReal.ofReal ((2 * x.2) ^ (1 / 2 : ℝ))) (q, p)
  have hF : Measurable (Function.uncurry F) := by
    refine Measurable.indicator ?_ (measurableSet_lt
      (measurable_horizontalShearMap_zero.comp measurable_fst) measurable_snd)
    exact (measurable_shearDifference.comp (measurable_snd.prodMk measurable_fst)).enorm.mul
      ((measurable_snd.const_mul 2).pow_const _).ennreal_ofReal
  have hrow : ∀ q, shearRowRemainder q = ∫⁻ p in Ioo 0 1, F q p := by
    intro q
    have h0 : 0 ≤ horizontalShearMap 0 q := Real.sqrt_nonneg _
    have e : Ioo (horizontalShearMap 0 q) 1 = Ioi (horizontalShearMap 0 q) ∩ Ioo 0 1 := by
      ext p
      simp only [mem_Ioo, mem_inter_iff, mem_Ioi]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h0.trans_lt h1, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    rw [shearRowRemainder, e, ← Measure.restrict_restrict measurableSet_Ioi,
      ← lintegral_indicator measurableSet_Ioi]
    rfl
  simp_rw [hrow]
  rw [lintegral_lintegral_swap hF.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioo fun p hp ↦ ?_
  have hp0 : 0 < p := hp.1
  have hp1 : p < 1 := hp.2
  set qs := Real.sqrt ((1 - p ^ 2) / 3)
  have hqs : 0 ≤ qs := Real.sqrt_nonneg _
  have hset : ∀ q ∈ Ioi (0 : ℝ), F q p = (Ioi qs).indicator (fun q ↦
      ‖shearDifference p q‖ₑ * ENNReal.ofReal ((2 * p) ^ (1 / 2 : ℝ))) q := by
    intro q hq
    have hq0 : 0 < q := hq
    have hiff : horizontalShearMap 0 q < p ↔ qs < q := by
      rw [horizontalShearMap_zero_lt_iff hp0]
      constructor
      · intro h
        exact (Real.sqrt_lt' hq0).2 h
      · intro h
        exact (Real.sqrt_lt' hq0).1 h
    simp only [F, indicator, mem_ofPred_eq, mem_Ioi, hiff]
  rw [setLIntegral_congr_fun measurableSet_Ioi hset, lintegral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  have hsub : Ioi qs ∩ Ioi (0 : ℝ) = Ioi qs := by
    have hqs0 : 0 < qs := Real.sqrt_pos.2 (by nlinarith)
    exact Set.inter_eq_left.2 (Ioi_subset_Ioi hqs0.le)
  rw [hsub, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_shearDifference_rows_eq hp0 hp1,
    ← ENNReal.ofReal_mul (by
      have : 0 < 4 - p ^ 2 := by nlinarith
      have : 0 < Real.sqrt (1 - p ^ 2) := Real.sqrt_pos.2 (by nlinarith)
      positivity)]
  congr 1
  simp only [shearRemainderDensity]
  rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num) p,
    show (6 : ℝ) = 2 * 3 by norm_num, Real.sqrt_mul (by norm_num) 3]
  have h4 : (4 : ℝ) - p ^ 2 ≠ 0 := by nlinarith
  have hs : Real.sqrt (1 - p ^ 2) ≠ 0 := (Real.sqrt_pos.2 (by nlinarith)).ne'
  field_simp

/-! ### The remainder on cells -/

/-- The cell bound of the remainder on `[p₀, p₁]`: `2c (p₁ - p₀)/((1 - p₀)^{1/2} + (1 - p₁)^{1/2})`
with `c = 3√6 p₁^{3/2} / ((4 - p₁²)(1 + p₀)^{1/2})`, rounded outward. -/
def shearRemainderCell (p₀ p₁ : ℚ) : Option ℤ :=
  if decide (0 ≤ p₀) && decide (p₀ < p₁) && decide (p₁ < 1) then
    some (ceilScaled 64 (2 * (3 * sqrtHigh 6 * (p₁ * sqrtHigh p₁) /
      ((4 - p₁ ^ 2) * sqrtLow (1 + p₀))) * (p₁ - p₀) / (sqrtLow (1 - p₀) + sqrtLow (1 - p₁))))
  else none

/-- `G(p) ≤ c/(1 - p)^{1/2}` on a cell, with the real constant `c`. -/
private theorem shearRemainderDensity_le {p₀ p₁ p : ℝ} (hp₀ : 0 ≤ p₀) (hp : p ∈ Ioc p₀ p₁)
    (hp₁ : p₁ < 1) :
    shearRemainderDensity p ≤ 3 * Real.sqrt 6 * (p₁ * Real.sqrt p₁) /
      ((4 - p₁ ^ 2) * Real.sqrt (1 + p₀)) / Real.sqrt (1 - p) := by
  obtain ⟨hpa, hpb⟩ := hp
  have hp0 : 0 < p := hp₀.trans_lt hpa
  have hu : 0 < 1 - p := by linarith
  have hsu := Real.sqrt_pos.2 hu
  have h4 : 0 < 4 - p₁ ^ 2 := by nlinarith
  have h4' : 4 - p₁ ^ 2 ≤ 4 - p ^ 2 := by nlinarith
  have hsq : Real.sqrt (1 - p ^ 2) = Real.sqrt (1 - p) * Real.sqrt (1 + p) := by
    rw [← Real.sqrt_mul hu.le]
    ring_nf
  have hpp : p * Real.sqrt p ≤ p₁ * Real.sqrt p₁ :=
    mul_le_mul hpb (Real.sqrt_le_sqrt hpb) (Real.sqrt_nonneg _) (by linarith)
  have h1p : Real.sqrt (1 + p₀) ≤ Real.sqrt (1 + p) := Real.sqrt_le_sqrt (by linarith)
  have h1p0 : 0 < Real.sqrt (1 + p₀) := Real.sqrt_pos.2 (by linarith)
  have h4p : 0 < 4 - p ^ 2 := by nlinarith
  have h1s : 0 < Real.sqrt (1 + p) := Real.sqrt_pos.2 (by linarith)
  have hp₁0 : 0 ≤ p₁ := by linarith
  unfold shearRemainderDensity
  rw [hsq, div_div, div_le_div_iff₀ (mul_pos h4p (mul_pos hsu h1s))
    (mul_pos (mul_pos h4 h1p0) hsu)]
  have h6 : 0 ≤ 3 * Real.sqrt 6 := by positivity
  calc 3 * Real.sqrt 6 * (p * Real.sqrt p) * ((4 - p₁ ^ 2) * Real.sqrt (1 + p₀) * Real.sqrt (1 - p))
      ≤ 3 * Real.sqrt 6 * (p₁ * Real.sqrt p₁) * ((4 - p ^ 2) * (Real.sqrt (1 - p) *
          Real.sqrt (1 + p))) := by
        rw [show (4 - p ^ 2) * (Real.sqrt (1 - p) * Real.sqrt (1 + p)) =
          (4 - p ^ 2) * Real.sqrt (1 + p) * Real.sqrt (1 - p) by ring]
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpp h6) (mul_le_mul_of_nonneg_right
          (mul_le_mul h4' h1p h1p0.le h4p.le) hsu.le) (by positivity)
          (mul_nonneg h6 (mul_nonneg hp₁0 (Real.sqrt_nonneg _)))

/-- **Soundness of a cell of the remainder.** -/
theorem lintegral_le_shearRemainderCell {p₀ p₁ : ℚ} {n : ℤ}
    (h : shearRemainderCell p₀ p₁ = some n) :
    ∫⁻ p in Ioc (p₀ : ℝ) p₁, ENNReal.ofReal (shearRemainderDensity p) ≤
      ENNReal.ofReal (n / 2 ^ 64) := by
  unfold shearRemainderCell at h
  split_ifs at h with hck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨hp₀, hp⟩, hp₁⟩ := hck
  simp only [Option.some.injEq] at h
  subst h
  have hp₀' : (0 : ℝ) ≤ p₀ := by exact_mod_cast hp₀
  have hp' : (p₀ : ℝ) < p₁ := by exact_mod_cast hp
  have hp₁' : (p₁ : ℝ) < 1 := by exact_mod_cast hp₁
  set c : ℝ := 3 * Real.sqrt 6 * (p₁ * Real.sqrt p₁) / ((4 - p₁ ^ 2) * Real.sqrt (1 + p₀))
  have h4 : (0 : ℝ) < 4 - p₁ ^ 2 := by nlinarith
  have hp₁0 : (0 : ℝ) ≤ p₁ := by linarith
  have h1p0 : 0 < Real.sqrt (1 + (p₀ : ℝ)) := Real.sqrt_pos.2 (by linarith)
  have hc0 : 0 ≤ c := div_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hp₁0 (Real.sqrt_nonneg _))) (mul_pos h4 h1p0).le
  -- the rational constant dominates `c`
  set cq : ℚ := 3 * sqrtHigh 6 * (p₁ * sqrtHigh p₁) / ((4 - p₁ ^ 2) * sqrtLow (1 + p₀))
  have hcq : c ≤ cq := by
    have h6 := sqrt_le_sqrtHigh (show (0 : ℚ) ≤ 6 by norm_num)
    have hp1s := sqrt_le_sqrtHigh (show (0 : ℚ) ≤ p₁ by linarith)
    have hl := sqrtLow_le_sqrt (show (0 : ℚ) ≤ 1 + p₀ by linarith)
    have hl0 := sqrtLow_pos (show (0 : ℚ) < 1 + p₀ by linarith)
    have hl0' : (0 : ℝ) < sqrtLow (1 + p₀) := by exact_mod_cast hl0
    have h4q : (0 : ℚ) < 4 - p₁ ^ 2 := by nlinarith
    simp only [c, cq]
    push_cast at h6 hp1s hl ⊢
    rw [div_le_div_iff₀ (mul_pos h4 h1p0) (mul_pos h4 hl0')]
    have hA : 3 * Real.sqrt 6 * (p₁ * Real.sqrt p₁) ≤
        3 * (sqrtHigh 6 : ℝ) * ((p₁ : ℝ) * (sqrtHigh p₁ : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h6 (by norm_num))
        (mul_le_mul_of_nonneg_left hp1s hp₁0) (mul_nonneg hp₁0 (Real.sqrt_nonneg _))
        (mul_nonneg (by norm_num) (le_trans (Real.sqrt_nonneg _) h6))
    have hB : (4 - (p₁ : ℝ) ^ 2) * sqrtLow (1 + p₀) ≤ (4 - p₁ ^ 2) * Real.sqrt (1 + p₀) :=
      mul_le_mul_of_nonneg_left hl h4.le
    exact mul_le_mul hA hB (mul_pos h4 hl0').le (mul_nonneg (mul_nonneg (by norm_num)
      (le_trans (Real.sqrt_nonneg _) h6)) (mul_nonneg hp₁0 (le_trans (Real.sqrt_nonneg _) hp1s)))
  calc ∫⁻ p in Ioc (p₀ : ℝ) p₁, ENNReal.ofReal (shearRemainderDensity p)
      ≤ ∫⁻ p in Ioc (p₀ : ℝ) p₁, ENNReal.ofReal (c / Real.sqrt (1 - p)) :=
        setLIntegral_mono' measurableSet_Ioc fun p hp ↦
          ENNReal.ofReal_le_ofReal (shearRemainderDensity_le hp₀' hp hp₁')
    _ = ENNReal.ofReal (-2 * c * Real.sqrt (1 - p₁) - -2 * c * Real.sqrt (1 - p₀)) := by
        rw [lintegral_Ioc_ofReal_deriv (g := fun p ↦ -2 * c * Real.sqrt (1 - p)) hp'.le
          (by fun_prop) (fun p hp ↦ ?_) (fun p hp ↦ by positivity)]
        have hu : 0 < 1 - p := by linarith [hp.2]
        have hd : HasDerivAt (fun p ↦ 1 - p) (-1) p := by
          simpa using (hasDerivAt_id p).const_sub 1
        refine ((hd.sqrt hu.ne').const_mul (-2 * c)).congr_deriv ?_
        have hs := Real.sqrt_pos.2 hu
        field_simp
    _ ≤ ENNReal.ofReal (((ceilScaled 64 (2 * cq * (p₁ - p₀) /
          (sqrtLow (1 - p₀) + sqrtLow (1 - p₁))) : ℤ) : ℝ) / 2 ^ 64) := by
        refine ENNReal.ofReal_le_ofReal (le_trans ?_ (le_ceilScaled_real 64 _))
        have hu₀ : (0 : ℝ) < 1 - p₀ := by linarith
        have hu₁ : (0 : ℝ) < 1 - p₁ := by linarith
        have hl₀ := sqrtLow_le_sqrt (show (0 : ℚ) ≤ 1 - p₀ by linarith)
        have hl₁ := sqrtLow_le_sqrt (show (0 : ℚ) ≤ 1 - p₁ by linarith)
        have hl₀' := sqrtLow_pos (show (0 : ℚ) < 1 - p₀ by linarith)
        have hl₁' := sqrtLow_pos (show (0 : ℚ) < 1 - p₁ by linarith)
        push_cast at hl₀ hl₁ ⊢
        have hL0 : (0 : ℝ) < sqrtLow (1 - p₀) := by exact_mod_cast hl₀'
        have hL1 : (0 : ℝ) < sqrtLow (1 - p₁) := by exact_mod_cast hl₁'
        have hs₀ := Real.sq_sqrt hu₀.le
        have hs₁ := Real.sq_sqrt hu₁.le
        have hsum : 0 < Real.sqrt (1 - p₀) + Real.sqrt (1 - p₁) := by positivity
        have e : -2 * c * Real.sqrt (1 - p₁) - -2 * c * Real.sqrt (1 - p₀) =
            2 * c * (p₁ - p₀) / (Real.sqrt (1 - p₀) + Real.sqrt (1 - p₁)) := by
          rw [eq_div_iff hsum.ne']
          nlinarith [hs₀, hs₁]
        rw [e]
        calc 2 * c * (p₁ - p₀) / (Real.sqrt (1 - p₀) + Real.sqrt (1 - p₁))
            ≤ 2 * c * (p₁ - p₀) / ((sqrtLow (1 - p₀) : ℝ) + sqrtLow (1 - p₁)) :=
              div_le_div_of_nonneg_left (by nlinarith) (by positivity) (by linarith)
          _ ≤ 2 * (cq : ℝ) * (p₁ - p₀) / ((sqrtLow (1 - p₀) : ℝ) + sqrtLow (1 - p₁)) :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcq (by norm_num)) (by linarith)) (by positivity)

/-- **The walk of the remainder** over `[0, e]`. -/
def shearRemainderWalk (ρ e : ℚ) : Option ℤ :=
  cellWalk (shearNextRow ρ) shearRemainderCell 1000000 0 e 0

/-- **Soundness of the walk of the remainder**: a walk value `N` bounds
`∫_{(0, e]} shearRemainderDensity` by `N/2^64`. For `e < 0` the interval is empty. -/
theorem lintegral_le_shearRemainderWalk {ρ e : ℚ} {N : ℤ}
    (h : shearRemainderWalk ρ e = some N) :
    ∫⁻ p in Ioc (0 : ℝ) e, ENNReal.ofReal (shearRemainderDensity p) ≤
      ENNReal.ofReal (N / 2 ^ 64) := by
  rcases lt_or_ge e 0 with he | he
  · rw [Ioc_eq_empty (not_lt.mpr (by exact_mod_cast he.le)), Measure.restrict_empty,
      lintegral_zero_measure]
    exact zero_le
  have := lintegral_le_of_cellWalk (F := fun p ↦ ENNReal.ofReal (shearRemainderDensity p))
    (g := fun x : ℚ ↦ (x : ℝ)) (K := 64)
    (fun a ha b hb hab ↦ by simp only; exact_mod_cast hab)
    (fun l u m hl hlu hm ↦ lintegral_le_shearRemainderCell hm) le_rfl he h
  simpa using this

/-- The end of the remainder: `∫_{1-δ}^1 G ≤ 2√6 δ^{1/2}`. -/
theorem lintegral_shearRemainderDensity_end_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫⁻ p in Ioo (1 - δ) 1, ENNReal.ofReal (shearRemainderDensity p) ≤
      ENNReal.ofReal (2 * Real.sqrt 6 * Real.sqrt δ) := by
  have hpt : ∀ p ∈ Ioc (1 - δ) 1, shearRemainderDensity p ≤ Real.sqrt 6 / Real.sqrt (1 - p) := by
    intro p hp
    rcases eq_or_lt_of_le hp.2 with h1 | h1
    · simp [shearRemainderDensity, h1]
    have hp0 : 0 ≤ p := by linarith [hp.1]
    have hu : 0 < 1 - p := by linarith
    have hsu := Real.sqrt_pos.2 hu
    have hsq : Real.sqrt (1 - p ^ 2) = Real.sqrt (1 - p) * Real.sqrt (1 + p) := by
      rw [← Real.sqrt_mul hu.le]
      ring_nf
    have hpp : p * Real.sqrt p ≤ 1 := by
      have : Real.sqrt p ≤ 1 := by rw [Real.sqrt_le_one]; linarith
      nlinarith [Real.sqrt_nonneg p]
    have h1p : 1 ≤ Real.sqrt (1 + p) := Real.le_sqrt_of_sq_le (by linarith)
    unfold shearRemainderDensity
    rw [hsq, div_le_div_iff₀ (by
      have : 0 < 4 - p ^ 2 := by nlinarith
      positivity) hsu]
    have h4 : 3 ≤ 4 - p ^ 2 := by nlinarith
    have h6 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
    calc 3 * Real.sqrt 6 * (p * Real.sqrt p) * Real.sqrt (1 - p)
        ≤ 3 * Real.sqrt 6 * 1 * Real.sqrt (1 - p) := by gcongr
      _ ≤ Real.sqrt 6 * ((4 - p ^ 2) * (Real.sqrt (1 - p) * Real.sqrt (1 + p))) := by
          have hA : 3 * Real.sqrt (1 - p) ≤ (4 - p ^ 2) * (Real.sqrt (1 - p) * Real.sqrt (1 + p)) :=
            mul_le_mul h4 (le_mul_of_one_le_right hsu.le h1p) hsu.le (by linarith)
          calc 3 * Real.sqrt 6 * 1 * Real.sqrt (1 - p) = Real.sqrt 6 * (3 * Real.sqrt (1 - p)) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hA h6
  calc ∫⁻ p in Ioo (1 - δ) 1, ENNReal.ofReal (shearRemainderDensity p)
      ≤ ∫⁻ p in Ioc (1 - δ) 1, ENNReal.ofReal (shearRemainderDensity p) :=
        lintegral_mono_set Ioo_subset_Ioc_self
    _ ≤ ∫⁻ p in Ioc (1 - δ) 1, ENNReal.ofReal (Real.sqrt 6 / Real.sqrt (1 - p)) :=
        setLIntegral_mono' measurableSet_Ioc fun p hp ↦ ENNReal.ofReal_le_ofReal (hpt p hp)
    _ = ENNReal.ofReal (-2 * Real.sqrt 6 * Real.sqrt (1 - 1) -
          -2 * Real.sqrt 6 * Real.sqrt (1 - (1 - δ))) := by
        rw [lintegral_Ioc_ofReal_deriv (g := fun p ↦ -2 * Real.sqrt 6 * Real.sqrt (1 - p))
          (by linarith) (by fun_prop) (fun p hp ↦ ?_) (fun p hp ↦ by positivity)]
        have hu : 0 < 1 - p := by linarith [hp.2]
        have hd : HasDerivAt (fun p ↦ 1 - p) (-1) p := by
          simpa using (hasDerivAt_id p).const_sub 1
        refine ((hd.sqrt hu.ne').const_mul (-2 * Real.sqrt 6)).congr_deriv ?_
        have hs := Real.sqrt_pos.2 hu
        field_simp
    _ = ENNReal.ofReal (2 * Real.sqrt 6 * Real.sqrt δ) := by
        congr 1
        simp only [sub_self, Real.sqrt_zero, mul_zero, sub_sub_cancel]
        ring

end IncompressibleFlow.SharpHolder
