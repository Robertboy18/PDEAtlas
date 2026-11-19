/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainVertical
public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainMapBounds
public import PDE.Analysis.Integration.CellSums

/-!
# Cell bounds of the cross integral of the vertical Hölder estimate of the strain

By `strainCrossConstant_eq`, the constant of the vertical Hölder estimate of the strain is
`C₂(a) = (√2/π) ∫_0^a p^{1/2} 2Φ_p(f(p)) dp`, with
`2Φ_p(t) = 2 p t / (((t - 1/2)² + p²) ((t + 1/2)² + p²))` and `f` the threshold of the strain
map. We bound the integrand `crossIntegrand p = p^{1/2} 2Φ_p(f(p))` near zero, at infinity and on
cells; the bounds near zero and at infinity are those of Chen and Hou, Part II, Supplementary
material II, Section 5.3.3:

* on `(0, r]`, `2Φ_p(f(p)) ≤ 1/p`, so the integral is at most `2 r^{1/2}`;
* on `(R, ∞)`, `2Φ_p(f(p)) ≤ 1/p²`, so the integral is at most `2 R^{-1/2}`;
* on a cell `(w², w'²]` the integrand is at most
  `w' · 2 u f⁺ / (((f⁻ - 1/2)² + l²)((f⁻ + 1/2)² + l²))`, where `l = w²`, `u = w'²` and
  `f⁻ ≤ f(l) ≤ f(u) ≤ f⁺` are rationals certified by the sign of the quartic `Δ₁`
  (`strainQuartic_pos_iff`, `strainQuartic_neg_iff`; `f` is monotone). The cell test
  `crossCellOk` and the integer cell bound `crossCellBound` are computable.

A walk over about `1.3 · 10⁵` cells between `2^-34` and `2^34` would give the numerical value
`C₂(a) ≤ 4.26/π` of Chen and Hou, Part I, Lemma 3.3; such a walk is too expensive to check in the
kernel within the build budget of the library and is not part of it.

## Main definitions

* `crossIntegrand`: the integrand `p^{1/2} 2Φ_p(f(p))`.
* `crossCellOk`, `crossCellValue`, `crossCellBound`, `crossCell`: the computable cell test and
  cell bound.

## Main results

* `two_mul_strainPotential_le_inv`, `two_mul_strainPotential_le_inv_sq`: the potential is at most
  `1/p` and `1/p²`.
* `rpow_mul_two_mul_strainPotential_le`: the pointwise bound on a cell.
* `lintegral_crossIntegrand_cell`: soundness of the cell test.
* `lintegral_Ioc_crossIntegrand_le`, `lintegral_Ioi_crossIntegrand_le`: the integral near zero and
  at infinity.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 3.3, p. 28.
  <https://arxiv.org/abs/2210.07191v4>
* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary material II,
  Section 5.3.3, (5.37)-(5.39), pp. 11-12.
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped ENNReal

namespace IncompressibleFlow.SharpHolder

/-! ### Pointwise bounds of the integrand -/

/-- `2 Φ_p(t) = 2 p t / (((t - 1/2)² + p²) ((t + 1/2)² + p²))` for `p ≠ 0`. -/
theorem two_mul_strainPotential_eq {p : ℝ} (hp : p ≠ 0) (t : ℝ) :
    2 * strainPotential p t =
      2 * p * t / (((t - 1 / 2) ^ 2 + p ^ 2) * ((t + 1 / 2) ^ 2 + p ^ 2)) := by
  have h₁ : (t - 1 / 2) ^ 2 + p ^ 2 ≠ 0 := by positivity
  have h₂ : (t + 1 / 2) ^ 2 + p ^ 2 ≠ 0 := by positivity
  rw [strainPotential_eq]
  field_simp
  ring

/-- `2 Φ_p(f(p)) ≤ 1/p` for `p > 0`. -/
theorem two_mul_strainPotential_le_inv {p : ℝ} (hp : 0 < p) :
    2 * strainPotential p (strainThreshold p) ≤ 1 / p := by
  set t := strainThreshold p
  have ht : 1 / 2 ≤ t := one_half_le_strainThreshold p
  rw [two_mul_strainPotential_eq hp.ne', div_le_div_iff₀ (by positivity) hp]
  have h₁ : p ^ 2 ≤ (t - 1 / 2) ^ 2 + p ^ 2 := by nlinarith
  have h₂ : 2 * t ≤ (t + 1 / 2) ^ 2 + p ^ 2 := by nlinarith [sq_nonneg (t - 1 / 2)]
  have := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  nlinarith

/-- `2 Φ_p(f(p)) ≤ 1/p²` for `p > 0`. -/
theorem two_mul_strainPotential_le_inv_sq {p : ℝ} (hp : 0 < p) :
    2 * strainPotential p (strainThreshold p) ≤ 1 / p ^ 2 := by
  set t := strainThreshold p
  have ht : 1 / 2 ≤ t := one_half_le_strainThreshold p
  rw [two_mul_strainPotential_eq hp.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have h₁ : p ^ 2 ≤ (t - 1 / 2) ^ 2 + p ^ 2 := by nlinarith
  have h₂ : 2 * t * p ≤ (t + 1 / 2) ^ 2 + p ^ 2 := by nlinarith [sq_nonneg (t + 1 / 2 - p)]
  have := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  nlinarith

/-- **The cell bound.** For `0 < l ≤ p ≤ u ≤ w²`, `w ≥ 0`, and rationals with
`1/2 ≤ f⁻ ≤ f(l)` and `f(u) ≤ f⁺`:
`p^{1/2} 2Φ_p(f(p)) ≤ w · 2 u f⁺ / (((f⁻ - 1/2)² + l²)((f⁻ + 1/2)² + l²))`. -/
theorem rpow_mul_two_mul_strainPotential_le {l u p w fl fu : ℝ} (hl : 0 < l) (hlp : l ≤ p)
    (hpu : p ≤ u) (hw : 0 ≤ w) (huw : u ≤ w ^ 2) (hfl : 1 / 2 ≤ fl)
    (hfl' : fl ≤ strainThreshold l) (hfu : strainThreshold u ≤ fu) :
    p ^ (1 / 2 : ℝ) * (2 * strainPotential p (strainThreshold p)) ≤
      w * (2 * u * fu / (((fl - 1 / 2) ^ 2 + l ^ 2) * ((fl + 1 / 2) ^ 2 + l ^ 2))) := by
  have hp : 0 < p := hl.trans_le hlp
  set t := strainThreshold p
  have htl : fl ≤ t := hfl'.trans (monotoneOn_strainThreshold (show l ∈ Ici 0 from hl.le)
    (show p ∈ Ici 0 from hp.le) hlp)
  have htu : t ≤ fu := (monotoneOn_strainThreshold (show (0:ℝ) ≤ p from hp.le)
    (show (0:ℝ) ≤ u from (hp.trans_le hpu).le) hpu).trans hfu
  have hsq : p ^ (1 / 2 : ℝ) ≤ w := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt p ≤ Real.sqrt (w ^ 2) := Real.sqrt_le_sqrt (hpu.trans huw)
      _ = w := Real.sqrt_sq hw
  have hΦ : 0 ≤ 2 * strainPotential p t := by
    rw [two_mul_strainPotential_eq hp.ne']
    have : 0 < t := lt_of_lt_of_le (by norm_num) (hfl.trans htl)
    positivity
  have hbound : 2 * strainPotential p t ≤
      2 * u * fu / (((fl - 1 / 2) ^ 2 + l ^ 2) * ((fl + 1 / 2) ^ 2 + l ^ 2)) := by
    rw [two_mul_strainPotential_eq hp.ne']
    have ht0 : 0 ≤ t := by linarith
    refine div_le_div₀ (by nlinarith) (by nlinarith) (by positivity) ?_
    have h₁ : (fl - 1 / 2) ^ 2 + l ^ 2 ≤ (t - 1 / 2) ^ 2 + p ^ 2 := by nlinarith
    have h₂ : (fl + 1 / 2) ^ 2 + l ^ 2 ≤ (t + 1 / 2) ^ 2 + p ^ 2 := by nlinarith
    exact mul_le_mul h₁ h₂ (by positivity) (by positivity)
  calc p ^ (1 / 2 : ℝ) * (2 * strainPotential p t) ≤ w * (2 * strainPotential p t) :=
        mul_le_mul_of_nonneg_right hsq hΦ
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hw

/-! ### The cell certificate -/

/-- The cell test on `(w², w'²]`: `w > 0`, the lower bound of `f(w²)` is `1/2` or below the root of
`Δ₁(·, w²)`, and the upper bound of `f(w'²)` is nonnegative and above the root of `Δ₁(·, w'²)`. -/
def crossCellOk (w w' : ℚ) : Bool :=
  let fl := thresholdLow (w ^ 2)
  let fu := thresholdGuess true (w' ^ 2)
  decide (0 < w) && (decide (fl ≤ 1 / 2) || decide (0 < strainQuarticRat fl (w ^ 2))) &&
    decide (0 ≤ fu) && decide (strainQuarticRat fu (w' ^ 2) < 0)

/-- The rational cell bound `(u - l) w' 2 u f⁺ / (((f⁻ - 1/2)² + l²)((f⁻ + 1/2)² + l²))`. -/
def crossCellValue (w w' : ℚ) : ℚ :=
  let l := w ^ 2
  let u := w' ^ 2
  let fl := thresholdLow l
  let fu := thresholdGuess true u
  (u - l) * (w' * (2 * u * fu / (((fl - 1 / 2) ^ 2 + l ^ 2) * ((fl + 1 / 2) ^ 2 + l ^ 2))))

/-- The integer cell bound on the grid `2^-64`. -/
def crossCellBound (w w' : ℚ) : ℤ := ceilScaled 64 (crossCellValue w w')

/-- The cell of the walk: its bound if its test passes. -/
def crossCell (w w' : ℚ) : Option ℤ :=
  if crossCellOk w w' then some (crossCellBound w w') else none

/-- The integrand of `strainCrossConstant_eq`. -/
def crossIntegrand (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (p ^ (1 / 2 : ℝ)) * ENNReal.ofReal (2 * strainPotential p (strainThreshold p))

/-- For `p > 0` the integrand is at most the real number `p^{1/2} 2Φ_p(f(p))`. -/
theorem crossIntegrand_le {p : ℝ} (hp : 0 < p) :
    crossIntegrand p ≤ ENNReal.ofReal (p ^ (1 / 2 : ℝ) * (2 * strainPotential p
      (strainThreshold p))) := by
  rw [crossIntegrand, ← ENNReal.ofReal_mul (by positivity)]

/-- **Soundness of one cell.** -/
theorem lintegral_crossIntegrand_cell {w w' : ℚ} (hw : 0 ≤ w) (hww : w < w')
    (h : crossCellOk w w' = true) :
    ∫⁻ p in Ioc ((w : ℝ) ^ 2) ((w' : ℝ) ^ 2), crossIntegrand p ≤
      ENNReal.ofReal (crossCellBound w w' / 2 ^ 64) := by
  simp only [crossCellOk, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hw0, hfl⟩, hfu0⟩, hfu⟩ := h
  set l : ℚ := w ^ 2
  set u : ℚ := w' ^ 2
  set fl := thresholdLow l
  set fu := thresholdGuess true u
  have hl : (0 : ℝ) < l := by simp only [l]; push_cast; positivity
  have hflh : (1 / 2 : ℝ) ≤ fl := by
    have h' : ((1 / 2 : ℚ) : ℝ) ≤ (fl : ℝ) := Rat.cast_le.2 (le_max_left _ _)
    simpa using h'
  have hfl' : (fl : ℝ) ≤ strainThreshold l := by
    rcases hfl with h | h
    · have h' : (fl : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.2 h
      have h'' : (fl : ℝ) ≤ 1 / 2 := by simpa using h'
      exact h''.trans (one_half_le_strainThreshold _)
    · have h' : (0 : ℝ) < strainQuartic fl l := by
        rw [← cast_strainQuarticRat]; exact_mod_cast h
      exact ((strainQuartic_pos_iff (by linarith) _).1 h').le
  have hfu' : strainThreshold u ≤ (fu : ℝ) := by
    have h' : strainQuartic fu u < 0 := by
      rw [← cast_strainQuarticRat]; exact_mod_cast hfu
    exact ((strainQuartic_neg_iff (by exact_mod_cast hfu0) _).1 h').le
  set c : ℝ := (w' : ℝ) * (2 * u * fu / (((fl - 1 / 2) ^ 2 + l ^ 2) * ((fl + 1 / 2) ^ 2 + l ^ 2)))
  have hcell : ∀ p ∈ Ioc ((w : ℝ) ^ 2) ((w' : ℝ) ^ 2), crossIntegrand p ≤ ENNReal.ofReal c := by
    intro p hp
    have hlp : (l : ℝ) ≤ p := by simp only [l]; push_cast; exact hp.1.le
    have hpu : p ≤ (u : ℝ) := by simp only [u]; push_cast; exact hp.2
    refine (crossIntegrand_le (hl.trans_le hlp)).trans (ENNReal.ofReal_le_ofReal ?_)
    exact rpow_mul_two_mul_strainPotential_le hl hlp hpu (by exact_mod_cast (hw.trans hww.le))
      (by simp only [u]; push_cast; exact le_rfl) hflh hfl' hfu'
  calc ∫⁻ p in Ioc ((w : ℝ) ^ 2) ((w' : ℝ) ^ 2), crossIntegrand p
      ≤ ∫⁻ _ in Ioc ((w : ℝ) ^ 2) ((w' : ℝ) ^ 2), ENNReal.ofReal c :=
        setLIntegral_mono measurable_const hcell
    _ = ENNReal.ofReal c * ENNReal.ofReal ((w' : ℝ) ^ 2 - (w : ℝ) ^ 2) := by
        rw [setLIntegral_const, Real.volume_Ioc]
    _ = ENNReal.ofReal (crossCellValue w w') := by
        have hfu0' : (0 : ℝ) < fu :=
          lt_of_lt_of_le (by norm_num) ((one_half_le_strainThreshold (u : ℝ)).trans hfu')
        have hw'0 : (0 : ℝ) ≤ w' := by exact_mod_cast (hw.trans hww.le)
        rw [← ENNReal.ofReal_mul (by simp only [c]; positivity)]
        congr 1
        simp only [crossCellValue, c, l, u, fl, fu]
        push_cast
        ring
    _ ≤ ENNReal.ofReal (crossCellBound w w' / 2 ^ 64) :=
        ENNReal.ofReal_le_ofReal (le_ceilScaled_real 64 _)

/-! ### The tails -/

/-- Near zero: `crossIntegrand p ≤ p^{-1/2}`, from `2Φ_p ≤ 1/p`. -/
theorem crossIntegrand_le_rpow {p : ℝ} (hp : 0 < p) :
    crossIntegrand p ≤ ENNReal.ofReal (p ^ (-1 / 2 : ℝ)) := by
  refine (crossIntegrand_le hp).trans (ENNReal.ofReal_le_ofReal ?_)
  calc p ^ (1 / 2 : ℝ) * (2 * strainPotential p (strainThreshold p)) ≤ p ^ (1 / 2 : ℝ) * (1 / p) :=
        mul_le_mul_of_nonneg_left (two_mul_strainPotential_le_inv hp) (by positivity)
    _ = p ^ (-1 / 2 : ℝ) := by
        rw [mul_one_div, ← Real.rpow_sub_one hp.ne']
        norm_num

/-- At infinity: `crossIntegrand p ≤ p^{-3/2}`, from `2Φ_p ≤ 1/p²`. -/
theorem crossIntegrand_le_rpow_three_halves {p : ℝ} (hp : 0 < p) :
    crossIntegrand p ≤ ENNReal.ofReal (p ^ (-3 / 2 : ℝ)) := by
  refine (crossIntegrand_le hp).trans (ENNReal.ofReal_le_ofReal ?_)
  calc p ^ (1 / 2 : ℝ) * (2 * strainPotential p (strainThreshold p)) ≤
        p ^ (1 / 2 : ℝ) * (1 / p ^ 2) :=
        mul_le_mul_of_nonneg_left (two_mul_strainPotential_le_inv_sq hp) (by positivity)
    _ = p ^ (-3 / 2 : ℝ) := by
        rw [mul_one_div, ← Real.rpow_natCast, ← Real.rpow_sub hp]
        norm_num

/-- Near `0`: `∫_0^{r²} p^{1/2} 2Φ_p(f(p)) dp ≤ 2 r` for `r > 0`. -/
theorem lintegral_Ioc_crossIntegrand_le {r : ℝ} (hr : 0 < r) :
    ∫⁻ p in Ioc 0 (r ^ 2), crossIntegrand p ≤ ENNReal.ofReal (2 * r) := by
  have hint : IntervalIntegrable (fun p : ℝ ↦ p ^ (-1 / 2 : ℝ)) volume 0 (r ^ 2) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hval : ∫ p in (0 : ℝ)..(r ^ 2), p ^ (-1 / 2 : ℝ) = 2 * r := by
    rw [integral_rpow (Or.inl (by norm_num))]
    rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, Real.zero_rpow (by norm_num), sub_zero,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq hr.le]
    ring
  calc ∫⁻ p in Ioc 0 (r ^ 2), crossIntegrand p
      ≤ ∫⁻ p in Ioc 0 (r ^ 2), ENNReal.ofReal (p ^ (-1 / 2 : ℝ)) :=
        setLIntegral_mono' measurableSet_Ioc fun p hp ↦ crossIntegrand_le_rpow hp.1
    _ = ENNReal.ofReal (∫ p in Ioc 0 (r ^ 2), p ^ (-1 / 2 : ℝ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 hint)
          ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun p hp ↦
            Real.rpow_nonneg hp.1.le _))]
    _ = ENNReal.ofReal (2 * r) := by
        rw [← intervalIntegral.integral_of_le (by positivity), hval]

/-- At infinity: `∫_{R²}^∞ p^{1/2} 2Φ_p(f(p)) dp ≤ 2 / R` for `R > 0`. -/
theorem lintegral_Ioi_crossIntegrand_le {R : ℝ} (hR : 0 < R) :
    ∫⁻ p in Ioi (R ^ 2), crossIntegrand p ≤ ENNReal.ofReal (2 / R) := by
  have hR2 : 0 < R ^ 2 := by positivity
  calc ∫⁻ p in Ioi (R ^ 2), crossIntegrand p
      ≤ ∫⁻ p in Ioi (R ^ 2), ENNReal.ofReal (p ^ (-3 / 2 : ℝ)) :=
        setLIntegral_mono' measurableSet_Ioi fun p hp ↦
          crossIntegrand_le_rpow_three_halves (hR2.trans hp)
    _ = ENNReal.ofReal (∫ p in Ioi (R ^ 2), p ^ (-3 / 2 : ℝ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) hR2)
          ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun p hp ↦
            Real.rpow_nonneg (hR2.trans hp).le _))]
    _ = ENNReal.ofReal (2 / R) := by
        rw [integral_Ioi_rpow_of_lt (by norm_num) hR2]
        congr 1
        rw [show (-3 / 2 : ℝ) + 1 = -(1 / 2) by norm_num, Real.rpow_neg hR2.le,
          ← Real.sqrt_eq_rpow, Real.sqrt_sq hR.le]
        field_simp

end IncompressibleFlow.SharpHolder
