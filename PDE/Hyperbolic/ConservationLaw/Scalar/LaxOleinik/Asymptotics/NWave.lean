/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Primitive.Integrable
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import CAS.ExactTactic

/-!
# The scalar N-wave and its lobe parameters

The two parameters are defined by the extrema of the datum's half-line
integrals. For an integrable datum supported almost everywhere in a bounded
interval, continuity and the two constant tails construct a point attaining
both extrema. Thus the profile parameters are determined by the datum.

The parameters `negativeLobeMass` and `positiveLobeMass` are `p` and `q` of (65) in Evans,
§3.4.5(b), and `nWave` is his N-wave (63) with `σ = F'(0)` (58) and `d = F''(0)` (64).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.5, equations (58) and (63)-(65).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis

namespace PDE.Hyperbolic.ConservationLaw.LaxOleinik

/-- Twice the negative of the minimum cumulative integral of the datum. -/
def negativeLobeMass (g : ℝ → ℝ) : ℝ :=
  -2 * sInf (range fun x : ℝ ↦ ∫ y in Iio x, g y)

/-- Twice the maximum remaining tail integral of the datum. -/
def positiveLobeMass (g : ℝ → ℝ) : ℝ :=
  2 * sSup (range fun x : ℝ ↦ ∫ y in Ioi x, g y)

/-- The N-wave determined by the datum and the flux's first two
derivatives at zero. The profile is zero at both fronts. -/
def nWave (F g : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  (Ioo (t * deriv F 0 - √(negativeLobeMass g * deriv (deriv F) 0 * t))
    (t * deriv F 0 + √(positiveLobeMass g * deriv (deriv F) 0 * t))).indicator
      (fun x ↦ (x / t - deriv F 0) / deriv (deriv F) 0)

/-- Every profile slice is integrable. In particular, its norm and its
difference from an integrable solution slice have nonvacuous real integrals. -/
theorem integrable_nWave (F g : ℝ → ℝ) (t : ℝ) :
    Integrable (nWave F g t) volume := by
  have hcont : Continuous (fun x : ℝ ↦ (x / t - deriv F 0) / deriv (deriv F) 0) :=
    ((continuous_id.div_const t).sub continuous_const).div_const _
  exact (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo

/-- The same point attains the defining minimum and maximum for the two
lobe parameters. It is constructed from integrability and support. -/
theorem exists_lobe_minimizer {g : ℝ → ℝ} (hg : Integrable g volume) {a b : ℝ} (hab : a ≤ b)
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc a b → g y = 0) :
    ∃ z ∈ Icc a b, (∫ y in Iio z, g y) = -negativeLobeMass g / 2 ∧
      (∫ y in Ioi z, g y) = positiveLobeMass g / 2 ∧
      ∀ x : ℝ, (∫ y in Iio z, g y) ≤ ∫ y in Iio x, g y := by
  obtain ⟨z, hz, hmin⟩ := exists_isMinOn_integral_Iio_of_ae_support_Icc hg hab hsupport
  have hsum (x : ℝ) : (∫ y in Iio x, g y) + (∫ y in Ioi x, g y) = ∫ y, g y := by
    simpa only [integral_Iic_eq_integral_Iio] using intervalIntegral.integral_Iic_add_Ioi
        (hg.integrableOn (s := Iic x)) (hg.integrableOn (s := Ioi x))
  have hleast : IsLeast (range fun x : ℝ ↦ ∫ y in Iio x, g y) (∫ y in Iio z, g y) :=
    ⟨⟨z, rfl⟩, by rintro _ ⟨x, rfl⟩; exact hmin x⟩
  have hgreatest : IsGreatest (range fun x : ℝ ↦ ∫ y in Ioi x, g y)
      (∫ y in Ioi z, g y) := by
    refine ⟨⟨z, rfl⟩, ?_⟩
    rintro _ ⟨x, rfl⟩
    have hx := hsum x
    have hzsum := hsum z
    have hxz := hmin x
    linarith
  refine ⟨z, hz, ?_, ?_, hmin⟩
  · rw [negativeLobeMass, hleast.csInf_eq]
    cas
  · rw [positiveLobeMass, hgreatest.csSup_eq]
    cas

/-- The difference between the lobe parameters is twice the total signed
mass of the datum. This follows from their attained extrema. -/
theorem positiveLobeMass_sub_negativeLobeMass {g : ℝ → ℝ} (hg : Integrable g volume) {a b : ℝ}
    (hab : a ≤ b) (hsupport : ∀ᵐ y ∂volume, y ∉ Icc a b → g y = 0) :
    positiveLobeMass g - negativeLobeMass g = 2 * ∫ y, g y := by
  obtain ⟨z, _, hp, hq, _⟩ := exists_lobe_minimizer hg hab hsupport
  have hsum := intervalIntegral.integral_Iic_add_Ioi
    (hg.integrableOn (s := Iic z)) (hg.integrableOn (s := Ioi z))
  rw [integral_Iic_eq_integral_Iio, hp, hq] at hsum
  linarith

/-- Compact support makes both lobe parameters nonnegative. Strict
positivity, when required for quantitative front localization, is separate. -/
theorem lobeMass_nonneg {g : ℝ → ℝ} (hg : Integrable g volume) {a b : ℝ} (hab : a ≤ b)
    (hsupport : ∀ᵐ y ∂volume, y ∉ Icc a b → g y = 0) :
    0 ≤ negativeLobeMass g ∧ 0 ≤ positiveLobeMass g := by
  obtain ⟨_, _, hp, _, hmin⟩ := exists_lobe_minimizer hg hab hsupport
  have ha := hmin a
  have hb := hmin b
  rw [hp, integral_Iio_eq_zero_of_ae_support_Icc hsupport le_rfl] at ha
  rw [hp, integral_Iio_eq_integral_of_ae_support_Icc hg hsupport le_rfl] at hb
  have hsum := positiveLobeMass_sub_negativeLobeMass hg hab hsupport
  constructor <;> linarith

/-- The N-wave written in spatial coordinates at positive squared time. -/
theorem nWave_sq_eq {F g : ℝ → ℝ} (hp : 0 ≤ negativeLobeMass g) (hq : 0 ≤ positiveLobeMass g)
    (hd : 0 < deriv (deriv F) 0) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    nWave F g (s ^ 2) x =
      (Ioo (deriv F 0 * s ^ 2 - √(negativeLobeMass g * deriv (deriv F) 0) * s)
        (deriv F 0 * s ^ 2 + √(positiveLobeMass g * deriv (deriv F) 0) * s)).indicator
        (fun x ↦ (x - deriv F 0 * s ^ 2) / (deriv (deriv F) 0 * s ^ 2)) x := by
  rw [nWave, Real.sqrt_mul (mul_nonneg hp hd.le),
    Real.sqrt_mul (mul_nonneg hq hd.le), Real.sqrt_sq hs.le, mul_comm (s ^ 2)]
  apply congrArg (fun f : ℝ → ℝ ↦ (Ioo _ _).indicator f x)
  funext y
  cas

/-- The N-wave height is bounded by a constant times the inverse square root of time. -/
theorem abs_nWave_sq_le {F g : ℝ → ℝ} (hp : 0 ≤ negativeLobeMass g) (hq : 0 ≤ positiveLobeMass g)
    (hd : 0 < deriv (deriv F) 0) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    |nWave F g (s ^ 2) x| ≤ (√(negativeLobeMass g * deriv (deriv F) 0) +
      √(positiveLobeMass g * deriv (deriv F) 0)) / (deriv (deriv F) 0 * s) := by
  let P := √(negativeLobeMass g * deriv (deriv F) 0)
  let Q := √(positiveLobeMass g * deriv (deriv F) 0)
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  rw [nWave_sq_eq hp hq hd hs]
  by_cases hx : x ∈ Ioo (deriv F 0 * s ^ 2 - P * s) (deriv F 0 * s ^ 2 + Q * s)
  · rw [indicator_of_mem hx, abs_div, abs_of_pos (mul_pos hd (sq_pos_of_pos hs))]
    have hxi : |x - deriv F 0 * s ^ 2| ≤ (P + Q) * s := by
      apply abs_le.mpr
      constructor <;> nlinarith [hx.1, hx.2]
    apply (div_le_iff₀ (mul_pos hd (sq_pos_of_pos hs))).2
    calc
      |x - deriv F 0 * s ^ 2| ≤ (P + Q) * s := hxi
      _ = (P + Q) / (deriv (deriv F) 0 * s) * (deriv (deriv F) 0 * s ^ 2) := by cas
  · rw [indicator_of_notMem hx, abs_zero]
    positivity

/-- An explicit bounded interval contains the support of each N-wave slice. -/
theorem nWave_sq_eq_zero_of_abs_gt {F g : ℝ → ℝ} (hp : 0 ≤ negativeLobeMass g)
    (hq : 0 ≤ positiveLobeMass g) (hd : 0 < deriv (deriv F) 0) {s : ℝ} (hs : 0 < s) {x : ℝ}
    (hx : |deriv F 0| * s ^ 2 + (√(negativeLobeMass g * deriv (deriv F) 0) +
      √(positiveLobeMass g * deriv (deriv F) 0)) * s < |x|) :
    nWave F g (s ^ 2) x = 0 := by
  let P := √(negativeLobeMass g * deriv (deriv F) 0)
  let Q := √(positiveLobeMass g * deriv (deriv F) 0)
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  rw [nWave_sq_eq hp hq hd hs]
  apply indicator_of_notMem
  intro hmem
  have hxi : |x - deriv F 0 * s ^ 2| ≤ (P + Q) * s := by
    apply abs_le.mpr
    constructor <;> nlinarith [hmem.1, hmem.2]
  have htriangle := abs_add_le (x - deriv F 0 * s ^ 2) (deriv F 0 * s ^ 2)
  rw [sub_add_cancel, abs_mul, abs_of_nonneg (sq_nonneg s)] at htriangle
  linarith

/-- At positive squared time the N-wave's `L¹` norm equals half the sum of its
lobe parameters. Both lobes are integrated directly. -/
theorem integral_abs_nWave_sq {F g : ℝ → ℝ} (hp : 0 ≤ negativeLobeMass g)
    (hq : 0 ≤ positiveLobeMass g) (hd : 0 < deriv (deriv F) 0) {s : ℝ} (hs : 0 < s) :
    (∫ x, |nWave F g (s ^ 2) x|) = (negativeLobeMass g + positiveLobeMass g) / 2 := by
  let d := deriv (deriv F) 0
  let c := deriv F 0 * s ^ 2
  let P := √(negativeLobeMass g * d)
  let Q := √(positiveLobeMass g * d)
  let a := c - P * s
  let b := c + Q * s
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := Real.sqrt_nonneg _
  have hP2 : P ^ 2 = negativeLobeMass g * d := Real.sq_sqrt (mul_nonneg hp hd.le)
  have hQ2 : Q ^ 2 = positiveLobeMass g * d := Real.sq_sqrt (mul_nonneg hq hd.le)
  have hac : a ≤ c := by dsimp [a]; linarith [mul_nonneg hP hs.le]
  have hcb : c ≤ b := by dsimp [b]; linarith [mul_nonneg hQ hs.le]
  have hab : a ≤ b := hac.trans hcb
  have hpoint (x : ℝ) : |nWave F g (s ^ 2) x| =
      (Ioo a b).indicator (fun x ↦ |x - c| / (d * s ^ 2)) x := by
    rw [nWave_sq_eq hp hq hd hs]
    by_cases hx : x ∈ Ioo a b
    · rw [indicator_of_mem hx, indicator_of_mem hx, abs_div,
        abs_of_pos (mul_pos hd (sq_pos_of_pos hs))]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, abs_zero]
  have hcont : Continuous (fun x : ℝ ↦ |x - c|) := (continuous_id.sub continuous_const).abs
  have hleft : (∫ x in a..c, |x - c|) = (a - c) ^ 2 / 2 := by
    have h := integral_pow_abs_sub_uIoc (a := c) (b := a) (n := 1)
    simpa only [pow_one, Nat.cast_one, Nat.cast_add, one_add_one_eq_two, sq_abs,
      uIoc_of_ge hac, ← intervalIntegral.integral_of_le hac] using h
  have hright : (∫ x in c..b, |x - c|) = (b - c) ^ 2 / 2 := by
    have h := integral_pow_abs_sub_uIoc (a := c) (b := b) (n := 1)
    simpa only [pow_one, Nat.cast_one, Nat.cast_add, one_add_one_eq_two, sq_abs,
      uIoc_of_le hcb, ← intervalIntegral.integral_of_le hcb] using h
  simp_rw [hpoint]
  rw [integral_indicator measurableSet_Ioo, integral_div,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable a c) (hcont.intervalIntegrable c b), hleft, hright]
  have heq : ((a - c) ^ 2 / 2 + (b - c) ^ 2 / 2) / (d * s ^ 2) =
      (P ^ 2 + Q ^ 2) / (2 * d) := by dsimp [a, b]; cas
  rw [heq, hP2, hQ2]
  cas

/-- The `L¹` norm of the N-wave is `(p + q) / 2` at every positive time. -/
theorem integral_abs_nWave {F g : ℝ → ℝ} (hp : 0 ≤ negativeLobeMass g) (hq : 0 ≤ positiveLobeMass g)
    (hd : 0 < deriv (deriv F) 0) {t : ℝ} (ht : 0 < t) :
    (∫ x, |nWave F g t x|) = (negativeLobeMass g + positiveLobeMass g) / 2 := by
  have h := integral_abs_nWave_sq hp hq hd (Real.sqrt_pos.mpr ht)
  simpa only [Real.sq_sqrt ht.le] using h

end PDE.Hyperbolic.ConservationLaw.LaxOleinik
