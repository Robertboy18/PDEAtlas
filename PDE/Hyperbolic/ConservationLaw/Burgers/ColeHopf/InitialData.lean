/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import CAS.ExactTactic

/-!
# Initial data for the Cole–Hopf Cauchy construction

For a bounded continuous Burgers datum `u₀` and viscosity `ν > 0`, the transformed
datum is `exp (-∫₀ˣ u₀ / (2ν))`. It is positive and continuously differentiable,
but need not be bounded. Dividing by `exp (Lx) + exp (-Lx)`, where
`L = ‖u₀‖∞ / (2ν)`, gives a bounded positive amplitude with bounded derivative.
This allows the heat construction to use exponential tilts of bounded data.

With `a = ν`, the datum `exp (-∫₀ˣ u₀ / (2ν))` is the heat datum `e^{-h/(2a)}` in formula (9)
of Evans, §4.4.1(b). Evans takes the primitive `h` of (7) from `-∞`; we integrate from `0`, which
multiplies the heat solution by a constant and leaves the velocity unchanged.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.1(b), equations (7)-(9).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace BurgersEquation.ColeHopf

/-- The positive datum obtained by exponentiating the primitive of the Burgers datum. -/
def initialPotential (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(∫ s in (0 : ℝ)..x, u₀ s) / (2 * ν))

/-- The exponential growth rate controlled by the initial uniform bound. -/
def initialGrowthRate (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) : ℝ := ‖u₀‖ / (2 * ν)

/-- The two-sided exponential envelope used to produce bounded heat data. -/
def exponentialEnvelope (L x : ℝ) : ℝ := Real.exp (L * x) + Real.exp (-L * x)

/-- The bounded amplitude shared by the two exponential tilts. -/
def initialAmplitude (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) : ℝ :=
  initialPotential ν u₀ x / exponentialEnvelope (initialGrowthRate ν u₀) x

/-- Exponentiation makes the transformed initial datum strictly positive. -/
theorem initialPotential_pos (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    0 < initialPotential ν u₀ x := Real.exp_pos _

/-- The transformed datum has the derivative required to recover the Burgers datum. -/
theorem hasDerivAt_initialPotential (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    HasDerivAt (initialPotential ν u₀)
      (-(u₀ x / (2 * ν)) * initialPotential ν u₀ x) x := by
  have hp := intervalIntegral.integral_hasDerivAt_right (u₀.continuous.intervalIntegrable 0 x)
    u₀.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter u₀.continuous.continuousAt
  unfold initialPotential
  simpa only [Pi.neg_apply, neg_div, mul_comm] using (hp.neg.div_const (2 * ν)).exp

/-- The transformed datum is continuous for every viscosity parameter. -/
theorem continuous_initialPotential (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) :
    Continuous (initialPotential ν u₀) :=
  continuous_iff_continuousAt.mpr fun x ↦ (hasDerivAt_initialPotential ν u₀ x).continuousAt

/-- Positive viscosity makes the growth rate nonnegative. -/
theorem initialGrowthRate_nonneg {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) :
    0 ≤ initialGrowthRate ν u₀ := div_nonneg (norm_nonneg _) (by positivity)

/-- The primitive estimate gives a two-sided exponential growth bound. -/
theorem initialPotential_le_exp_abs {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    initialPotential ν u₀ x ≤ Real.exp (initialGrowthRate ν u₀ * |x|) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := x) (fun s _ ↦ u₀.norm_coe_le_norm s)
  simp only [sub_zero, Real.norm_eq_abs] at hi
  apply Real.exp_le_exp.mpr
  change -(∫ s in (0 : ℝ)..x, u₀ s) / (2 * ν) ≤ ‖u₀‖ / (2 * ν) * |x|
  calc
    _ ≤ |∫ s in (0 : ℝ)..x, u₀ s| / (2 * ν) :=
      div_le_div_of_nonneg_right (neg_le_abs _) (by positivity)
    _ ≤ ‖u₀‖ * |x| / (2 * ν) :=
      div_le_div_of_nonneg_right hi (by positivity)
    _ = _ := by cas

/-- The envelope is strictly positive, so its quotient never divides by zero. -/
theorem exponentialEnvelope_pos (L x : ℝ) : 0 < exponentialEnvelope L x :=
  add_pos (Real.exp_pos _) (Real.exp_pos _)

/-- The exponential of the absolute value is controlled by the two-sided envelope. -/
theorem exp_mul_abs_le_exponentialEnvelope (L x : ℝ) :
    Real.exp (L * |x|) ≤ exponentialEnvelope L x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_pos _).le
  · rw [abs_of_nonpos hx, mul_neg, ← neg_mul]
    exact le_add_of_nonneg_left (Real.exp_pos _).le

/-- The bounded amplitude is still strictly positive. -/
theorem initialAmplitude_pos (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    0 < initialAmplitude ν u₀ x :=
  div_pos (initialPotential_pos ν u₀ x) (exponentialEnvelope_pos _ _)

/-- The normalized amplitude lies below one for every bounded continuous datum. -/
theorem initialAmplitude_le_one {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    initialAmplitude ν u₀ x ≤ 1 := by
  apply (div_le_one (exponentialEnvelope_pos _ _)).mpr
  exact (initialPotential_le_exp_abs hν u₀ x).trans (exp_mul_abs_le_exponentialEnvelope _ _)

/-- The exponential datum is the sum of two tilted copies of the bounded amplitude. -/
theorem initialPotential_eq_tilted_amplitude (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    initialPotential ν u₀ x = Real.exp (initialGrowthRate ν u₀ * x) * initialAmplitude ν u₀ x +
      Real.exp (-initialGrowthRate ν u₀ * x) * initialAmplitude ν u₀ x := by
  rw [← add_mul]
  exact (mul_div_cancel₀ _ (exponentialEnvelope_pos _ _).ne').symm

/-- The derivative of the two-sided exponential envelope. -/
theorem hasDerivAt_exponentialEnvelope (L x : ℝ) :
    HasDerivAt (exponentialEnvelope L) (L * (Real.exp (L * x) - Real.exp (-L * x))) x := by
  unfold exponentialEnvelope
  cas

/-- The bounded amplitude is continuous. -/
theorem continuous_initialAmplitude (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) :
    Continuous (initialAmplitude ν u₀) :=
  (continuous_initialPotential ν u₀).div
    (by unfold exponentialEnvelope; fun_prop) (fun x ↦ (exponentialEnvelope_pos _ x).ne')

/-- The quotient rule expresses the derivative using the bounded amplitude itself. -/
theorem hasDerivAt_initialAmplitude (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    HasDerivAt (initialAmplitude ν u₀)
      ((-(u₀ x / (2 * ν)) -
        initialGrowthRate ν u₀ *
          (Real.exp (initialGrowthRate ν u₀ * x) - Real.exp (-initialGrowthRate ν u₀ * x)) /
            exponentialEnvelope (initialGrowthRate ν u₀) x) *
        initialAmplitude ν u₀ x) x := by
  have hden := (exponentialEnvelope_pos (initialGrowthRate ν u₀) x).ne'
  convert (hasDerivAt_initialPotential ν u₀ x).div
    (hasDerivAt_exponentialEnvelope (initialGrowthRate ν u₀) x) hden using 1
  · rfl
  · unfold initialAmplitude
    cas using hden

/-- The derivative is continuous even when the Burgers datum has no derivative. -/
theorem contDiff_initialAmplitude (ν : ℝ) (u₀ : ℝ →ᵇ ℝ) :
    ContDiff ℝ 1 (initialAmplitude ν u₀) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_initialAmplitude ν u₀ x).differentiableAt, ?_⟩
  have heq := funext fun x ↦ (hasDerivAt_initialAmplitude ν u₀ x).deriv
  rw [heq]
  apply Continuous.mul _ (continuous_initialAmplitude ν u₀)
  apply Continuous.sub ((u₀.continuous.div_const _).neg)
  apply Continuous.div
  · fun_prop
  · unfold exponentialEnvelope
    fun_prop
  · exact fun x ↦ (exponentialEnvelope_pos _ x).ne'

/-- The amplitude derivative has a uniform bound determined by the initial velocity bound. -/
theorem abs_deriv_initialAmplitude_le {ν : ℝ} (hν : 0 < ν) (u₀ : ℝ →ᵇ ℝ) (x : ℝ) :
    |deriv (initialAmplitude ν u₀) x| ≤ 2 * initialGrowthRate ν u₀ := by
  let L := initialGrowthRate ν u₀
  have hL : 0 ≤ L := initialGrowthRate_nonneg hν u₀
  have hu : |u₀ x / (2 * ν)| ≤ L := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * ν)]
    exact div_le_div_of_nonneg_right (u₀.norm_coe_le_norm x) (by positivity)
  have hden : |L * (Real.exp (L * x) - Real.exp (-L * x)) /
      exponentialEnvelope L x| ≤ L := by
    rw [abs_div, abs_mul, abs_of_nonneg hL,
      abs_of_pos (exponentialEnvelope_pos L x), div_le_iff₀ (exponentialEnvelope_pos L x)]
    apply mul_le_mul_of_nonneg_left _ hL
    simpa only [exponentialEnvelope, abs_of_pos (Real.exp_pos _)] using
      abs_sub (Real.exp (L * x)) (Real.exp (-L * x))
  rw [(hasDerivAt_initialAmplitude ν u₀ x).deriv, abs_mul, abs_of_pos (initialAmplitude_pos ν u₀ x)]
  have hcoef : |-(u₀ x / (2 * ν)) -
      L * (Real.exp (L * x) - Real.exp (-L * x)) / exponentialEnvelope L x| ≤ 2 * L := by
    calc
      _ ≤ |-(u₀ x / (2 * ν))| +
          |L * (Real.exp (L * x) - Real.exp (-L * x)) / exponentialEnvelope L x| := abs_sub _ _
      _ ≤ L + L := add_le_add (by simpa only [abs_neg] using hu) hden
      _ = _ := by cas
  exact (mul_le_mul_of_nonneg_right hcoef (initialAmplitude_pos ν u₀ x).le).trans
    (mul_le_of_le_one_right (by positivity) (initialAmplitude_le_one hν u₀ x))

end BurgersEquation.ColeHopf
