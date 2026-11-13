/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.SignedPower
public import PDE.Analysis.MeasureTheory.LpNorm
import CAS.ExactTactic

/-!
# Explicit norming densities for mixed Lebesgue spaces

The spatial signed power is scaled to prescribe its outer norm growth. At conjugate
mixed exponents it pairs with its input to give the exact norm power. This proves
norm bounds from tests against mixed Lebesgue classes, without a dual representation
assumption. All comparisons use the actual almost-everywhere quotient representatives.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- Rescale the spatial odd power to have the prescribed norm growth. This is
the spatial component of the norming density for mixed Lebesgue spaces. -/
noncomputable def normScaledSignedPower {p q : ℝ≥0∞} {r : ℝ}
    (hr : 0 < r) (hq : p / ENNReal.ofReal r = q) (s : ℝ) (u : Lp ℝ p ν) : Lp ℝ q ν :=
  ‖u‖ ^ (s - r) • superposition (fun _ ↦ Real.signedPower r) (memLp_signedPower hr hq) u

/-- The rescaled odd power has norm exactly equal to the chosen power of the input norm. -/
theorem norm_normScaledSignedPower {p q : ℝ≥0∞} {r s : ℝ}
    (hr : 0 < r) (hq : p / ENNReal.ofReal r = q) (hs : 0 < s) (u : Lp ℝ p ν) :
    ‖normScaledSignedPower hr hq s u‖ = ‖u‖ ^ s := by
  have hu0 : 0 ≤ ‖u‖ := ENNReal.toReal_nonneg
  let J := superposition (fun _ ↦ Real.signedPower r) (memLp_signedPower hr hq) u
  change ‖‖u‖ ^ (s - r) • J‖ = _
  rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_smul (‖u‖ ^ (s - r)) J),
    eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm]
  change ‖‖u‖ ^ (s - r)‖ * ‖J‖ = _
  rw [norm_superposition_signedPower hr hq,
    Real.norm_of_nonneg (Real.rpow_nonneg hu0 _)]
  by_cases hu : ‖u‖ = 0
  · simp only [hu, Real.zero_rpow hr.ne', Real.zero_rpow hs.ne', mul_zero]
  · have hu' : 0 < ‖u‖ := lt_of_le_of_ne hu0 (Ne.symm hu)
    generalize ‖u‖ = a at hu' ⊢
    cas using hu'

/-- Actual almost-everywhere strong measurability of the spatial norming map.
The scalar normalization may have a negative exponent; measurability suffices. -/
theorem aestronglyMeasurable_normScaledSignedPower {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] {r s : ℝ}
    (hp : p ≠ ∞) (hr : 0 < r) (hq : p / ENNReal.ofReal r = q)
    {u : α → Lp ℝ p ν} (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable (fun t ↦ normScaledSignedPower hr hq s (u t)) μ :=
  ((hu.norm.aemeasurable.pow_const (s - r)).aestronglyMeasurable).smul
    ((continuous_superposition_signedPower hp hr hq).comp_aestronglyMeasurable hu)

/-- The spatial norming map sends a mixed Lebesgue function to the mixed space
with both exponents divided by their respective powers. -/
theorem memLp_normScaledSignedPower {p q b c : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] {r s : ℝ}
    (hp : p ≠ ∞) (hr : 0 < r) (hq : p / ENNReal.ofReal r = q)
    (hs : 0 < s) (hc : b / ENNReal.ofReal s = c) (u : Lp (Lp ℝ p ν) b μ) :
    MemLp (fun t ↦ normScaledSignedPower hr hq s (u t)) c μ := by
  have hpow : MemLp (fun t ↦ ‖u t‖ ^ s) c μ := by
    simpa only [ENNReal.toReal_ofReal hs.le, hc] using
      (Lp.memLp u).norm_rpow_div (ENNReal.ofReal s)
  apply hpow.mono' (aestronglyMeasurable_normScaledSignedPower hp hr hq (Lp.aestronglyMeasurable u))
  exact Filter.Eventually.of_forall fun t ↦ (norm_normScaledSignedPower hr hq hs (u t)).le

private theorem mul_signedPower_eq_norm_rpow {r : ℝ} (hr : 0 < r) (x : ℝ) :
    x * Real.signedPower r x = ‖x‖ ^ (r + 1) := by
  have hnonneg (y : ℝ) (hy : 0 ≤ y) : y * Real.signedPower r y = ‖y‖ ^ (r + 1) := by
    rw [Real.signedPower_of_nonneg hr hy, Real.norm_of_nonneg hy]
    rcases hy.eq_or_lt with rfl | hy
    · simp [Real.zero_rpow (by linarith : r + 1 ≠ 0)]
    · cas using hy
  rcases le_total 0 x with hx | hx
  · exact hnonneg x hx
  · simpa only [Real.signedPower_neg, _root_.norm_neg, neg_mul_neg] using
      hnonneg (-x) (neg_nonneg.mpr hx)

/-- The spatial normalized power pairs with its input to give the prescribed
norm power. The pairing uses the actual quotient representatives. -/
theorem integral_mul_normScaledSignedPower {p q : ℝ≥0∞} {r s : ℝ}
    (hp₀ : p ≠ 0) (hp : p ≠ ∞) (hr : 0 < r)
    (hq : p / ENNReal.ofReal r = q) (hpr : p.toReal = r + 1)
    (hs : 0 < s) (u : Lp ℝ p ν) :
    (∫ x, u x * normScaledSignedPower hr hq s u x ∂ν) = ‖u‖ ^ (s + 1) := by
  have he : (fun x ↦ u x * normScaledSignedPower hr hq s u x) =ᵐ[ν]
      fun x ↦ ‖u‖ ^ (s - r) * ‖u x‖ ^ (r + 1) := by
    filter_upwards [Lp.coeFn_smul (‖u‖ ^ (s - r))
      (superposition (fun _ ↦ Real.signedPower r) (memLp_signedPower hr hq) u),
      coeFn_superposition (fun _ ↦ Real.signedPower r) (memLp_signedPower hr hq) u]
      with x hsmul hpow
    change u x * (‖u‖ ^ (s - r) •
      superposition (fun _ ↦ Real.signedPower r) (memLp_signedPower hr hq) u) x = _
    rw [hsmul, Pi.smul_apply, smul_eq_mul, hpow, mul_left_comm,
      mul_signedPower_eq_norm_rpow hr]
  rw [integral_congr_ae he, integral_const_mul]
  have hi := Lp.norm_rpow_eq_integral hp₀ hp u
  rw [hpr] at hi
  rw [← hi]
  by_cases hu : ‖u‖ = 0
  · simp [hu, Real.zero_rpow (by linarith : r + 1 ≠ 0),
      Real.zero_rpow (by linarith : s + 1 ≠ 0)]
  · have hu' : 0 < ‖u‖ := lt_of_le_of_ne (ENNReal.toReal_nonneg : 0 ≤ ‖u‖) (Ne.symm hu)
    generalize ‖u‖ = a at hu' ⊢
    cas using hu'

/-- The spatial normalization assembled as an actual mixed Lebesgue class. -/
noncomputable def mixedNormScaledSignedPower {p q b c : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] {r s : ℝ}
    (hp : p ≠ ∞) (hr : 0 < r) (hq : p / ENNReal.ofReal r = q)
    (hs : 0 < s) (hc : b / ENNReal.ofReal s = c) (u : Lp (Lp ℝ p ν) b μ) :
    Lp (Lp ℝ q ν) c μ :=
  (memLp_normScaledSignedPower hp hr hq hs hc u).toLp _

/-- The mixed normalized power has exactly the outer norm growth prescribed by `s`. -/
theorem norm_mixedNormScaledSignedPower {p q b c : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] {r s : ℝ}
    (hp : p ≠ ∞) (hr : 0 < r) (hq : p / ENNReal.ofReal r = q)
    (hs : 0 < s) (hc : b / ENNReal.ofReal s = c) (u : Lp (Lp ℝ p ν) b μ) :
    ‖mixedNormScaledSignedPower hp hr hq hs hc u‖ = ‖u‖ ^ s := by
  subst c
  rw [mixedNormScaledSignedPower, Lp.norm_toLp]
  have he : eLpNorm (fun t ↦ normScaledSignedPower hr hq s (u t))
      (b / ENNReal.ofReal s) μ =
      eLpNorm (fun t ↦ ‖u t‖ ^ s) (b / ENNReal.ofReal s) μ := by
    apply eLpNorm_congr_norm_ae
      (aestronglyMeasurable_normScaledSignedPower hp hr hq (Lp.aestronglyMeasurable u))
      (((Lp.aestronglyMeasurable u).norm.aemeasurable.pow_const s).aestronglyMeasurable)
    filter_upwards with t
    rw [norm_normScaledSignedPower hr hq hs,
      Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [he, eLpNorm_norm_rpow _ (Lp.aestronglyMeasurable u) hs]
  have hs0 : ENNReal.ofReal s ≠ 0 := by positivity
  rw [div_eq_mul_inv, mul_assoc,
    ENNReal.inv_mul_cancel hs0 ENNReal.ofReal_ne_top, mul_one,
    ← ENNReal.toReal_rpow, Lp.norm_def]

/-- The iterated pairing with the mixed normalized power is the exact outer
norm power. Both quotient transports are explicit, without dual representation. -/
theorem integral_integral_mul_mixedNormScaledSignedPower {p q b c : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] {r s : ℝ}
    (hp₀ : p ≠ 0) (hp : p ≠ ∞) (hr : 0 < r)
    (hq : p / ENNReal.ofReal r = q) (hpr : p.toReal = r + 1)
    (hb₀ : b ≠ 0) (hb : b ≠ ∞) (hs : 0 < s)
    (hc : b / ENNReal.ofReal s = c) (hbs : b.toReal = s + 1)
    (u : Lp (Lp ℝ p ν) b μ) :
    (∫ t, ∫ x, u t x * mixedNormScaledSignedPower hp hr hq hs hc u t x ∂ν ∂μ) =
      ‖u‖ ^ (s + 1) := by
  have he : (fun t ↦ ∫ x, u t x * mixedNormScaledSignedPower hp hr hq hs hc u t x ∂ν)
      =ᵐ[μ] fun t ↦ ‖u t‖ ^ (s + 1) := by
    filter_upwards [(memLp_normScaledSignedPower hp hr hq hs hc u).coeFn_toLp] with t ht
    change (∫ x, u t x * ((memLp_normScaledSignedPower hp hr hq hs hc u).toLp _) t x ∂ν) = _
    rw [ht]
    exact integral_mul_normScaledSignedPower hp₀ hp hr hq hpr hs (u t)
  rw [integral_congr_ae he, ← hbs]
  exact (Lp.norm_rpow_eq_integral hb₀ hb u).symm

/-- Bounds against every dual mixed Lebesgue class control the actual mixed norm.
The explicit normalized odd power proves this without a Bochner duality premise. -/
theorem norm_le_of_forall_integral_integral_mul_le {p q b c : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ b)] {r s C : ℝ}
    (hp₀ : p ≠ 0) (hp : p ≠ ∞) (hr : 0 < r)
    (hq : p / ENNReal.ofReal r = q) (hpr : p.toReal = r + 1)
    (hb₀ : b ≠ 0) (hb : b ≠ ∞) (hs : 0 < s)
    (hc : b / ENNReal.ofReal s = c) (hbs : b.toReal = s + 1) (hC : 0 ≤ C)
    (u : Lp (Lp ℝ p ν) b μ)
    (hbound : ∀ v : Lp (Lp ℝ q ν) c μ, (∫ t, ∫ x, u t x * v t x ∂ν ∂μ) ≤ C * ‖v‖) :
    ‖u‖ ≤ C := by
  by_cases hu : ‖u‖ = 0
  · simpa only [hu] using hC
  have hu' : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  have h := hbound (mixedNormScaledSignedPower hp hr hq hs hc u)
  rw [integral_integral_mul_mixedNormScaledSignedPower hp₀ hp hr hq hpr
    hb₀ hb hs hc hbs, norm_mixedNormScaledSignedPower hp hr hq hs hc] at h
  have he : ‖u‖ ^ (s + 1) = ‖u‖ * ‖u‖ ^ s := by
    generalize ‖u‖ = a at hu' ⊢
    cas using hu'
  rw [he] at h
  exact le_of_mul_le_mul_right h (Real.rpow_pos_of_pos hu' s)

end MeasureTheory.Lp
