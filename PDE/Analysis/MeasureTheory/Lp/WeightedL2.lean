/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.Positivity.Finset

/-!
# Weighted L² integrability and real Lp estimates

A measurable function bounded by `ε` against a nonnegative integrable weight `w`
has integrable weighted square. Multiplication by `√w` then gives an element of
`L² μ`, whose norm is at most `ε √M` when the weight has mass at most `M`.
The weight may vanish, and all bounds need hold only almost everywhere.

The estimates prove `MemLp` membership as well as the norm bound, since a
real-valued integral or `lpNorm` is totalized at nonintegrable functions.

The remaining results are Cauchy–Schwarz for real `L²` functions, the
`L∞ × Lp → Lp` multiplier estimate, and bounds on product pairings and their
differences. The measure is arbitrary throughout.
-/

@[expose] public section

noncomputable section


open scoped ENNReal InnerProductSpace

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A bounded measurable function has integrable square against an integrable
nonnegative weight. No finiteness assumption on the ambient measure is needed. -/
theorem integrable_sq_mul_of_ae_abs_le
    {f w : X → ℝ} {ε : ℝ} (hf : AEStronglyMeasurable f μ)
    (hw : 0 ≤ᵐ[μ] w) (hwint : Integrable w μ)
    (hbound : ∀ᵐ x ∂μ, |f x| ≤ ε) :
    Integrable (fun x ↦ f x ^ 2 * w x) μ := by
  refine (hwint.const_mul (ε ^ 2)).mono'
    ((hf.pow 2).mul hwint.aestronglyMeasurable) ?_
  filter_upwards [hw, hbound] with x hwx hfx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hwx)]
  exact mul_le_mul_of_nonneg_right
    (sq_le_sq.2 (hfx.trans (le_abs_self ε))) hwx

/-- Multiplication by the square root of an integrable weight sends bounded
measurable functions into `L²`. Zeros of the weight cause no restriction. -/
theorem memLp_mul_sqrt_of_ae_abs_le
    {f w : X → ℝ} {ε : ℝ} (hf : AEStronglyMeasurable f μ)
    (hw : 0 ≤ᵐ[μ] w) (hwint : Integrable w μ)
    (hbound : ∀ᵐ x ∂μ, |f x| ≤ ε) :
    MemLp (fun x ↦ f x * √(w x)) 2 μ := by
  have hmeas := hf.mul
    (Real.continuous_sqrt.comp_aestronglyMeasurable hwint.aestronglyMeasurable)
  apply (memLp_two_iff_integrable_sq hmeas).2
  apply (integrable_sq_mul_of_ae_abs_le hf hw hwint hbound).congr
  filter_upwards [hw] with x hwx
  change f x ^ 2 * w x = (f x * √(w x)) ^ 2
  simp only [mul_pow, Real.sq_sqrt hwx]

/-- The `L²` norm of `f √w` is the square root of the weighted square integral.
With the `MemLp` hypothesis this is the norm of an `Lp` element. -/
theorem norm_toLp_mul_sqrt_eq_sqrt_integral
    {f w : X → ℝ} (hf : MemLp (fun x ↦ f x * √(w x)) 2 μ)
    (hw : 0 ≤ᵐ[μ] w) :
    ‖hf.toLp (fun x ↦ f x * √(w x))‖ =
      √(∫ x, f x ^ 2 * w x ∂μ) := by
  rw [Lp.norm_toLp, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
    ← one_div, ← Real.sqrt_eq_rpow]
  apply congrArg Real.sqrt
  apply integral_congr_ae
  filter_upwards [hw] with x hwx
  simp only [mul_pow, Real.sq_sqrt hwx]

/-- The weighted `L²` norm is at most `ε √M` if `|f| ≤ ε` and the weight has
mass at most `M`. For measurable bounded `f`, obtain `hf` from
`memLp_mul_sqrt_of_ae_abs_le`; no separate square-integrability assumption is needed. -/
theorem norm_toLp_mul_sqrt_le_of_ae_abs_le
    {f w : X → ℝ} {ε M : ℝ}
    (hf : MemLp (fun x ↦ f x * √(w x)) 2 μ)
    (hε : 0 ≤ ε) (hw : 0 ≤ᵐ[μ] w) (hwint : Integrable w μ)
    (hbound : ∀ᵐ x ∂μ, |f x| ≤ ε) (hmass : ∫ x, w x ∂μ ≤ M) :
    ‖hf.toLp (fun x ↦ f x * √(w x))‖ ≤ ε * √M := by
  have hfint : Integrable (fun x ↦ f x ^ 2 * w x) μ := by
    apply hf.integrable_sq.congr
    filter_upwards [hw] with x hwx
    simp only [mul_pow, Real.sq_sqrt hwx]
  have hle : (fun x ↦ f x ^ 2 * w x) ≤ᵐ[μ] fun x ↦ ε ^ 2 * w x := by
    filter_upwards [hw, hbound] with x hwx hfx
    exact mul_le_mul_of_nonneg_right
      (sq_le_sq.2 (hfx.trans (le_abs_self ε))) hwx
  have hboundSq : ∫ x, f x ^ 2 * w x ∂μ ≤ ε ^ 2 * M :=
    calc
      ∫ x, f x ^ 2 * w x ∂μ ≤ ∫ x, ε ^ 2 * w x ∂μ :=
        integral_mono_ae hfint (hwint.const_mul _) hle
      _ = ε ^ 2 * ∫ x, w x ∂μ := integral_const_mul _ _
      _ ≤ ε ^ 2 * M := mul_le_mul_of_nonneg_left hmass (sq_nonneg ε)
  rw [norm_toLp_mul_sqrt_eq_sqrt_integral hf hw]
  calc
    √(∫ x, f x ^ 2 * w x ∂μ) ≤ √(ε ^ 2 * M) :=
      Real.sqrt_le_sqrt hboundSq
    _ = ε * √M := by rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε]

/-- Cauchy–Schwarz for the integral pairing of two real `L2` functions. -/
theorem abs_integral_mul_le_lpNorm_two_mul_lpNorm_two
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ lpNorm f 2 μ * lpNorm g 2 μ := by
  let F : Lp ℝ 2 μ := hf.toLp f
  let G : Lp ℝ 2 μ := hg.toLp g
  have hinner : ∫ x, f x * g x ∂μ = ⟪F, G⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
    simp only [F, G, hfx, hgx, RCLike.inner_apply, conj_trivial]
    ring
  rw [hinner]
  simpa only [F, G, Lp.norm_toLp, toReal_eLpNorm] using abs_real_inner_le_norm F G

/-- Multiplication by a real `L-infinity` function is bounded on every real `Lp` space. -/
theorem lpNorm_mul_le_lpNorm_top_mul_lpNorm
    {p : ℝ≥0∞} {f g : X → ℝ} (hf : MemLp f ∞ μ) (hg : MemLp g p μ) :
    lpNorm (fun x ↦ f x * g x) p μ ≤ lpNorm f ∞ μ * lpNorm g p μ := by
  have hfg : AEStronglyMeasurable (fun x ↦ f x * g x) μ :=
    hf.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂μ, ‖f x * g x‖ ≤ lpNorm f ∞ μ * ‖g x‖ := by
    filter_upwards [ae_le_lpNorm_exponent_top hf] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hseminorm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hfg hpoint p
  have hfinite : ENNReal.ofReal (lpNorm f ∞ μ) * eLpNorm g p μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono hfinite hseminorm
  simpa only [toReal_eLpNorm, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal lpNorm_nonneg] using hreal

/-- An `L∞` coefficient bounds the integral pairing of two real `L²` functions
for any measure. -/
theorem abs_integral_triple_mul_le_lpNorm_measure
    {χ f g : X → ℝ} (hχ : MemLp χ ∞ μ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, χ x * f x * g x ∂μ| ≤ lpNorm χ ∞ μ * lpNorm f 2 μ * lpNorm g 2 μ := by
  have hχf : MemLp (fun x ↦ χ x * f x) 2 μ := hχ.mul hf
  exact (abs_integral_mul_le_lpNorm_two_mul_lpNorm_two hχf hg).trans
    (mul_le_mul_of_nonneg_right (lpNorm_mul_le_lpNorm_top_mul_lpNorm hχ hf) lpNorm_nonneg)

/-- A pointwise bound `‖χ x‖ ≤ C` bounds the `L∞` norm of `χ` by `C`. -/
theorem lpNorm_top_le_of_bound {χ : X → ℝ} {C : ℝ}
    (hχ : AEStronglyMeasurable χ μ) (hC : 0 ≤ C) (hbound : ∀ x, ‖χ x‖ ≤ C) :
    lpNorm χ ∞ μ ≤ C := by
  have h := eLpNormEssSup_le_of_ae_bound (μ := μ) (Filter.Eventually.of_forall hbound)
  rw [← toReal_eLpNorm, eLpNorm_exponent_top hχ]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal hC)

/-- `abs_integral_triple_mul_le_lpNorm_measure` with the `L∞` norm of the coefficient
replaced by a pointwise bound `C`. -/
theorem abs_integral_triple_mul_le_of_bound {χ f g : X → ℝ} {C : ℝ}
    (hχ : AEStronglyMeasurable χ μ) (hC : 0 ≤ C) (hbound : ∀ x, ‖χ x‖ ≤ C)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, χ x * f x * g x ∂μ| ≤ C * lpNorm f 2 μ * lpNorm g 2 μ := by
  have htop := memLp_top_of_bound (μ := μ) hχ C (Filter.Eventually.of_forall hbound)
  exact (abs_integral_triple_mul_le_lpNorm_measure htop hf hg).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (lpNorm_top_le_of_bound hχ hC hbound) lpNorm_nonneg)
      lpNorm_nonneg)

/-- The change in an `L∞`-weighted product pairing is bounded by the `L²`
changes of its two factors. All four factors are square-integrable for the same
measure; no finiteness assumption on that measure is needed. -/
theorem abs_integral_triple_mul_sub_le_lpNorm_measure
    {χ f f₀ g g₀ : X → ℝ} (hχ : MemLp χ ∞ μ)
    (hf : MemLp f 2 μ) (hf₀ : MemLp f₀ 2 μ)
    (hg : MemLp g 2 μ) (hg₀ : MemLp g₀ 2 μ) :
    |(∫ x, χ x * f x * g x ∂μ) - ∫ x, χ x * f₀ x * g₀ x ∂μ| ≤
      lpNorm χ ∞ μ *
        (lpNorm (fun x ↦ f x - f₀ x) 2 μ * lpNorm g 2 μ +
          lpNorm f₀ 2 μ * lpNorm (fun x ↦ g x - g₀ x) 2 μ) := by
  have h₁ := abs_integral_triple_mul_le_lpNorm_measure hχ (hf.sub hf₀) hg
  have h₂ := abs_integral_triple_mul_le_lpNorm_measure hχ hf₀ (hg.sub hg₀)
  simp only [Pi.sub_def] at h₁ h₂
  have heq : (fun x ↦ χ x * f x * g x - χ x * f₀ x * g₀ x) =
      (fun x ↦ χ x * (f x - f₀ x) * g x + χ x * f₀ x * (g x - g₀ x)) := by
    funext x
    ring
  have hfg : Integrable (fun x ↦ χ x * f x * g x) μ :=
    (hχ.mul (r := 2) hf).integrable_mul hg
  have hf₀g₀ : Integrable (fun x ↦ χ x * f₀ x * g₀ x) μ :=
    (hχ.mul (r := 2) hf₀).integrable_mul hg₀
  have hdiff : Integrable (fun x ↦ χ x * (f x - f₀ x) * g x) μ :=
    (hχ.mul (r := 2) (hf.sub hf₀)).integrable_mul hg
  have hdiff₀ : Integrable (fun x ↦ χ x * f₀ x * (g x - g₀ x)) μ :=
    (hχ.mul (r := 2) hf₀).integrable_mul (hg.sub hg₀)
  rw [← integral_sub hfg hf₀g₀, heq, integral_add hdiff hdiff₀]
  exact (abs_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))

/-- Measure-level `L²` Cauchy–Schwarz in square-integral notation. -/
theorem integral_abs_mul_le_sqrt_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, |f x * g x| ∂μ) ≤
      √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have h := integral_mul_norm_le_Lp_mul_Lq
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two hf' hg'
  simpa [Real.norm_eq_abs, abs_mul, sq_abs, Real.sqrt_eq_rpow] using h

/--
A weighted square integral gives `L²` membership of the square-root weighted
function. The measurability hypothesis is stated for that function.
-/
theorem memLp_mul_sqrt_of_aestronglyMeasurable_of_integrable_weighted_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a Φ : α → ℝ}
    (hmeas : AEStronglyMeasurable (fun x ↦ a x * √(Φ x)) μ)
    (hΦ_nonneg : ∀ x, 0 ≤ Φ x)
    (henergy : Integrable (fun x ↦ a x ^ 2 * Φ x) μ) :
    MemLp (fun x ↦ a x * √(Φ x)) 2 μ := by
  have hsq : Integrable (fun x ↦ (a x * √(Φ x)) ^ 2) μ := by
    refine henergy.congr ?_
    filter_upwards with x
    simp only [mul_pow, Real.sq_sqrt (hΦ_nonneg x)]
  exact (memLp_two_iff_integrable_sq hmeas).2 hsq

/--
A strictly positive weight floor converts weighted squared `L²` control into
unweighted squared `L²` control with the exact reciprocal-floor factor.
-/
theorem integral_sq_le_inv_mul_integral_sq_mul_of_floor
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f Φ : α → ℝ) (C : ℝ)
    (hC : 0 < C) (hFloor : ∀ x, C ≤ Φ x)
    (hSq : Integrable (fun x ↦ f x ^ 2) μ)
    (hWeighted : Integrable (fun x ↦ f x ^ 2 * Φ x) μ) :
    (∫ x, f x ^ 2 ∂μ) ≤ C⁻¹ * ∫ x, f x ^ 2 * Φ x ∂μ := by
  have hCinv : 0 ≤ C⁻¹ := inv_nonneg.mpr hC.le
  have hScaled : Integrable (fun x ↦ C⁻¹ * (f x ^ 2 * Φ x)) μ :=
    hWeighted.const_mul C⁻¹
  calc
    (∫ x, f x ^ 2 ∂μ) ≤ ∫ x, C⁻¹ * (f x ^ 2 * Φ x) ∂μ := by
      apply integral_mono hSq hScaled
      intro x
      calc
        f x ^ 2 = C⁻¹ * (f x ^ 2 * C) := by
          field_simp
        _ ≤ C⁻¹ * (f x ^ 2 * Φ x) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hFloor x) (sq_nonneg (f x))) hCinv
    _ = C⁻¹ * ∫ x, f x ^ 2 * Φ x ∂μ := by
      rw [integral_const_mul]

/-- Square-root form of the positive-weight-floor comparison. -/
theorem sqrt_integral_sq_le_sqrt_inv_mul_sqrt_integral_sq_mul_of_floor
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f Φ : α → ℝ) (C : ℝ)
    (hC : 0 < C) (hFloor : ∀ x, C ≤ Φ x)
    (hSq : Integrable (fun x ↦ f x ^ 2) μ)
    (hWeighted : Integrable (fun x ↦ f x ^ 2 * Φ x) μ) :
    √(∫ x, f x ^ 2 ∂μ) ≤
      √C⁻¹ * √(∫ x, f x ^ 2 * Φ x ∂μ) := by
  calc
    √(∫ x, f x ^ 2 ∂μ) ≤
        √(C⁻¹ * ∫ x, f x ^ 2 * Φ x ∂μ) :=
      Real.sqrt_le_sqrt
        (integral_sq_le_inv_mul_integral_sq_mul_of_floor
          μ f Φ C hC hFloor hSq hWeighted)
    _ = √C⁻¹ * √(∫ x, f x ^ 2 * Φ x ∂μ) := by
      rw [Real.sqrt_mul (inv_nonneg.mpr hC.le)]

/-- Weighted Cauchy bound for the integral of the absolute product when the
coefficient comparison holds almost everywhere. The functions and weights
are unchanged; the comparison enters only through integral monotonicity. -/
theorem weightedInterpolation_integral_abs_term_cauchy_measure_of_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b w Φprev Φnext : α → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare : ∀ᵐ x ∂μ,
      |w x| ≤ A * √(Φprev x) * √(Φnext x))
    (ha : MemLp (fun x ↦ a x * √(Φprev x)) 2 μ)
    (hb : MemLp (fun x ↦ b x * √(Φnext x)) 2 μ)
    (hterm_int : Integrable (fun x ↦ a x * b x * w x) μ) :
    (∫ x, |a x * b x * w x| ∂μ) ≤
      A * √(∫ x, a x ^ 2 * Φprev x ∂μ) *
        √(∫ x, b x ^ 2 * Φnext x ∂μ) := by
  let fa : α → ℝ := fun x ↦ a x * √(Φprev x)
  let fb : α → ℝ := fun x ↦ b x * √(Φnext x)
  have hprod_int : Integrable (fun x ↦ fa x * fb x) μ := by
    change Integrable (fa * fb) μ
    exact ha.integrable_mul hb
  have hpoint : ∀ᵐ x ∂μ, |a x * b x * w x| ≤ A * |fa x * fb x| := by
    filter_upwards [hcompare] with x hx
    have hab : 0 ≤ |a x| * |b x| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      |a x * b x * w x| = |a x| * |b x| * |w x| := by
        rw [abs_mul, abs_mul]
      _ ≤ |a x| * |b x| *
            (A * √(Φprev x) * √(Φnext x)) :=
        mul_le_mul_of_nonneg_left hx hab
      _ = A * |fa x * fb x| := by
        simp only [fa, fb, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        ring
  have hraw :
      (∫ x, |a x * b x * w x| ∂μ) ≤ A * ∫ x, |fa x * fb x| ∂μ := by
    calc
      (∫ x, |a x * b x * w x| ∂μ) ≤ ∫ x, A * |fa x * fb x| ∂μ :=
        integral_mono_ae hterm_int.abs (hprod_int.abs.const_mul A) hpoint
      _ = A * ∫ x, |fa x * fb x| ∂μ := by rw [integral_const_mul]
  have hcauchy := MeasureTheory.integral_abs_mul_le_sqrt_integral_sq ha hb
  have hfa_sq : (∫ x, fa x ^ 2 ∂μ) = ∫ x, a x ^ 2 * Φprev x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [fa, mul_pow, Real.sq_sqrt (hprev_nonneg x)]
  have hfb_sq : (∫ x, fb x ^ 2 ∂μ) = ∫ x, b x ^ 2 * Φnext x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [fb, mul_pow, Real.sq_sqrt (hnext_nonneg x)]
  calc
    (∫ x, |a x * b x * w x| ∂μ) ≤ A * ∫ x, |fa x * fb x| ∂μ := hraw
    _ ≤ A * (√(∫ x, fa x ^ 2 ∂μ) *
          √(∫ x, fb x ^ 2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hcauchy hA
    _ = A * √(∫ x, a x ^ 2 * Φprev x ∂μ) *
          √(∫ x, b x ^ 2 * Φnext x ∂μ) := by
      rw [hfa_sq, hfb_sq]
      ring

/-- Adjacent-weight Cauchy estimate with an almost-everywhere coefficient
comparison over an arbitrary measure. -/
theorem weightedInterpolation_integral_term_cauchy_measure_of_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b w Φprev Φnext : α → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare : ∀ᵐ x ∂μ,
      |w x| ≤ A * √(Φprev x) * √(Φnext x))
    (ha : MemLp (fun x ↦ a x * √(Φprev x)) 2 μ)
    (hb : MemLp (fun x ↦ b x * √(Φnext x)) 2 μ)
    (hterm_int : Integrable (fun x ↦ a x * b x * w x) μ) :
    |∫ x, a x * b x * w x ∂μ| ≤
      A * √(∫ x, a x ^ 2 * Φprev x ∂μ) *
        √(∫ x, b x ^ 2 * Φnext x ∂μ) := by
  calc
    |∫ x, a x * b x * w x ∂μ| ≤ ∫ x, |a x * b x * w x| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ _ := weightedInterpolation_integral_abs_term_cauchy_measure_of_ae
      hA hprev_nonneg hnext_nonneg hcompare ha hb hterm_int

/--
Adjacent-weight integral Cauchy estimate over an arbitrary
measure; this is the form used on the half-plane product measure.
-/
theorem weightedInterpolation_integral_term_cauchy_measure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b w Φprev Φnext : α → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare : ∀ x,
      |w x| ≤ A * √(Φprev x) * √(Φnext x))
    (ha : MemLp (fun x ↦ a x * √(Φprev x)) 2 μ)
    (hb : MemLp (fun x ↦ b x * √(Φnext x)) 2 μ)
    (hterm_int : Integrable (fun x ↦ a x * b x * w x) μ) :
    |∫ x, a x * b x * w x ∂μ| ≤
      A * √(∫ x, a x ^ 2 * Φprev x ∂μ) *
        √(∫ x, b x ^ 2 * Φnext x ∂μ) := by
  exact weightedInterpolation_integral_term_cauchy_measure_of_ae
    hA hprev_nonneg hnext_nonneg (ae_of_all μ hcompare) ha hb hterm_int

/-- Pull a uniformly bounded multiplier out of an absolute integral estimate. -/
theorem integral_bounded_multiplier_abs_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {L core : α → ℝ} {C : ℝ}
    (hbound : ∀ x, |L x| ≤ C)
    (hfull : Integrable (fun x ↦ L x * core x) μ)
    (hcore : Integrable core μ) :
    |∫ x, L x * core x ∂μ| ≤ C * ∫ x, |core x| ∂μ := by
  have hpoint : ∀ x, |L x * core x| ≤ C * |core x| := by
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hbound x) (abs_nonneg _)
  calc
    |∫ x, L x * core x ∂μ| ≤ ∫ x, |L x * core x| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, C * |core x| ∂μ :=
      integral_mono hfull.abs (hcore.abs.const_mul C) hpoint
    _ = C * ∫ x, |core x| ∂μ := by rw [integral_const_mul]

/-- Weighted `L²` Cauchy bound for the integral of the absolute product. -/
theorem weightedInterpolation_integral_abs_term_cauchy_measure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b w Φprev Φnext : α → ℝ} {A : ℝ}
    (hA : 0 ≤ A)
    (hprev_nonneg : ∀ x, 0 ≤ Φprev x)
    (hnext_nonneg : ∀ x, 0 ≤ Φnext x)
    (hcompare : ∀ x,
      |w x| ≤ A * √(Φprev x) * √(Φnext x))
    (ha : MemLp (fun x ↦ a x * √(Φprev x)) 2 μ)
    (hb : MemLp (fun x ↦ b x * √(Φnext x)) 2 μ)
    (hterm_int : Integrable (fun x ↦ a x * b x * w x) μ) :
    (∫ x, |a x * b x * w x| ∂μ) ≤
      A * √(∫ x, a x ^ 2 * Φprev x ∂μ) *
        √(∫ x, b x ^ 2 * Φnext x ∂μ) := by
  exact weightedInterpolation_integral_abs_term_cauchy_measure_of_ae
    hA hprev_nonneg hnext_nonneg (ae_of_all μ hcompare) ha hb hterm_int

/-- A bounded scalar coefficient may be pulled in front of the weighted pairing. -/
theorem coefficient_mixed_inner_bound
    (μ : Measure X) (Φ : X → ℝ≥0∞) (f g : (X → ℝ))
    (hf : MemLp f 2 (μ.withDensity Φ))
    (hg : MemLp g 2 (μ.withDensity Φ))
    {c C : ℝ} (hC : |c| ≤ C) :
    |c * ∫ x, f x * g x ∂(μ.withDensity Φ)| ≤
      C * lpNorm f 2 (μ.withDensity Φ) *
        lpNorm g 2 (μ.withDensity Φ) := by
  have hCnonneg : 0 ≤ C := (abs_nonneg c).trans hC
  calc
    |c * ∫ x, f x * g x ∂(μ.withDensity Φ)| =
        |c| * |∫ x, f x * g x ∂(μ.withDensity Φ)| := by rw [abs_mul]
    _ ≤ C * (lpNorm f 2 (μ.withDensity Φ) *
        lpNorm g 2 (μ.withDensity Φ)) :=
      mul_le_mul hC (abs_integral_mul_le_lpNorm_two_mul_lpNorm_two hf hg)
        (abs_nonneg _) hCnonneg
    _ = C * lpNorm f 2 (μ.withDensity Φ) *
        lpNorm g 2 (μ.withDensity Φ) := by ring

/-- Coefficient control, Cauchy–Schwarz, and Young's inequality combined. -/
theorem coefficient_mixed_inner_young
    (μ : Measure X) (Φ : X → ℝ≥0∞) (f g : (X → ℝ))
    (hf : MemLp f 2 (μ.withDensity Φ))
    (hg : MemLp g 2 (μ.withDensity Φ))
    {c C η : ℝ} (hC : |c| ≤ C) (hη : 0 < η) :
    |c * ∫ x, f x * g x ∂(μ.withDensity Φ)| ≤
      C * ((η / 2) * lpNorm f 2 (μ.withDensity Φ) ^ 2 +
        (1 / (2 * η)) * lpNorm g 2 (μ.withDensity Φ) ^ 2) := by
  have hCnonneg : 0 ≤ C := (abs_nonneg c).trans hC
  calc
    |c * ∫ x, f x * g x ∂(μ.withDensity Φ)| ≤
        C * lpNorm f 2 (μ.withDensity Φ) *
          lpNorm g 2 (μ.withDensity Φ) :=
      coefficient_mixed_inner_bound μ Φ f g hf hg hC
    _ = C * (lpNorm f 2 (μ.withDensity Φ) *
        lpNorm g 2 (μ.withDensity Φ)) := by ring
    _ ≤ C * ((η / 2) * lpNorm f 2 (μ.withDensity Φ) ^ 2 +
        (1 / (2 * η)) * lpNorm g 2 (μ.withDensity Φ) ^ 2) :=
      mul_le_mul_of_nonneg_left (by
        have hyoung := two_mul_le_add_mul_sq
          (a := lpNorm f 2 (μ.withDensity Φ))
          (b := lpNorm g 2 (μ.withDensity Φ)) hη
        simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
        nlinarith [hyoung]) hCnonneg

/-- Young's inequality applied after the nonlinear multiplier estimate. -/
theorem abs_integral_triple_mul_le_young
    (μ : Measure X) (Φ : X → ℝ≥0∞)
    (f g h : X → ℝ)
    (hf : MemLp f ∞ (μ.withDensity Φ))
    (hg : MemLp g 2 (μ.withDensity Φ))
    (hh : MemLp h 2 (μ.withDensity Φ))
    {η : ℝ} (hη : 0 < η) :
    |∫ x, (f * g) x * h x ∂(μ.withDensity Φ)| ≤
      (η / 2) * lpNorm g 2 (μ.withDensity Φ) ^ 2 +
        (1 / (2 * η)) * lpNorm f ∞ (μ.withDensity Φ) ^ 2 *
          lpNorm h 2 (μ.withDensity Φ) ^ 2 := by
  have hbound := abs_integral_triple_mul_le_lpNorm_measure hf hg hh
  have hyoung :
      lpNorm g 2 (μ.withDensity Φ) *
          (lpNorm f ∞ (μ.withDensity Φ) *
            lpNorm h 2 (μ.withDensity Φ)) ≤
        (η / 2) * lpNorm g 2 (μ.withDensity Φ) ^ 2 +
          (1 / (2 * η)) * (lpNorm f ∞ (μ.withDensity Φ) *
            lpNorm h 2 (μ.withDensity Φ)) ^ 2 := by
    have hyoung := two_mul_le_add_mul_sq
      (a := lpNorm g 2 (μ.withDensity Φ))
      (b := lpNorm f ∞ (μ.withDensity Φ) * lpNorm h 2 (μ.withDensity Φ)) hη
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    nlinarith [hyoung]
  calc
    |∫ x, (f * g) x * h x ∂(μ.withDensity Φ)| ≤
        lpNorm f ∞ (μ.withDensity Φ) *
          lpNorm g 2 (μ.withDensity Φ) *
            lpNorm h 2 (μ.withDensity Φ) := hbound
    _ = lpNorm g 2 (μ.withDensity Φ) *
        (lpNorm f ∞ (μ.withDensity Φ) *
          lpNorm h 2 (μ.withDensity Φ)) := by ring
    _ ≤ (η / 2) * lpNorm g 2 (μ.withDensity Φ) ^ 2 +
        (1 / (2 * η)) * (lpNorm f ∞ (μ.withDensity Φ) *
          lpNorm h 2 (μ.withDensity Φ)) ^ 2 := hyoung
    _ = (η / 2) * lpNorm g 2 (μ.withDensity Φ) ^ 2 +
        (1 / (2 * η)) * lpNorm f ∞ (μ.withDensity Φ) ^ 2 *
          lpNorm h 2 (μ.withDensity Φ) ^ 2 := by ring

/-- Young's split with the `L-infinity` multiplier outside the parentheses. -/
theorem abs_integral_triple_mul_le_young_linf_factor
    (μ : Measure X) (Φ : X → ℝ≥0∞)
    (f g h : X → ℝ)
    (hf : MemLp f ∞ (μ.withDensity Φ))
    (hg : MemLp g 2 (μ.withDensity Φ))
    (hh : MemLp h 2 (μ.withDensity Φ))
    {η : ℝ} (hη : 0 < η) :
    |∫ x, (f * g) x * h x ∂(μ.withDensity Φ)| ≤
      lpNorm f ∞ (μ.withDensity Φ) *
        ((η / 2) * lpNorm g 2 (μ.withDensity Φ) ^ 2 +
          (1 / (2 * η)) * lpNorm h 2 (μ.withDensity Φ) ^ 2) := by
  have hbound := abs_integral_triple_mul_le_lpNorm_measure hf hg hh
  have hyoung :
      lpNorm g 2 (μ.withDensity Φ) *
          lpNorm h 2 (μ.withDensity Φ) ≤
        (η / 2) * lpNorm g 2 (μ.withDensity Φ) ^ 2 +
          (1 / (2 * η)) * lpNorm h 2 (μ.withDensity Φ) ^ 2 := by
    have hyoung := two_mul_le_add_mul_sq
      (a := lpNorm g 2 (μ.withDensity Φ))
      (b := lpNorm h 2 (μ.withDensity Φ)) hη
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
    nlinarith [hyoung]
  calc
    |∫ x, (f * g) x * h x ∂(μ.withDensity Φ)| ≤
        lpNorm f ∞ (μ.withDensity Φ) *
          lpNorm g 2 (μ.withDensity Φ) *
            lpNorm h 2 (μ.withDensity Φ) := hbound
    _ = lpNorm f ∞ (μ.withDensity Φ) *
        (lpNorm g 2 (μ.withDensity Φ) *
          lpNorm h 2 (μ.withDensity Φ)) := by ring
    _ ≤ lpNorm f ∞ (μ.withDensity Φ) *
        ((η / 2) * lpNorm g 2 (μ.withDensity Φ) ^ 2 +
          (1 / (2 * η)) * lpNorm h 2 (μ.withDensity Φ) ^ 2) :=
      mul_le_mul_of_nonneg_left hyoung lpNorm_nonneg

end MeasureTheory
