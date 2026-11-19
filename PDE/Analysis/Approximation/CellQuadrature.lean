/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.BilinearInterpolation
public import CAS.Continuum.Quadrature.SimpsonPeano
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals over cells from vertex values and second derivatives

The trapezoid rule for the `L¹` integral of Chen and Hou, Part II, Lemma 4.2: for `f` with pure
second derivatives bounded by `Mₓ`, `M_y` on `Q = [a, b] × [c, d]`,
`∫_Q |f| ≤ |Q| / 4 ∑_{vertices} |f| + |Q| / 12 (h₁² Mₓ + h₂² M_y)`
(`setIntegral_abs_le_trapezoid`). Taking absolute values inside the rule is what makes it a
one-sided bound; the `1/12` comes from integrating the pointwise envelope
`Mₓ (x - a) (b - x) / 2 + M_y (y - c) (d - y) / 2` of bilinear interpolation, not from the uniform
`1/8` bound.

Part II, Lemma 4.4 interpolates a kernel in its first variable: for `x` in
`P = [a₁, b₁] × [a₂, b₂]` and any measure `ν` in the second variable,
`∫ |K(x, ·)| dν ≤ ∑_v λ_v(x) ∫ |K(v, ·)| dν + (x₁ - a₁)(b₁ - x₁)/2 ∫ M₁ +
(x₂ - a₂)(b₂ - x₂)/2 ∫ M₂`, `v` the four vertices of `P` and `λ_v` the bilinear weights
(`integral_abs_le_of_corners`; the regularity in `x` is required for every point of the measure
space, so a kernel that is regular only on the integration region is used with that region as
the space); the form with `h₁²/8`, `h₂²/8` and constant bounds is
`integral_abs_le_of_corners_const`. The vertices are `(a₁, a₂)`, `(a₁, b₂)`, `(b₁, a₂)`,
`(b₁, b₂)`.

## Main definitions

* `tensorSimpson`: the tensor Simpson rule on `[a, b] × [c, d]`, with the weights `(1, 4, 1) / 6`
  at the endpoints and midpoints in each variable.

## Main results

* `setIntegral_bilinearInterpolant`: the integral of the bilinear interpolant over the cell is
  `|Q| / 4` times the sum of the four vertex values.
* `setIntegral_abs_le_trapezoid`: Part II, Lemma 4.2,
  `∫_Q |f| ≤ |Q| / 4 ∑_{vertices} |f| + |Q| / 12 (h₁² Mₓ + h₂² M_y)`.
* `integral_abs_le_of_corners`: Part II, Lemma 4.4, with bounds `M₁`, `M₂` that depend on the
  second variable.
* `integral_abs_le_of_corners_const`: Part II, Lemma 4.4 with constant bounds and a finite
  measure.
* `abs_setIntegral_sub_tensorSimpson_le`: Supp II (6.16),
  `|∫_Q g - tensorSimpson g| ≤ h₁ h₂ (h₁⁴ Mₓ + h₂⁴ M_y) / 2880` when the fourth derivatives along
  the slices are bounded by `Mₓ` and `M_y`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Section 4.1.3,
  Lemmas 4.2 and 4.4; Supplementary material II (in the same PDF), Section 6.4.1, (6.16).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

open Set MeasureTheory

/-! ### Integrals of the interpolation weights -/

/-- An integral over `[a, b]` from an antiderivative. -/
theorem setIntegral_Icc_eq_sub_of_hasDerivAt {f F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ∀ x, HasDerivAt F (f x) x) (hf : Continuous f) :
    ∫ x in Icc a b, f x = F b - F a := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hF x)
      (hf.intervalIntegrable a b)]

/-- For `a < b`, `∫_{[a, b]} (b - x) / (b - a) dx = (b - a) / 2`. -/
theorem setIntegral_Icc_sub_div {a b : ℝ} (hab : a < b) :
    ∫ x in Icc a b, (b - x) / (b - a) = (b - a) / 2 := by
  have hne : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hF (x : ℝ) : HasDerivAt (fun y ↦ (b - y) ^ 2 * (-1 / (2 * (b - a)))) ((b - x) / (b - a))
      x := by
    have h1 : HasDerivAt (fun y ↦ b - y) (-1) x := by
      simpa using (hasDerivAt_id' x).const_sub b
    convert (h1.fun_pow 2).mul_const (-1 / (2 * (b - a))) using 1
    field_simp
    ring
  rw [setIntegral_Icc_eq_sub_of_hasDerivAt hab.le hF (by fun_prop)]
  field_simp
  ring

/-- For `a < b`, `∫_{[a, b]} (x - a) / (b - a) dx = (b - a) / 2`. -/
theorem setIntegral_Icc_div_sub {a b : ℝ} (hab : a < b) :
    ∫ x in Icc a b, (x - a) / (b - a) = (b - a) / 2 := by
  have hne : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hF (x : ℝ) : HasDerivAt (fun y ↦ (y - a) ^ 2 * (1 / (2 * (b - a)))) ((x - a) / (b - a))
      x := by
    have h1 : HasDerivAt (fun y ↦ y - a) 1 x := by
      simpa using (hasDerivAt_id' x).sub_const a
    convert (h1.fun_pow 2).mul_const (1 / (2 * (b - a))) using 1
    field_simp
    ring
  rw [setIntegral_Icc_eq_sub_of_hasDerivAt hab.le hF (by fun_prop)]
  field_simp
  ring

/-- For `a ≤ b`, `∫_{[a, b]} (x - a) (b - x) dx = (b - a)³ / 6`. -/
theorem setIntegral_Icc_sub_mul_sub {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Icc a b, (x - a) * (b - x) = (b - a) ^ 3 / 6 := by
  have hF (x : ℝ) : HasDerivAt (fun y ↦ (y - a) ^ 3 * (-1 / 3) + (y - a) ^ 2 * ((b - a) / 2))
      ((x - a) * (b - x)) x := by
    have h1 : HasDerivAt (fun y ↦ y - a) 1 x := by
      simpa using (hasDerivAt_id' x).sub_const a
    convert ((h1.fun_pow 3).mul_const (-1 / 3)).add ((h1.fun_pow 2).mul_const ((b - a) / 2))
      using 1
    push_cast
    ring
  rw [setIntegral_Icc_eq_sub_of_hasDerivAt hab hF (by fun_prop)]
  ring

/-- The integral over a rectangle of a product of a function of `x` and a function of `y`. -/
theorem setIntegral_rect_mul (g k : ℝ → ℝ) (a b c d : ℝ) :
    ∫ p in Icc a b ×ˢ Icc c d, g p.1 * k p.2 = (∫ x in Icc a b, g x) * ∫ y in Icc c d, k y := by
  rw [Measure.volume_eq_prod, setIntegral_prod_mul]

/-- **The bilinear interpolant integrates to the trapezoid rule:** its integral over the cell is
`|Q| / 4` times the sum of the four vertex values. -/
theorem setIntegral_bilinearInterpolant {F : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a < b)
    (hcd : c < d) :
    ∫ p in Icc a b ×ˢ Icc c d, bilinearInterpolant F a b c d p.1 p.2 =
      (b - a) * (d - c) / 4 * (F a c + F a d + F b c + F b d) := by
  have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hint (g k : ℝ → ℝ) (hg : Continuous g) (hk : Continuous k) :
      IntegrableOn (fun p : ℝ × ℝ ↦ g p.1 * k p.2) (Icc a b ×ˢ Icc c d) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ ↦ g p.1 * k p.2).continuousOn.integrableOn_compact hK
  set u₀ : ℝ → ℝ := fun x ↦ (b - x) / (b - a)
  set u₁ : ℝ → ℝ := fun x ↦ (x - a) / (b - a)
  set w₀ : ℝ → ℝ := fun y ↦ (d - y) / (d - c)
  set w₁ : ℝ → ℝ := fun y ↦ (y - c) / (d - c)
  have hu₀ : Continuous u₀ := by fun_prop
  have hu₁ : Continuous u₁ := by fun_prop
  have hw₀ : Continuous w₀ := by fun_prop
  have hw₁ : Continuous w₁ := by fun_prop
  have hexpand : ∫ p in Icc a b ×ˢ Icc c d, bilinearInterpolant F a b c d p.1 p.2 =
      ∫ p in Icc a b ×ˢ Icc c d, ((F a c * u₀ p.1 * w₀ p.2 + F a d * u₀ p.1 * w₁ p.2) +
        (F b c * u₁ p.1 * w₀ p.2 + F b d * u₁ p.1 * w₁ p.2)) := by
    congr 1
    funext p
    simp only [bilinearInterpolant, linearInterpolant, u₀, u₁, w₀, w₁]
    ring
  have i₁ := hint (fun x ↦ F a c * u₀ x) w₀ (by fun_prop) hw₀
  have i₂ := hint (fun x ↦ F a d * u₀ x) w₁ (by fun_prop) hw₁
  have i₃ := hint (fun x ↦ F b c * u₁ x) w₀ (by fun_prop) hw₀
  have i₄ := hint (fun x ↦ F b d * u₁ x) w₁ (by fun_prop) hw₁
  rw [hexpand, integral_add (i₁.fun_add i₂) (i₃.fun_add i₄), integral_add i₁ i₂,
    integral_add i₃ i₄, setIntegral_rect_mul (fun x ↦ F a c * u₀ x) w₀,
    setIntegral_rect_mul (fun x ↦ F a d * u₀ x) w₁, setIntegral_rect_mul (fun x ↦ F b c * u₁ x) w₀,
    setIntegral_rect_mul (fun x ↦ F b d * u₁ x) w₁]
  simp only [integral_const_mul, u₀, u₁, w₀, w₁, setIntegral_Icc_sub_div hab,
    setIntegral_Icc_div_sub hab, setIntegral_Icc_sub_div hcd, setIntegral_Icc_div_sub hcd]
  ring

/-! ### The trapezoid rule for `∫ |f|` (Part II, Lemma 4.2) -/

/-- Interpolation with nonnegative weights does not increase absolute values. -/
theorem abs_linearInterpolant_le_linearInterpolant_abs {a b fa fb x : ℝ} (hab : a < b)
    (hx : x ∈ Icc a b) : |linearInterpolant a b fa fb x| ≤ linearInterpolant a b |fa| |fb| x := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hw₀ : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hx.2) hden.le
  have hw₁ : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) hden.le
  unfold linearInterpolant
  refine (abs_add_le _ _).trans (le_of_eq ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg hw₀, abs_of_nonneg hw₁]

/-- Interpolation with nonnegative weights is monotone in the endpoint values. -/
theorem linearInterpolant_mono {a b fa fb ga gb x : ℝ} (hab : a < b) (hx : x ∈ Icc a b)
    (ha : fa ≤ ga) (hb : fb ≤ gb) :
    linearInterpolant a b fa fb x ≤ linearInterpolant a b ga gb x := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hw₀ : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hx.2) hden.le
  have hw₁ : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) hden.le
  unfold linearInterpolant
  gcongr

/-- Bilinear interpolation with nonnegative weights does not increase absolute values. -/
theorem abs_bilinearInterpolant_le_bilinearInterpolant_abs {f : ℝ → ℝ → ℝ} {a b c d x y : ℝ}
    (hab : a < b) (hcd : c < d) (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    |bilinearInterpolant f a b c d x y| ≤ bilinearInterpolant (fun u v ↦ |f u v|) a b c d x y :=
  (abs_linearInterpolant_le_linearInterpolant_abs hab hx).trans
    (linearInterpolant_mono hab hx (abs_linearInterpolant_le_linearInterpolant_abs hcd hy)
      (abs_linearInterpolant_le_linearInterpolant_abs hcd hy))

/-- **Part II, Lemma 4.2 (trapezoidal rule for the `L¹` integral).** For `f` on
`Q = [a, b] × [c, d]` with pure second derivatives bounded by `Mₓ` and `M_y`,
`∫_Q |f| ≤ T(|f|, Q) + |Q| (h₁² Mₓ + h₂² M_y) / 12` where `T(|f|, Q)` is `|Q| / 4` times the sum of
`|f|` at the four vertices. -/
theorem setIntegral_abs_le_trapezoid {f fx fxx fy fyy : ℝ → ℝ → ℝ} {a b c d Mx My : ℝ}
    (hab : a < b) (hcd : c < d)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d))
    (hcontX : ∀ v ∈ Icc c d, ContinuousOn (fun u ↦ f u v) (Icc a b))
    (hderivX : ∀ v ∈ Icc c d, ∀ u ∈ Ioo a b, HasDerivAt (fun z ↦ f z v) (fx u v) u)
    (hderivXX : ∀ v ∈ Icc c d, ∀ u ∈ Ioo a b, HasDerivAt (fun z ↦ fx z v) (fxx u v) u)
    (hboundX : ∀ v ∈ Icc c d, ∀ u ∈ Ioo a b, |fxx u v| ≤ Mx)
    (hcontY : ∀ u ∈ Icc a b, ContinuousOn (f u) (Icc c d))
    (hderivY : ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d, HasDerivAt (f u) (fy u v) v)
    (hderivYY : ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d, HasDerivAt (fy u) (fyy u v) v)
    (hboundY : ∀ u ∈ Icc a b, ∀ v ∈ Ioo c d, |fyy u v| ≤ My) :
    ∫ p in Icc a b ×ˢ Icc c d, |f p.1 p.2| ≤
      (b - a) * (d - c) / 4 * (|f a c| + |f a d| + |f b c| + |f b d|) +
        (b - a) * (d - c) / 12 * ((b - a) ^ 2 * Mx + (d - c) ^ 2 * My) := by
  have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  set Q := Icc a b ×ˢ Icc c d
  set G : ℝ × ℝ → ℝ := fun p ↦ bilinearInterpolant (fun u v ↦ |f u v|) a b c d p.1 p.2 +
    (Mx / 2 * ((p.1 - a) * (b - p.1)) * 1 + 1 * (My / 2 * ((p.2 - c) * (d - p.2))))
  have hpt : ∀ p ∈ Q, |f p.1 p.2| ≤ G p := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have henv := abs_sub_bilinearInterpolant_le_envelope hab hcd hcontX hderivX hderivXX hboundX
      hcontY hderivY hderivYY hboundY hx hy
    have hB := abs_bilinearInterpolant_le_bilinearInterpolant_abs (f := f) hab hcd hx hy
    have := abs_sub_abs_le_abs_sub (f x y) (bilinearInterpolant f a b c d x y)
    simp only [G]
    linarith
  have hGcont : Continuous G := by
    simp only [G, bilinearInterpolant, linearInterpolant]
    fun_prop
  have hmono := setIntegral_mono_on (μ := volume) (hf.abs.integrableOn_compact hK)
    (hGcont.continuousOn.integrableOn_compact hK) (measurableSet_Icc.prod measurableSet_Icc) hpt
  refine hmono.trans (le_of_eq ?_)
  have i₀ : IntegrableOn (fun p : ℝ × ℝ ↦ bilinearInterpolant (fun u v ↦ |f u v|) a b c d p.1 p.2)
      Q := by
    refine Continuous.continuousOn ?_ |>.integrableOn_compact hK
    simp only [bilinearInterpolant, linearInterpolant]
    fun_prop
  have i₁ : IntegrableOn (fun p : ℝ × ℝ ↦ (fun x ↦ Mx / 2 * ((x - a) * (b - x))) p.1 *
      (fun _ ↦ (1 : ℝ)) p.2) Q :=
    (by fun_prop : Continuous fun p : ℝ × ℝ ↦ Mx / 2 * ((p.1 - a) * (b - p.1)) * 1).continuousOn
      |>.integrableOn_compact hK
  have i₂ : IntegrableOn (fun p : ℝ × ℝ ↦ (fun _ ↦ (1 : ℝ)) p.1 *
      (fun y ↦ My / 2 * ((y - c) * (d - y))) p.2) Q :=
    (by fun_prop : Continuous fun p : ℝ × ℝ ↦ 1 * (My / 2 * ((p.2 - c) * (d - p.2)))).continuousOn
      |>.integrableOn_compact hK
  have hone (u v : ℝ) (huv : u ≤ v) : ∫ _ in Icc u v, (1 : ℝ) = v - u :=
    setIntegral_Icc_eq_sub_of_hasDerivAt (F := id) huv (fun x ↦ hasDerivAt_id x) continuous_const
  simp only [G]
  rw [integral_add i₀ (i₁.fun_add i₂), integral_add i₁ i₂]
  simp only [Q]
  rw [setIntegral_bilinearInterpolant hab hcd,
    setIntegral_rect_mul (fun x ↦ Mx / 2 * ((x - a) * (b - x))) (fun _ ↦ 1),
    setIntegral_rect_mul (fun _ ↦ 1) (fun y ↦ My / 2 * ((y - c) * (d - y))),
    integral_const_mul, integral_const_mul,
    setIntegral_Icc_sub_mul_sub hab.le, setIntegral_Icc_sub_mul_sub hcd.le, hone a b hab.le,
    hone c d hcd.le]
  ring

/-! ### Interpolation of a kernel in its first variable (Part II, Lemma 4.4) -/

/-- Integration commutes with linear interpolation in a parameter. -/
theorem integral_linearInterpolant {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {F G : Y → ℝ} {a b x : ℝ} (hF : Integrable F ν) (hG : Integrable G ν) :
    ∫ z, linearInterpolant a b (F z) (G z) x ∂ν =
      linearInterpolant a b (∫ z, F z ∂ν) (∫ z, G z ∂ν) x := by
  unfold linearInterpolant
  rw [integral_add (hF.const_mul _) (hG.const_mul _), integral_const_mul, integral_const_mul]

/-- The linear interpolant in `x` of two integrable functions of the parameter is integrable in the
parameter. -/
theorem integrable_linearInterpolant {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {F G : Y → ℝ} {a b x : ℝ} (hF : Integrable F ν) (hG : Integrable G ν) :
    Integrable (fun z ↦ linearInterpolant a b (F z) (G z) x) ν := by
  unfold linearInterpolant
  exact (hF.const_mul _).fun_add (hG.const_mul _)

/-- Integration commutes with bilinear interpolation in a parameter. -/
theorem integral_bilinearInterpolant {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {G : ℝ → ℝ → Y → ℝ} {a b c d x y : ℝ}
    (hac : Integrable (G a c) ν) (had : Integrable (G a d) ν) (hbc : Integrable (G b c) ν)
    (hbd : Integrable (G b d) ν) :
    ∫ z, bilinearInterpolant (fun u v ↦ G u v z) a b c d x y ∂ν =
      bilinearInterpolant (fun u v ↦ ∫ z, G u v z ∂ν) a b c d x y := by
  unfold bilinearInterpolant
  rw [integral_linearInterpolant (integrable_linearInterpolant hac had)
    (integrable_linearInterpolant hbc hbd), integral_linearInterpolant hac had,
    integral_linearInterpolant hbc hbd]

/-- The bilinear interpolant in `(x, y)` of four integrable functions of the parameter is integrable
in the parameter. -/
theorem integrable_bilinearInterpolant {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {G : ℝ → ℝ → Y → ℝ} {a b c d x y : ℝ}
    (hac : Integrable (G a c) ν) (had : Integrable (G a d) ν) (hbc : Integrable (G b c) ν)
    (hbd : Integrable (G b d) ν) :
    Integrable (fun z ↦ bilinearInterpolant (fun u v ↦ G u v z) a b c d x y) ν :=
  integrable_linearInterpolant (integrable_linearInterpolant hac had)
    (integrable_linearInterpolant hbc hbd)

/-- **Part II, Lemma 4.4.** Let `K(x, y)` have pure second `x`-derivatives bounded by `M₁(y)` and
`M₂(y)` on `P = [a₁, b₁] × [a₂, b₂]` for every `y`. For `x ∈ P` and any measure `ν` in `y`,
`∫ |K(x, ·)| dν` is at most the bilinear interpolant of the four vertex integrals
`∫ |K(v, ·)| dν` plus `(x₁ - a₁)(b₁ - x₁)/2 ∫ M₁ dν + (x₂ - a₂)(b₂ - x₂)/2 ∫ M₂ dν`. -/
theorem integral_abs_le_of_corners {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {K Kx Kxx Ky Kyy : ℝ → ℝ → Y → ℝ} {M₁ M₂ : Y → ℝ} {a₁ b₁ a₂ b₂ x₁ x₂ : ℝ}
    (h₁ : a₁ < b₁) (h₂ : a₂ < b₂)
    (hcontX : ∀ y, ∀ v ∈ Icc a₂ b₂, ContinuousOn (fun u ↦ K u v y) (Icc a₁ b₁))
    (hderivX : ∀ y, ∀ v ∈ Icc a₂ b₂, ∀ u ∈ Ioo a₁ b₁,
      HasDerivAt (fun z ↦ K z v y) (Kx u v y) u)
    (hderivXX : ∀ y, ∀ v ∈ Icc a₂ b₂, ∀ u ∈ Ioo a₁ b₁,
      HasDerivAt (fun z ↦ Kx z v y) (Kxx u v y) u)
    (hboundX : ∀ y, ∀ v ∈ Icc a₂ b₂, ∀ u ∈ Ioo a₁ b₁, |Kxx u v y| ≤ M₁ y)
    (hcontY : ∀ y, ∀ u ∈ Icc a₁ b₁, ContinuousOn (fun v ↦ K u v y) (Icc a₂ b₂))
    (hderivY : ∀ y, ∀ u ∈ Icc a₁ b₁, ∀ v ∈ Ioo a₂ b₂,
      HasDerivAt (fun z ↦ K u z y) (Ky u v y) v)
    (hderivYY : ∀ y, ∀ u ∈ Icc a₁ b₁, ∀ v ∈ Ioo a₂ b₂,
      HasDerivAt (fun z ↦ Ky u z y) (Kyy u v y) v)
    (hboundY : ∀ y, ∀ u ∈ Icc a₁ b₁, ∀ v ∈ Ioo a₂ b₂, |Kyy u v y| ≤ M₂ y)
    (hK : Integrable (K x₁ x₂) ν) (hac : Integrable (K a₁ a₂) ν) (had : Integrable (K a₁ b₂) ν)
    (hbc : Integrable (K b₁ a₂) ν) (hbd : Integrable (K b₁ b₂) ν)
    (hM₁ : Integrable M₁ ν) (hM₂ : Integrable M₂ ν)
    (hx₁ : x₁ ∈ Icc a₁ b₁) (hx₂ : x₂ ∈ Icc a₂ b₂) :
    ∫ y, |K x₁ x₂ y| ∂ν ≤
      bilinearInterpolant (fun u v ↦ ∫ y, |K u v y| ∂ν) a₁ b₁ a₂ b₂ x₁ x₂ +
        (x₁ - a₁) * (b₁ - x₁) / 2 * ∫ y, M₁ y ∂ν + (x₂ - a₂) * (b₂ - x₂) / 2 * ∫ y, M₂ y ∂ν := by
  have hpt : ∀ y, |K x₁ x₂ y| ≤ bilinearInterpolant (fun u v ↦ |K u v y|) a₁ b₁ a₂ b₂ x₁ x₂ +
      ((x₁ - a₁) * (b₁ - x₁) / 2 * M₁ y + (x₂ - a₂) * (b₂ - x₂) / 2 * M₂ y) := by
    intro y
    have henv := abs_sub_bilinearInterpolant_le_envelope (f := fun u v ↦ K u v y)
      (fx := fun u v ↦ Kx u v y) (fxx := fun u v ↦ Kxx u v y) (fy := fun u v ↦ Ky u v y)
      (fyy := fun u v ↦ Kyy u v y) h₁ h₂ (hcontX y) (hderivX y) (hderivXX y) (hboundX y)
      (hcontY y) (hderivY y) (hderivYY y) (hboundY y) hx₁ hx₂
    have hB := abs_bilinearInterpolant_le_bilinearInterpolant_abs (f := fun u v ↦ K u v y)
      h₁ h₂ hx₁ hx₂
    have := abs_sub_abs_le_abs_sub (K x₁ x₂ y)
      (bilinearInterpolant (fun u v ↦ K u v y) a₁ b₁ a₂ b₂ x₁ x₂)
    have e1 : (x₁ - a₁) * (b₁ - x₁) / 2 * M₁ y = M₁ y * (x₁ - a₁) * (b₁ - x₁) / 2 := by ring
    have e2 : (x₂ - a₂) * (b₂ - x₂) / 2 * M₂ y = M₂ y * (x₂ - a₂) * (b₂ - x₂) / 2 := by ring
    rw [e1, e2]
    linarith
  have hBint : Integrable (fun y ↦ bilinearInterpolant (fun u v ↦ |K u v y|) a₁ b₁ a₂ b₂ x₁ x₂)
      ν := integrable_bilinearInterpolant (G := fun u v y ↦ |K u v y|) hac.abs had.abs hbc.abs
    hbd.abs
  have hEint : Integrable (fun y ↦ (x₁ - a₁) * (b₁ - x₁) / 2 * M₁ y +
      (x₂ - a₂) * (b₂ - x₂) / 2 * M₂ y) ν := (hM₁.const_mul _).fun_add (hM₂.const_mul _)
  refine (integral_mono hK.abs (hBint.fun_add hEint) hpt).trans (le_of_eq ?_)
  rw [integral_add hBint hEint, integral_add (hM₁.const_mul _) (hM₂.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_bilinearInterpolant (G := fun u v y ↦ |K u v y|) hac.abs had.abs hbc.abs hbd.abs]
  ring

/-- **Part II, Lemma 4.4.** With constant bounds `Mₓ`, `M_y` and a finite measure,
`∫ |K(x, ·)| dν ≤ ∑_v λ_v(x) ∫ |K(v, ·)| dν + (h₁² Mₓ / 8 + h₂² M_y / 8) ν(Y)`. -/
theorem integral_abs_le_of_corners_const {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    [IsFiniteMeasure ν] {K Kx Kxx Ky Kyy : ℝ → ℝ → Y → ℝ} {Mx My a₁ b₁ a₂ b₂ x₁ x₂ : ℝ}
    (h₁ : a₁ < b₁) (h₂ : a₂ < b₂) (hMx : 0 ≤ Mx) (hMy : 0 ≤ My)
    (hcontX : ∀ y, ∀ v ∈ Icc a₂ b₂, ContinuousOn (fun u ↦ K u v y) (Icc a₁ b₁))
    (hderivX : ∀ y, ∀ v ∈ Icc a₂ b₂, ∀ u ∈ Ioo a₁ b₁,
      HasDerivAt (fun z ↦ K z v y) (Kx u v y) u)
    (hderivXX : ∀ y, ∀ v ∈ Icc a₂ b₂, ∀ u ∈ Ioo a₁ b₁,
      HasDerivAt (fun z ↦ Kx z v y) (Kxx u v y) u)
    (hboundX : ∀ y, ∀ v ∈ Icc a₂ b₂, ∀ u ∈ Ioo a₁ b₁, |Kxx u v y| ≤ Mx)
    (hcontY : ∀ y, ∀ u ∈ Icc a₁ b₁, ContinuousOn (fun v ↦ K u v y) (Icc a₂ b₂))
    (hderivY : ∀ y, ∀ u ∈ Icc a₁ b₁, ∀ v ∈ Ioo a₂ b₂,
      HasDerivAt (fun z ↦ K u z y) (Ky u v y) v)
    (hderivYY : ∀ y, ∀ u ∈ Icc a₁ b₁, ∀ v ∈ Ioo a₂ b₂,
      HasDerivAt (fun z ↦ Ky u z y) (Kyy u v y) v)
    (hboundY : ∀ y, ∀ u ∈ Icc a₁ b₁, ∀ v ∈ Ioo a₂ b₂, |Kyy u v y| ≤ My)
    (hK : Integrable (K x₁ x₂) ν) (hac : Integrable (K a₁ a₂) ν) (had : Integrable (K a₁ b₂) ν)
    (hbc : Integrable (K b₁ a₂) ν) (hbd : Integrable (K b₁ b₂) ν)
    (hx₁ : x₁ ∈ Icc a₁ b₁) (hx₂ : x₂ ∈ Icc a₂ b₂) :
    ∫ y, |K x₁ x₂ y| ∂ν ≤
      bilinearInterpolant (fun u v ↦ ∫ y, |K u v y| ∂ν) a₁ b₁ a₂ b₂ x₁ x₂ +
        ((b₁ - a₁) ^ 2 / 8 * Mx + (b₂ - a₂) ^ 2 / 8 * My) * ν.real univ := by
  have h := integral_abs_le_of_corners (M₁ := fun _ ↦ Mx) (M₂ := fun _ ↦ My) h₁ h₂ hcontX
    hderivX hderivXX hboundX hcontY hderivY hderivYY hboundY hK hac had hbc hbd
    (integrable_const _) (integrable_const _) hx₁ hx₂
  simp only [integral_const, smul_eq_mul] at h
  refine h.trans ?_
  have hq₁ : (x₁ - a₁) * (b₁ - x₁) ≤ (b₁ - a₁) ^ 2 / 4 := by
    nlinarith [sq_nonneg (x₁ - (a₁ + b₁) / 2)]
  have hq₂ : (x₂ - a₂) * (b₂ - x₂) ≤ (b₂ - a₂) ^ 2 / 4 := by
    nlinarith [sq_nonneg (x₂ - (a₂ + b₂) / 2)]
  have hν : 0 ≤ ν.real univ := measureReal_nonneg
  have e1 : (x₁ - a₁) * (b₁ - x₁) / 2 * (ν.real univ * Mx) ≤
      (b₁ - a₁) ^ 2 / 8 * Mx * ν.real univ := by
    have := mul_le_mul_of_nonneg_right hq₁ (mul_nonneg hν hMx)
    nlinarith
  have e2 : (x₂ - a₂) * (b₂ - x₂) / 2 * (ν.real univ * My) ≤
      (b₂ - a₂) ^ 2 / 8 * My * ν.real univ := by
    have := mul_le_mul_of_nonneg_right hq₂ (mul_nonneg hν hMy)
    nlinarith
  nlinarith

/-! ### The tensor Simpson rule (Supp II (6.16)) -/

/-- The tensor Simpson rule on `[a, b] × [c, d]`: the area `h₁ h₂` times `∑ cᵢ cⱼ g(aᵢ, bⱼ)` with
the weights `c = (1, 4, 1) / 6` at the endpoints and midpoints. -/
noncomputable def tensorSimpson (g : ℝ → ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  (b - a) * (d - c) / 36 *
    ((g a c + 4 * g ((a + b) / 2) c + g b c) +
      4 * (g a ((c + d) / 2) + 4 * g ((a + b) / 2) ((c + d) / 2) + g b ((c + d) / 2)) +
      (g a d + 4 * g ((a + b) / 2) d + g b d))

/-- The one-panel Simpson bound for a set integral over `[a, b]`. -/
theorem abs_setIntegral_sub_simpson_le {f : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hf : ContDiffOn ℝ 4 f (Icc a b))
    (hC : ∀ x ∈ Icc a b, |iteratedDerivWithin 4 f (Icc a b) x| ≤ C) :
    |(∫ x in Icc a b, f x) - (b - a) * (f a + 4 * f ((a + b) / 2) + f b) / 6| ≤
      C * (b - a) ^ 5 / 2880 := by
  have h := CAS.Continuum.norm_integral_sub_simpsonRule_valueOn_le hab hf
    (fun x hx ↦ by rw [Real.norm_eq_abs]; exact hC x hx)
  rw [CAS.Continuum.simpsonRule_valueOn_eq_formula, Real.norm_eq_abs,
    intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc] at h
  exact h

/-- **Supp II (6.16).** For `g` continuous on `Q = [a, b] × [c, d]` with
fourth derivatives along the slices bounded by `Mₓ` and `M_y`,
`|∫_Q g - tensorSimpson g| ≤ h₁ h₂ (h₁⁴ Mₓ + h₂⁴ M_y) / 2880`. The rule is applied in `y` on every
vertical slice and then in `x`; only the pure fourth derivatives enter. -/
theorem abs_setIntegral_sub_tensorSimpson_le {g : ℝ → ℝ → ℝ} {a b c d Mx My : ℝ}
    (hab : a < b) (hcd : c < d)
    (hg : ContinuousOn (Function.uncurry g) (Icc a b ×ˢ Icc c d))
    (hx : ∀ y ∈ Icc c d, ContDiffOn ℝ 4 (fun x ↦ g x y) (Icc a b))
    (hMx : ∀ y ∈ Icc c d, ∀ x ∈ Icc a b,
      |iteratedDerivWithin 4 (fun x ↦ g x y) (Icc a b) x| ≤ Mx)
    (hy : ∀ x ∈ Icc a b, ContDiffOn ℝ 4 (g x) (Icc c d))
    (hMy : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d, |iteratedDerivWithin 4 (g x) (Icc c d) y| ≤ My) :
    |(∫ p in Icc a b ×ˢ Icc c d, g p.1 p.2) - tensorSimpson g a b c d| ≤
      (b - a) * (d - c) / 2880 * ((b - a) ^ 4 * Mx + (d - c) ^ 4 * My) := by
  have hK : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hint : IntegrableOn (fun p : ℝ × ℝ ↦ g p.1 p.2) (Icc a b ×ˢ Icc c d) :=
    hg.integrableOn_compact hK
  have hfub : ∫ p in Icc a b ×ˢ Icc c d, g p.1 p.2 = ∫ x in Icc a b, ∫ y in Icc c d, g x y := by
    rw [Measure.volume_eq_prod]
    exact setIntegral_prod (fun p : ℝ × ℝ ↦ g p.1 p.2) (by rwa [← Measure.volume_eq_prod])
  have hJint : IntegrableOn (fun x ↦ ∫ y in Icc c d, g x y) (Icc a b) := by
    have h1 : Integrable (fun p : ℝ × ℝ ↦ g p.1 p.2)
        ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact hint
    exact h1.integral_prod_left
  have hc : c ∈ Icc c d := ⟨le_rfl, hcd.le⟩
  have hd : d ∈ Icc c d := ⟨hcd.le, le_rfl⟩
  have hn : (c + d) / 2 ∈ Icc c d := ⟨by linarith, by linarith⟩
  have hrow (y : ℝ) (hy' : y ∈ Icc c d) : IntegrableOn (fun x ↦ g x y) (Icc a b) :=
    (hx y hy').continuousOn.integrableOn_compact isCompact_Icc
  set Sy : ℝ → ℝ := fun x ↦ (d - c) * (g x c + 4 * g x ((c + d) / 2) + g x d) / 6 with hSydef
  have hSyint : IntegrableOn Sy (Icc a b) := by
    simp only [Sy]
    exact ((((hrow c hc).fun_add ((hrow _ hn).const_mul 4)).fun_add (hrow d hd)).const_mul
      (d - c)).div_const 6
  have hinner : ∀ x ∈ Icc a b, ‖(∫ y in Icc c d, g x y) - Sy x‖ ≤ My * (d - c) ^ 5 / 2880 :=
    fun x hx' ↦ by
      rw [Real.norm_eq_abs]
      exact abs_setIntegral_sub_simpson_le hcd (hy x hx') (hMy x hx')
  have houter := norm_setIntegral_le_of_norm_le_const
    (measure_Icc_lt_top (μ := volume) (a := a) (b := b)) hinner
  rw [Real.norm_eq_abs, Real.volume_real_Icc_of_le hab.le,
    integral_sub hJint hSyint] at houter
  have hSy : ∫ x in Icc a b, Sy x = (d - c) / 6 * ((∫ x in Icc a b, g x c) +
      4 * (∫ x in Icc a b, g x ((c + d) / 2)) + ∫ x in Icc a b, g x d) := by
    simp only [Sy]
    rw [integral_div, integral_const_mul,
      integral_add ((hrow c hc).fun_add ((hrow _ hn).const_mul 4)) (hrow d hd),
      integral_add (hrow c hc) ((hrow _ hn).const_mul 4), integral_const_mul]
    ring
  have ec := abs_setIntegral_sub_simpson_le hab (hx c hc) (hMx c hc)
  have en := abs_setIntegral_sub_simpson_le hab (hx _ hn) (hMx _ hn)
  have ed := abs_setIntegral_sub_simpson_le hab (hx d hd) (hMx d hd)
  set Eo := (∫ x in Icc a b, ∫ y in Icc c d, g x y) - ∫ x in Icc a b, Sy x
  set Ec := (∫ x in Icc a b, g x c) - (b - a) * (g a c + 4 * g ((a + b) / 2) c + g b c) / 6
  set En := (∫ x in Icc a b, g x ((c + d) / 2)) - (b - a) * (g a ((c + d) / 2) +
    4 * g ((a + b) / 2) ((c + d) / 2) + g b ((c + d) / 2)) / 6
  set Ed := (∫ x in Icc a b, g x d) - (b - a) * (g a d + 4 * g ((a + b) / 2) d + g b d) / 6
  have hX : (∫ p in Icc a b ×ˢ Icc c d, g p.1 p.2) - tensorSimpson g a b c d =
      Eo + (d - c) / 6 * (Ec + 4 * En + Ed) := by
    rw [hfub]
    simp only [Eo, Ec, En, Ed, hSy, tensorSimpson]
    ring
  have hdc : 0 < (d - c) / 6 := by linarith
  rw [hX]
  calc |Eo + (d - c) / 6 * (Ec + 4 * En + Ed)| ≤
        |Eo| + (d - c) / 6 * (|Ec| + 4 * |En| + |Ed|) := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_pos hdc]
        gcongr
        calc |Ec + 4 * En + Ed| ≤ |Ec| + |4 * En| + |Ed| := abs_add_three _ _ _
          _ = |Ec| + 4 * |En| + |Ed| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    _ ≤ My * (d - c) ^ 5 / 2880 * (b - a) + (d - c) / 6 *
        (Mx * (b - a) ^ 5 / 2880 + 4 * (Mx * (b - a) ^ 5 / 2880) + Mx * (b - a) ^ 5 / 2880) := by
        gcongr
    _ = (b - a) * (d - c) / 2880 * ((b - a) ^ 4 * Mx + (d - c) ^ 4 * My) := by ring

end PDE.Analysis.Approximation
