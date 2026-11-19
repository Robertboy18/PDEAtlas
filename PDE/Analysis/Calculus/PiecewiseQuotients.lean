/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PDE.Analysis.Calculus.Radial.RealPower
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import PDE.FDeriv.Calculus

/-!
# Piecewise bounds of quotients

Elementary estimates behind the cellwise bounds of Chen and Hou: lower bounds of `A + B/x`, of
`f(x)/x` and of `I_k(f)(x) = x^{-k} ∫₀ˣ f(s) s^{k-1} ds` on a mesh interval, the angular factors
`x²/r²` on a cell, the logarithmic derivatives of radial weights `ρ = ∑ₗ sₗ |x|^{cₗ}`, and the
Hölder quotients of `y²/(x² + y²)` and of `F/|x|^{1/2}`. The vertical segments of (8.74) reduce to
the horizontal case through `y²/(x² + y²) = 1 - x²/(x² + y²)`.

Upper bounds follow by applying the lower bounds to `-f`.

## Main results

* `min_div_le_div_of_le_deriv`: if `f' ≥ m` on `(a, b)`, then on `[a, b]`
  `f(x)/x ≥ min(f(a)/a, (f(a) + (b - a) m)/b)`, the bound of `f/x` of Section 8.9.1.
* `le_div_of_le_deriv_of_eq_zero`: on the first interval, `f(0) = 0` and `f' ≥ m` give
  `f(x)/x ≥ m`.
* `le_div_integral_mul_pow`: the lower bound of `I_k(f)` on a mesh interval from a lower bound of
  `f` there and of the integral up to its left end.
* `sq_div_sq_add_sq_mem_Icc`: `x_l²/(x_l² + y_u²) ≤ x²/r² ≤ x_u²/(x_u² + y_l²)` on a cell (8.35).
* `mul_partialDeriv_radialSum`: `xᵢ ∂ᵢρ = (xᵢ²/|x|²) ∑ₗ sₗ cₗ |x|^{cₗ}` (8.34).
* `abs_sq_div_sub_mul_le`: the Hölder quotient of `y²/(x² + y²)` along a horizontal segment,
  weighted by `|w|^{1/2}` with `|w| ≤ |(z, y)|`, is at most `M₂ y²/(x² + y²)`,
  `M₂ = (x + z)|z - x|^{1/2}/(y² + z²)^{3/4}` (8.72).
* `add_mul_sqrt_sub_le`: `(x + z)|z - x|^{1/2} ≤ (32/27)^{1/2} z^{3/2}`.
* `abs_div_sqrt_sub_div_sqrt_le`: the splitting
  `δ(F/|x|^{1/2}) ≤ (|δF|/d) M₃^{1/2} + |F(x)/x₁| M₄ M₅` of Section 8.9.4.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Supplementary material I (in the
  same PDF), Section 8.3.2, (8.34)-(8.35), Section 8.4.1, (8.40), Section 8.9.1, Section 8.9.2,
  (8.72)-(8.74), and Section 8.9.4. <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set MeasureTheory intervalIntegral

namespace PDE.Analysis

/-- On `[a, b]` with `0 < a`, `A + min(B/a, B/b) ≤ A + B/x`. -/
theorem add_min_div_le {A B a b x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    A + min (B / a) (B / b) ≤ A + B / x := by
  have hx : 0 < x := ha.trans_le hax
  have hb : 0 < b := hx.trans_le hxb
  gcongr
  rcases le_total 0 B with hB | hB
  · exact (min_le_right _ _).trans (div_le_div_of_nonneg_left hB hx hxb)
  · refine (min_le_left _ _).trans ?_
    rw [div_le_div_iff₀ ha hx]
    nlinarith

/-- **The bound of `f/x` on a cell**, Supplementary material I, Section 8.9.1: if `f` is
continuous on `[a, b]`, `0 < a`, differentiable on `(a, b)` with `f' ≥ m`, then for `x ∈ [a, b]`,
`min(f(a)/a, (f(a) + (b - a) m)/b) ≤ f(x)/x`. -/
theorem min_div_le_div_of_le_deriv {f : ℝ → ℝ} {a b m x : ℝ} (ha : 0 < a)
    (hf : ContinuousOn f (Icc a b)) (hf' : DifferentiableOn ℝ f (Ioo a b))
    (hm : ∀ y ∈ Ioo a b, m ≤ deriv f y) (hx : x ∈ Icc a b) :
    min (f a / a) ((f a + (b - a) * m) / b) ≤ f x / x := by
  have hab : a ≤ b := hx.1.trans hx.2
  have hx0 : 0 < x := ha.trans_le hx.1
  have hb : 0 < b := hx0.trans_le hx.2
  have hmv := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hf
    (by rwa [interior_Icc]) (by rwa [interior_Icc]) a ⟨le_rfl, hab⟩ x hx hx.1
  have h1 : (f a + m * (x - a)) / x ≤ f x / x := by gcongr; linarith
  have h2 := add_min_div_le (A := m) (B := f a - m * a) ha hx.1 hx.2
  have e1 : m + (f a - m * a) / a = f a / a := by field_simp; ring
  have e2 : m + (f a - m * a) / b = (f a + (b - a) * m) / b := by field_simp; ring
  have e3 : m + (f a - m * a) / x = (f a + m * (x - a)) / x := by field_simp; ring
  rw [← e3] at h1
  calc min (f a / a) ((f a + (b - a) * m) / b) = m + min ((f a - m * a) / a)
        ((f a - m * a) / b) := by rw [← e1, ← e2, min_add_add_left]
    _ ≤ _ := h2.trans h1

/-- **The first cell**: if `f(0) = 0` and `f' ≥ m` on `(0, b)`, with `f` continuous on `[0, b]`,
then `m ≤ f(x)/x` for `x ∈ (0, b]`. -/
theorem le_div_of_le_deriv_of_eq_zero {f : ℝ → ℝ} {b m x : ℝ}
    (hf : ContinuousOn f (Icc 0 b)) (hf' : DifferentiableOn ℝ f (Ioo 0 b))
    (hm : ∀ y ∈ Ioo 0 b, m ≤ deriv f y) (h0 : f 0 = 0) (hx : x ∈ Ioc 0 b) : m ≤ f x / x := by
  have hmv := (convex_Icc 0 b).mul_sub_le_image_sub_of_le_deriv hf
    (by rwa [interior_Icc]) (by rwa [interior_Icc]) 0 ⟨le_rfl, hx.1.le.trans hx.2⟩ x
    ⟨hx.1.le, hx.2⟩ hx.1.le
  rw [h0, sub_zero, sub_zero] at hmv
  rw [le_div_iff₀ hx.1]
  linarith

/-- `∫ₐˣ f(s) s^{k-1} ds ≥ m (x^k - a^k)/k` if `f ≥ m` on `[a, x]`, `0 ≤ a ≤ x` and `k ≥ 1`. -/
theorem mul_sub_pow_div_le_integral {f : ℝ → ℝ} {a x m : ℝ} {k : ℕ} (hk : 1 ≤ k) (ha : 0 ≤ a)
    (hax : a ≤ x) (hf : IntervalIntegrable (fun s ↦ f s * s ^ (k - 1)) volume a x)
    (hm : ∀ s ∈ Icc a x, m ≤ f s) :
    m * (x ^ k - a ^ k) / k ≤ ∫ s in a..x, f s * s ^ (k - 1) := by
  have hint : ∫ s in a..x, m * s ^ (k - 1) = m * (x ^ k - a ^ k) / k := by
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
    rw [hk']
    have : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast hk'
    rw [this]
    ring
  rw [← hint]
  refine intervalIntegral.integral_mono_on hax ?_ hf fun s hs ↦ ?_
  · exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _
  · exact mul_le_mul_of_nonneg_right (hm s hs) (pow_nonneg (ha.trans hs.1) _)

/-- **The bound of `I_k(f)` on a cell**, Supplementary material I, Section 8.9.1: if
`∫₀ᵃ f(s) s^{k-1} ds ≥ S/k`, `f ≥ m` on `[a, b]`, `0 < a` and `x ∈ [a, b]`, then
`I_k(f)(x) = x^{-k} ∫₀ˣ f(s) s^{k-1} ds ≥ m/k + min((S - aᵏ m)/aᵏ, (S - aᵏ m)/bᵏ)/k`. -/
theorem le_div_integral_mul_pow {f : ℝ → ℝ} {a b m S x : ℝ} {k : ℕ} (hk : 1 ≤ k) (ha : 0 < a)
    (hx : x ∈ Icc a b) (hf0 : IntervalIntegrable (fun s ↦ f s * s ^ (k - 1)) volume 0 a)
    (hf : IntervalIntegrable (fun s ↦ f s * s ^ (k - 1)) volume a x)
    (hS : S / k ≤ ∫ s in (0 : ℝ)..a, f s * s ^ (k - 1)) (hm : ∀ s ∈ Icc a x, m ≤ f s) :
    m / k + min ((S - a ^ k * m) / a ^ k) ((S - a ^ k * m) / b ^ k) / k ≤
      (∫ s in (0 : ℝ)..x, f s * s ^ (k - 1)) / x ^ k := by
  have hx0 : 0 < x := ha.trans_le hx.1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hxk : 0 < x ^ k := pow_pos hx0 k
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hf0 hf
  have hpiece := mul_sub_pow_div_le_integral hk ha.le hx.1 hf hm
  have hlow : (S + m * (x ^ k - a ^ k)) / k ≤ ∫ s in (0 : ℝ)..x, f s * s ^ (k - 1) := by
    rw [← hsplit, add_div]
    exact add_le_add hS hpiece
  have hmin := add_min_div_le (A := m) (B := S - a ^ k * m) (pow_pos ha k)
    (pow_le_pow_left₀ ha.le hx.1 k) (pow_le_pow_left₀ hx0.le hx.2 k)
  have e : (m + (S - a ^ k * m) / x ^ k) / k = (S + m * (x ^ k - a ^ k)) / k / x ^ k := by
    field_simp
    ring
  calc m / k + min ((S - a ^ k * m) / a ^ k) ((S - a ^ k * m) / b ^ k) / k =
        (m + min ((S - a ^ k * m) / a ^ k) ((S - a ^ k * m) / b ^ k)) / k := by ring
    _ ≤ (m + (S - a ^ k * m) / x ^ k) / k := by gcongr
    _ = (S + m * (x ^ k - a ^ k)) / k / x ^ k := e
    _ ≤ _ := by gcongr

/-! ### The angular factors on a cell -/

/-- `t/(t + s)` is increasing in `t ≥ 0` and decreasing in `s ≥ 0` (with `0/0 = 0`). -/
theorem div_add_le_div_add {t t' s s' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') (hs : 0 ≤ s')
    (hss : s' ≤ s) : t / (t + s) ≤ t' / (t' + s') := by
  have ht' : 0 ≤ t' := ht.trans htt
  have hs0 : 0 ≤ s := hs.trans hss
  rcases (add_nonneg ht hs0).eq_or_lt with h1 | h1
  · rw [← h1, div_zero]
    exact div_nonneg ht' (add_nonneg ht' hs)
  rcases (add_nonneg ht' hs).eq_or_lt with h2 | h2
  · have h3 : t' = 0 := by linarith
    have h4 : t = 0 := by linarith
    rw [h3, h4, zero_div, zero_div]
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg ht hs, mul_nonneg (sub_nonneg.2 htt) (sub_nonneg.2 hss)]

/-- **Supplementary material I (8.35)**: on a cell `[x_l, x_u] × [y_l, y_u]` of the closed
quadrant, `x_l²/(x_l² + y_u²) ≤ x²/(x² + y²) ≤ x_u²/(x_u² + y_l²)` (with `0/0 = 0`). -/
theorem sq_div_sq_add_sq_mem_Icc {x y xl xu yl yu : ℝ} (hxl : 0 ≤ xl) (hx : x ∈ Icc xl xu)
    (hyl : 0 ≤ yl) (hy : y ∈ Icc yl yu) :
    xl ^ 2 / (xl ^ 2 + yu ^ 2) ≤ x ^ 2 / (x ^ 2 + y ^ 2) ∧
      x ^ 2 / (x ^ 2 + y ^ 2) ≤ xu ^ 2 / (xu ^ 2 + yl ^ 2) := by
  have hx0 : 0 ≤ x := hxl.trans hx.1
  have hy0 : 0 ≤ y := hyl.trans hy.1
  exact ⟨div_add_le_div_add (sq_nonneg _) (pow_le_pow_left₀ hxl hx.1 2) (sq_nonneg _)
      (pow_le_pow_left₀ hy0 hy.2 2),
    div_add_le_div_add (sq_nonneg _) (pow_le_pow_left₀ hx0 hx.2 2) (sq_nonneg _)
      (pow_le_pow_left₀ hyl hy.1 2)⟩

/-! ### Radial weights -/

/-- **Supplementary material I (8.34)**: for a radial weight `ρ = ∑ₗ sₗ |x|^{cₗ}` and `x ≠ 0`,
`xᵢ ∂ᵢρ(x) = (xᵢ²/|x|²) ∑ₗ sₗ cₗ |x|^{cₗ}`. -/
theorem mul_partialDeriv_radialSum {n m : ℕ} (s c : Fin m → ℝ) (i : Fin n) {x : ℝ^n}
    (hx : x ≠ 0) :
    x i * (∂[i] (fun y : ℝ^n ↦ ∑ l, s l * ‖y‖ ^ c l)) x =
      x i ^ 2 / ‖x‖ ^ 2 * ∑ l, s l * c l * ‖x‖ ^ c l := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hd : ∀ l ∈ Finset.univ, DifferentiableAt ℝ (fun y : ℝ^n ↦ s l * ‖y‖ ^ c l) x := fun l _ ↦
    ((PDE.Analysis.Radial.contDiffAt_norm_rpow (c l) hx (k := 1)).differentiableAt
      (by norm_num)).const_mul (s l)
  rw [partialDeriv_sum Finset.univ hd i, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  have hc : (∂[i] (fun y : ℝ^n ↦ s l * ‖y‖ ^ c l)) x =
      s l * (∂[i] (fun y : ℝ^n ↦ ‖y‖ ^ c l)) x := by
    simpa [smul_eq_mul] using partialDeriv_const_smul (i := i) (f := fun y : ℝ^n ↦ ‖y‖ ^ c l)
      (x := x) (s l)
  rw [hc, PDE.Analysis.Radial.partialDeriv_norm_rpow _ _ hx, Real.rpow_sub hr, Real.rpow_two]
  field_simp

/-! ### The angular factor and the half power -/

/-- **Supplementary material I (8.72)**: for `0 ≤ a < b`, `y > 0` and `r ≤ (b² + y²)^{1/2}`,
`|y²/(a² + y²) - y²/(b² + y²)| (b - a)^{-1/2} r^{1/2} ≤
(a + b)(b - a)^{1/2}/(b² + y²)^{3/4} · y²/(a² + y²)`, the bound `M M₂ ≤ M₂ sin²β` with `M₂` the
second factor. -/
theorem abs_sq_div_sub_mul_le {a b y r : ℝ} (ha : 0 ≤ a) (hab : a < b) (hy : 0 < y)
    (hr : r ≤ √(b ^ 2 + y ^ 2)) :
    |y ^ 2 / (a ^ 2 + y ^ 2) - y ^ 2 / (b ^ 2 + y ^ 2)| / √(b - a) * √r ≤
      (a + b) * √(b - a) / (b ^ 2 + y ^ 2) ^ (3 / 4 : ℝ) * (y ^ 2 / (a ^ 2 + y ^ 2)) := by
  set X := b ^ 2 + y ^ 2
  have hX : 0 < X := by positivity
  have hA : 0 < a ^ 2 + y ^ 2 := by positivity
  have hd : 0 < b - a := sub_pos.2 hab
  have hab0 : 0 ≤ a + b := by linarith
  set s := X ^ (1 / 4 : ℝ)
  have hs : 0 < s := by positivity
  have hs4 : s ^ 4 = X := by rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]; norm_num
  have hs3 : X ^ (3 / 4 : ℝ) = s ^ 3 := by rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]; norm_num
  have hrs : √r ≤ s := (Real.sqrt_le_left hs.le).2 <| hr.trans_eq <| by
    rw [← hs4, show s ^ 4 = (s ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hdiff : |y ^ 2 / (a ^ 2 + y ^ 2) - y ^ 2 / X| / √(b - a) =
      (a + b) * √(b - a) * (y ^ 2 / (a ^ 2 + y ^ 2)) / s ^ 4 := by
    rw [abs_of_nonneg (sub_nonneg.2 (div_le_div_of_nonneg_left (sq_nonneg y) hA
      (by nlinarith : a ^ 2 + y ^ 2 ≤ b ^ 2 + y ^ 2))), hs4]
    field_simp
    rw [Real.sq_sqrt hd.le]
    ring
  rw [hdiff, hs3]
  calc _ ≤ (a + b) * √(b - a) * (y ^ 2 / (a ^ 2 + y ^ 2)) / s ^ 4 * s :=
        mul_le_mul_of_nonneg_left hrs (div_nonneg (by positivity) (by positivity))
    _ = _ := by field_simp

/-- **Supplementary material I (8.73)**: for `0 ≤ a ≤ b`,
`(a + b)(b - a)^{1/2} ≤ (32/27)^{1/2} b^{3/2}`, from `(1 - λ)(1 + λ)² ≤ 32/27`. -/
theorem add_mul_sqrt_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (a + b) * √(b - a) ≤ √(32 / 27) * (b * √b) := by
  have hb : 0 ≤ b := ha.trans hab
  have hd : 0 ≤ b - a := sub_nonneg.2 hab
  have hL : 0 ≤ (a + b) * √(b - a) := by positivity
  have hR : 0 ≤ √(32 / 27) * (b * √b) := by positivity
  refine (pow_le_pow_iff_left₀ hL hR (by norm_num : (2 : ℕ) ≠ 0)).1 ?_
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hd, Real.sq_sqrt (by norm_num),
    Real.sq_sqrt hb]
  nlinarith [mul_nonneg (sq_nonneg (3 * a - b)) (by positivity : (0 : ℝ) ≤ a / 9 + 5 * b / 27)]

/-- **Supplementary material I, Section 8.9.4**: for `p, q, d, x₁ > 0` (`p = |x|`, `q = |y|`,
`d = |xᵢ - yᵢ|`),
`|F_y/q^{1/2} - F_x/p^{1/2}| / d^{1/2} ≤ (|F_y - F_x|/d) (d/q)^{1/2} +
|F_x/x₁| · x₁/(p^{1/2} q^{1/2}) · |q^{1/2} - p^{1/2}|/d^{1/2}`, the splitting
`T₁ M₃^{1/2} + T₂ M₄ M₅`. -/
theorem abs_div_sqrt_sub_div_sqrt_le {Fx Fy p q d x₁ : ℝ} (hp : 0 < p) (hq : 0 < q) (hd : 0 < d)
    (hx₁ : 0 < x₁) :
    |Fy / √q - Fx / √p| / √d ≤
      |Fy - Fx| / d * √(d / q) + |Fx / x₁| * (x₁ / (√p * √q)) * (|√q - √p| / √d) := by
  have sp := Real.sqrt_pos.2 hp
  have sq := Real.sqrt_pos.2 hq
  have sd := Real.sqrt_pos.2 hd
  have hsplit : Fy / √q - Fx / √p = (Fy - Fx) / √q + Fx * (√p - √q) / (√p * √q) := by
    field_simp
    ring
  have e1 : |(Fy - Fx) / √q| / √d = |Fy - Fx| / d * √(d / q) := by
    rw [abs_div, abs_of_pos sq, Real.sqrt_div hd.le]
    field_simp
    rw [Real.sq_sqrt hd.le]
  have e2 : |Fx * (√p - √q) / (√p * √q)| / √d =
      |Fx / x₁| * (x₁ / (√p * √q)) * (|√q - √p| / √d) := by
    rw [abs_div, abs_mul, abs_div, abs_of_pos (mul_pos sp sq), abs_of_pos hx₁, abs_sub_comm]
    field_simp
  rw [hsplit]
  calc |(Fy - Fx) / √q + Fx * (√p - √q) / (√p * √q)| / √d ≤
        (|(Fy - Fx) / √q| + |Fx * (√p - √q) / (√p * √q)|) / √d := by
        gcongr
        exact abs_add_le _ _
    _ = _ := by rw [add_div, e1, e2]

private theorem abs_sum_mul_rpow_le {m : ℕ} {s c : Fin m → ℝ} {t K : ℝ} (ht : 0 < t)
    (hs : ∀ l, 0 ≤ s l) (hc : ∀ l, |c l| ≤ K) :
    |∑ l, s l * c l * t ^ c l| ≤ K * ∑ l, s l * t ^ c l := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
  have hp : 0 < t ^ c l := Real.rpow_pos_of_pos ht _
  rw [abs_mul, abs_mul, abs_of_nonneg (hs l), abs_of_pos hp]
  linarith [mul_le_mul_of_nonneg_right (hc l) (mul_nonneg (hs l) hp.le)]

/-- **The logarithmic derivative of a radial power sum**, Supplementary material I, Section 8.4.1
(the bound of `J₂` for `φ₄`): for `ρ = ∑ₗ sₗ |x|^{cₗ}` with `sₗ ≥ 0`, `|cₗ| ≤ K` and `ρ(x) > 0`,
`|xᵢ ∂ᵢρ(x)/ρ(x)| ≤ K xᵢ²/|x|² ≤ K`. -/
theorem abs_mul_partialDeriv_div_radialSum_le {n m : ℕ} (s c : Fin m → ℝ) (i : Fin n) {x : ℝ^n}
    (hx : x ≠ 0) {K : ℝ} (hs : ∀ l, 0 ≤ s l) (hc : ∀ l, |c l| ≤ K)
    (hρ : 0 < ∑ l, s l * ‖x‖ ^ c l) :
    |x i * (∂[i] (fun y : ℝ^n ↦ ∑ l, s l * ‖y‖ ^ c l)) x / ∑ l, s l * ‖x‖ ^ c l| ≤
      K * (x i ^ 2 / ‖x‖ ^ 2) := by
  have hq : 0 ≤ x i ^ 2 / ‖x‖ ^ 2 := by positivity
  rw [mul_partialDeriv_radialSum s c i hx, abs_div, abs_mul, abs_of_nonneg hq, abs_of_pos hρ,
    div_le_iff₀ hρ]
  exact (mul_le_mul_of_nonneg_left (abs_sum_mul_rpow_le (norm_pos_iff.2 hx) hs hc) hq).trans_eq
    (by ring)

/-- The factor `xᵢ²/|x|²` is at most one. -/
theorem sq_div_norm_sq_le_one {n : ℕ} (x : ℝ^n) (i : Fin n) : x i ^ 2 / ‖x‖ ^ 2 ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [div_le_one (by positivity)]
    have h := PiLp.norm_apply_le x i
    rw [Real.norm_eq_abs] at h
    nlinarith [abs_nonneg (x i), sq_abs (x i)]

/-- `|xᵢ ∂ᵢρ(x)| ≤ K (xᵢ²/|x|²) ρ(x)` for a radial power sum `ρ = ∑ₗ sₗ |x|^{cₗ}` with `sₗ ≥ 0`
and `|cₗ| ≤ K`. -/
theorem abs_mul_partialDeriv_radialSum_le {n m : ℕ} (s c : Fin m → ℝ) (i : Fin n) {x : ℝ^n}
    (hx : x ≠ 0) {K : ℝ} (hs : ∀ l, 0 ≤ s l) (hc : ∀ l, |c l| ≤ K) :
    |x i * (∂[i] (fun y : ℝ^n ↦ ∑ l, s l * ‖y‖ ^ c l)) x| ≤
      K * (x i ^ 2 / ‖x‖ ^ 2) * ∑ l, s l * ‖x‖ ^ c l := by
  have hq : 0 ≤ x i ^ 2 / ‖x‖ ^ 2 := by positivity
  rw [mul_partialDeriv_radialSum s c i hx, abs_mul, abs_of_nonneg hq]
  exact (mul_le_mul_of_nonneg_left (abs_sum_mul_rpow_le (norm_pos_iff.2 hx) hs hc) hq).trans_eq
    (by ring)

/-- **The logarithmic derivatives of a mixed weight**, Supplementary material I, Section 8.4.1,
(8.40): for `φ = |x₁|^{-1/2} P + Q` with radial power sums `P`, `Q` with nonnegative
coefficients and exponents bounded by `K`, on `{x₁ > 0}`,
`|x₁ ∂₁φ| ≤ (1/2 + K) φ` and `|x₂ ∂₂φ| ≤ K φ`, from
`x₁ ∂₁φ = -P/(2 x₁^{1/2}) + x₁^{-1/2} x₁ ∂₁P + x₁ ∂₁Q` and `x₂ ∂₂φ = x₁^{-1/2} x₂ ∂₂P + x₂ ∂₂Q`. -/
theorem abs_mul_partialDeriv_mixedSum_le {m₁ m₂ : ℕ} (s c : Fin m₁ → ℝ) (s' c' : Fin m₂ → ℝ)
    {x : ℝ^2} (hx0 : 0 < x 0) {K : ℝ} (hK : 0 ≤ K) (hs : ∀ l, 0 ≤ s l) (hc : ∀ l, |c l| ≤ K)
    (hs' : ∀ l, 0 ≤ s' l) (hc' : ∀ l, |c' l| ≤ K) (j : Fin 2) :
    |x j * (∂[j] (fun y : ℝ^2 ↦ |y 0| ^ (-(1 / 2) : ℝ) * ∑ l, s l * ‖y‖ ^ c l +
        ∑ l, s' l * ‖y‖ ^ c' l)) x| ≤
      ((if j = 0 then 1 / 2 else 0) + K) *
        (|x 0| ^ (-(1 / 2) : ℝ) * ∑ l, s l * ‖x‖ ^ c l + ∑ l, s' l * ‖x‖ ^ c' l) := by
  have hx : x ≠ 0 := fun h ↦ by simp [h] at hx0
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hdiff {m : ℕ} (s c : Fin m → ℝ) :
      DifferentiableAt ℝ (fun y : ℝ^2 ↦ ∑ l, s l * ‖y‖ ^ c l) x :=
    .fun_sum fun l _ ↦ ((Radial.contDiffAt_norm_rpow (c l) hx (k := 1)).differentiableAt
      (by norm_num)).const_mul (s l)
  set P : ℝ^2 → ℝ := fun y ↦ ∑ l, s l * ‖y‖ ^ c l
  set Q : ℝ^2 → ℝ := fun y ↦ ∑ l, s' l * ‖y‖ ^ c' l
  have hP0 : 0 ≤ P x := Finset.sum_nonneg fun l _ ↦ mul_nonneg (hs l) (Real.rpow_nonneg hr.le _)
  have hQ0 : 0 ≤ Q x := Finset.sum_nonneg fun l _ ↦ mul_nonneg (hs' l) (Real.rpow_nonneg hr.le _)
  have hq := mul_le_of_le_one_right hK (sq_div_norm_sq_le_one x j)
  have hP : |x j * (∂[j] P) x| ≤ K * P x :=
    (abs_mul_partialDeriv_radialSum_le s c j hx hs hc).trans (mul_le_mul_of_nonneg_right hq hP0)
  have hQ : |x j * (∂[j] Q) x| ≤ K * Q x :=
    (abs_mul_partialDeriv_radialSum_le s' c' j hx hs' hc').trans
      (mul_le_mul_of_nonneg_right hq hQ0)
  -- near `x` the weight is `x₁^{-1/2} P + Q`
  set a : ℝ → ℝ := fun t ↦ t ^ (-(1 / 2) : ℝ)
  have hga : HasDerivAt a (-(1 / 2) * x 0 ^ (-(1 / 2) - 1 : ℝ)) (x 0) :=
    Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
  have hloc : (fun y : ℝ^2 ↦ |y 0| ^ (-(1 / 2) : ℝ) * P y + Q y) =ᶠ[nhds x]
      fun y ↦ a (y 0) * P y + Q y := by
    filter_upwards [(isOpen_lt continuous_const
      (EuclideanSpace.proj (0 : Fin 2)).continuous).mem_nhds hx0] with y (hy : 0 < y 0)
    simp only [a, abs_of_pos hy]
  have hda : DifferentiableAt ℝ (fun y : ℝ^2 ↦ a (y 0)) x :=
    (hga.differentiableAt.comp x
      (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt :)
  have hderiv : (∂[j] (fun y : ℝ^2 ↦ |y 0| ^ (-(1 / 2) : ℝ) * P y + Q y)) x =
      (if j = 0 then 1 else 0) * (-(1 / 2) * x 0 ^ (-(1 / 2) - 1 : ℝ)) * P x +
        a (x 0) * (∂[j] P) x + (∂[j] Q) x := by
    rw [partialDeriv_congr_nhds j hloc, partialDeriv_add (hda.fun_mul (hdiff s c)) (hdiff s' c'),
      partialDeriv_mul hda (hdiff s c), partialDeriv_comp_coord j 0 hga.differentiableAt,
      hga.deriv, smul_eq_mul]
  have ha0 : 0 < a (x 0) := Real.rpow_pos_of_pos hx0 _
  have hPa : |a (x 0) * (x j * (∂[j] P) x)| ≤ K * (a (x 0) * P x) := by
    rw [abs_mul, abs_of_pos ha0]
    linarith [mul_le_mul_of_nonneg_left hP ha0.le]
  -- `x₁ ∂₁(x₁^{-1/2}) = -x₁^{-1/2}/2`
  have hpow : x 0 * x 0 ^ (-(1 / 2) - 1 : ℝ) * P x = a (x 0) * P x := by
    simp only [a]
    rw [show (-(1 / 2) - 1 : ℝ) = -(1 / 2) + -1 by ring, Real.rpow_add hx0, Real.rpow_neg_one]
    field_simp
  have hAP := mul_nonneg ha0.le hP0
  change |x j * (∂[j] (fun y : ℝ^2 ↦ |y 0| ^ (-(1 / 2) : ℝ) * P y + Q y)) x| ≤ _
  rw [hderiv, show |x 0| ^ (-(1 / 2) : ℝ) = a (x 0) by simp [a, abs_of_pos hx0]]
  change _ ≤ _ * (a (x 0) * P x + Q x)
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte, one_mul] at hPa hQ ⊢
    rw [abs_le] at hPa hQ ⊢
    constructor <;> linarith
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, zero_mul, zero_add] at hPa hQ ⊢
    rw [abs_le] at hPa hQ ⊢
    constructor <;> linarith

end PDE.Analysis
