/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Rectangle.MixedPrimitive
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BiotSavartKernel
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Integrals of the planar Biot–Savart kernels over rectangles

With `G(y) = -(1/2) log |y|`, the kernels of the velocity gradient are `K₁ = ∂₁∂₂G =
y₁ y₂ / |y|⁴` (`hessianKernel 0 1`) and `K₂ = ∂₁²G = (y₁² - y₂²) / (2 |y|⁴)` (`hessianKernel 0 0`),
and the kernels of the velocity are `∂ᵢG = π gradientKernel i`. Over a closed rectangle
`Q = [a, b] × [c, d]` avoiding the origin (`a ≤ b`, `c ≤ d`, `0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0`)
their integrals are mixed differences `cornerSum H a b c d = H b d - H a d - H b c + H a c` of
explicit primitives, as in Chen and Hou II, Supplementary material II, Section 5.1, (5.3) and
(5.4):

* `K₁`: `H = G = -(1/4) log (u² + v²)`;
* `K₂`: `H = (1/2) arctan (u / v)`. The primitive enters only through its derivative along the
  two horizontal edges, and with Lean's `u / 0 = 0` it is valid on every rectangle avoiding the
  origin, also when an edge lies on the axis `v = 0` or the rectangle crosses it;
* `∂₁G` and `∂₂G`: `H = -(2u arctan (v/u) + v log (u² + v²))/4` and
  `-(2v arctan (u/v) + u log (u² + v²))/4`. These kernels are locally integrable and the
  primitives continuous, so the formulas hold on every closed rectangle, also on the singular
  boxes around the pole;
* the third derivatives `∂₀K₁ = ∂₁K₂ = y₁ (y₁² - 3y₀²) / |y|⁶` and
  `∂₁K₁ = -∂₀K₂ = y₀ (y₀² - 3y₁²) / |y|⁶`: the rational primitives `-u / (2(u² + v²))` and
  `-v / (2(u² + v²))`.

For the symmetrized kernel `kₛ(x, y) = k(x - y) - k(x - R₀ y) - k(x - R₁ y) + k(x + y)` of Chen
and Hou II, (4.25) (`GreenFunction.symmetrizedKernel`), the integral over `Q` is the
alternating sum of the integrals of `k` over the four rectangles `x - Q`, `x - R₀ Q`, `x - R₁ Q`,
`x + Q`, so for `K₁` and `K₂` it is `symmetrizedCornerSum H x a b c d`, sixteen values of the
primitive.

The sums of logarithms and of arctangents collapse to one logarithm of a rational cross ratio
and, on the closed first quadrant, one arctangent of a rational number; a single arctangent cannot
hold on every rectangle, since `∫_{[1,9] × [-3,3]} K₂ = arctan (4/3) > π/4`.

## Main definitions

* `symmetrizedCornerSum`: the alternating sum of the corner sums of `H` over the four rectangles
  `x - Q`, `x - R₀ Q`, `x - R₁ Q`, `x + Q`.
* `crossRatio`: `R = (b² + d²)(a² + c²) / ((a² + d²)(b² + c²))`.
* `symmetrizedCrossRatio`: `R₁ R₄ / (R₂ R₃)` for the four rectangles of the symmetrization.
* `quadrantArg`: `Z = (b-a)(d-c)(ab-cd) / ((d² + ab)(c² + ab) + (b-a)² cd)`.

## Main results

* `integral_rectangle_hessianKernel_zero_one_eq_cornerSum`,
  `integral_rectangle_hessianKernel_zero_zero_eq_cornerSum`: `∫_Q K₁` and `∫_Q K₂` are the corner
  sums of `-(1/4) log (u² + v²)` and `(1/2) arctan (u / v)`;
  `integral_integral_hessianKernel_zero_one` and `integral_integral_hessianKernel_zero_zero` are
  the same for the iterated integrals.
* `integral_rectangle_gradientKernel_zero_eq_cornerSum`,
  `integral_rectangle_gradientKernel_one_eq_cornerSum`: the corner sums for `∂₁G` and `∂₂G` on
  every closed rectangle.
* `integral_rectangle_partialDeriv_zero_hessianKernel_zero_one`,
  `integral_rectangle_partialDeriv_one_hessianKernel_zero_one`: the rational corner sums for
  `∂₀K₁` and `∂₁K₁`, from `partialDeriv_zero_hessianKernel_zero_one` and its three neighbours.
* `integral_hessianKernel_zero_zero_right`, `integral_hessianKernel_zero_zero_left`: the inner
  integrals of `K₂` along a segment.
* `integral_rectangle_symmetrizedKernel`: `∫_Q kₛ(x, ·)` is the alternating sum over the four
  rectangles; `integral_rectangle_symmetrizedKernel_zero_one` and
  `integral_rectangle_symmetrizedKernel_zero_zero` specialize it to `K₁` and `K₂`.
* `cornerSum_log_eq_neg_log_crossRatio`: `∫_Q K₁ = -(1/4) log R`.
* `symmetrizedCornerSum_log_eq_neg_log_symmetrizedCrossRatio`:
  `∫_Q K₁ₛ(x, ·) = -(1/4) log (R₁ R₄ / (R₂ R₃))`.
* `cornerSum_arctan_eq_arctan_quadrantArg`: `∫_Q K₂ = (1/2) arctan Z` on the closed first
  quadrant.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Section 4.1.5, (4.25),
  and Supplementary material II, Section 5.1, (5.3)-(5.4).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

noncomputable section

open PDE (coordinateLine)
open MeasureTheory Set PDE.Analysis

namespace PotentialTheory.Planar

/-! ### The primitives in coordinates -/

/-- A point `(x, y)` of a closed rectangle `[a, b] × [c, d]` avoiding the origin has `x² + y² ≠ 0`.
-/
private theorem sq_add_sq_ne_zero {a b c d x y : ℝ} (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0)
    (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) : x ^ 2 + y ^ 2 ≠ 0 := by
  intro h
  have hx0 : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy0 : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  subst hx0 hy0
  rcases h0 with h | h | h | h
  · linarith [hx.1]
  · linarith [hx.2]
  · linarith [hy.1]
  · linarith [hy.2]

/-- `∂_x (-(1/4) log (x² + y²)) = -x / (2 (x² + y²))`. -/
private theorem hasDerivAt_log_left {x y : ℝ} (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun x ↦ -Real.log (x ^ 2 + y ^ 2) / 4) (-x / (2 * (x ^ 2 + y ^ 2))) x := by
  have h1 : HasDerivAt (fun x ↦ x ^ 2 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
  convert ((h1.log h).neg).div_const 4 using 1
  field_simp
  ring

/-- `∂_y (-x / (2 (x² + y²))) = x y / (x² + y²)²`. -/
private theorem hasDerivAt_neg_div_right {x y : ℝ} (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun y ↦ -x / (2 * (x ^ 2 + y ^ 2))) (x * y / (x ^ 2 + y ^ 2) ^ 2) y := by
  have h1 : HasDerivAt (fun y ↦ 2 * (x ^ 2 + y ^ 2)) (2 * (2 * y)) y := by
    simpa using ((hasDerivAt_pow 2 y).const_add (x ^ 2)).const_mul 2
  have h2 : (2 : ℝ) * (x ^ 2 + y ^ 2) ≠ 0 := mul_ne_zero two_ne_zero h
  convert (hasDerivAt_const y (-x)).div h1 h2 using 1
  field_simp
  ring

/-- `∂_x (-y / (2 (x² + y²))) = x y / (x² + y²)²`. -/
private theorem hasDerivAt_neg_div_left {x y : ℝ} (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun x ↦ -y / (2 * (x ^ 2 + y ^ 2))) (x * y / (x ^ 2 + y ^ 2) ^ 2) x := by
  have h' : y ^ 2 + x ^ 2 ≠ 0 := by rwa [add_comm]
  have := hasDerivAt_neg_div_right (x := y) (y := x) h'
  simp only [add_comm (y ^ 2), mul_comm y x] at this
  exact this

/-- `∂_y (y / (2 (x² + y²))) = (x² - y²) / (2 (x² + y²)²)`. -/
private theorem hasDerivAt_div_right {x y : ℝ} (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun y ↦ y / (2 * (x ^ 2 + y ^ 2))) ((x ^ 2 - y ^ 2) / (2 * (x ^ 2 + y ^ 2) ^ 2))
      y := by
  have h1 : HasDerivAt (fun y ↦ 2 * (x ^ 2 + y ^ 2)) (2 * (2 * y)) y := by
    simpa using ((hasDerivAt_pow 2 y).const_add (x ^ 2)).const_mul 2
  have h2 : (2 : ℝ) * (x ^ 2 + y ^ 2) ≠ 0 := mul_ne_zero two_ne_zero h
  convert (hasDerivAt_id' y).div h1 h2 using 1
  field_simp
  ring

/-- `∂_x ((1/2) arctan (x / y)) = y / (2 (x² + y²))`, also for `y = 0` where both sides vanish. -/
theorem hasDerivAt_arctan_div_left (x y : ℝ) :
    HasDerivAt (fun x ↦ Real.arctan (x / y) / 2) (y / (2 * (x ^ 2 + y ^ 2))) x := by
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    simpa using hasDerivAt_const x (0 : ℝ)
  · have h := ((Real.hasDerivAt_arctan (x / y)).comp x ((hasDerivAt_id' x).div_const y)).div_const 2
    have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
    refine h.congr_deriv ?_
    rw [div_pow, show 1 + x ^ 2 / y ^ 2 = (x ^ 2 + y ^ 2) / y ^ 2 by
      rw [add_div, div_self hy2, add_comm]]
    field_simp

/-- `∂_x (-x / (2 (x² + y²))) = (x² - y²) / (2 (x² + y²)²)`. -/
private theorem hasDerivAt_neg_div_self_left {x y : ℝ} (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun x ↦ -x / (2 * (x ^ 2 + y ^ 2))) ((x ^ 2 - y ^ 2) / (2 * (x ^ 2 + y ^ 2) ^ 2))
      x := by
  have h1 : HasDerivAt (fun x ↦ 2 * (x ^ 2 + y ^ 2)) (2 * (2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).add_const (y ^ 2)).const_mul 2
  have h2 : (2 : ℝ) * (x ^ 2 + y ^ 2) ≠ 0 := mul_ne_zero two_ne_zero h
  convert (hasDerivAt_neg' x).div h1 h2 using 1
  field_simp
  ring

/-- `∂_y (x² + y²)² = 2 (x² + y²) · 2y`. -/
private theorem hasDerivAt_sq_add_sq_sq (x y : ℝ) :
    HasDerivAt (fun y ↦ (x ^ 2 + y ^ 2) ^ 2) (2 * (x ^ 2 + y ^ 2) * (2 * y)) y := by
  have h := (hasDerivAt_pow 2 (x ^ 2 + y ^ 2)).comp y ((hasDerivAt_pow 2 y).const_add (x ^ 2))
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

/-- `∂_y (x y / (x² + y²)²) = x (x² - 3y²) / (x² + y²)³`. -/
private theorem hasDerivAt_kernelOne_right {x y : ℝ} (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun y ↦ x * y / (x ^ 2 + y ^ 2) ^ 2)
      (x * (x ^ 2 - 3 * y ^ 2) / (x ^ 2 + y ^ 2) ^ 3) y := by
  have h1 : HasDerivAt (fun y ↦ x * y) x y := by simpa using (hasDerivAt_id' y).const_mul x
  convert h1.div (hasDerivAt_sq_add_sq_sq x y) (pow_ne_zero 2 h) using 1
  field_simp
  ring

/-- `∂_y ((x² - y²) / (2 (x² + y²)²)) = y (y² - 3x²) / (x² + y²)³`. -/
private theorem hasDerivAt_kernelTwo_right {x y : ℝ} (h : x ^ 2 + y ^ 2 ≠ 0) :
    HasDerivAt (fun y ↦ (x ^ 2 - y ^ 2) / (2 * (x ^ 2 + y ^ 2) ^ 2))
      (y * (y ^ 2 - 3 * x ^ 2) / (x ^ 2 + y ^ 2) ^ 3) y := by
  have h1 : HasDerivAt (fun y ↦ x ^ 2 - y ^ 2) (-(2 * y)) y := by
    simpa using (hasDerivAt_pow 2 y).const_sub (x ^ 2)
  have h3 : (2 : ℝ) * (x ^ 2 + y ^ 2) ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 h)
  convert h1.div ((hasDerivAt_sq_add_sq_sq x y).const_mul 2) h3 using 1
  field_simp
  ring

/-! ### Rectangle integrals in coordinates -/

/-- A function continuous on `[a, b] × [c, d]` is integrable on `[c, d]` in its second variable, for
every `x ∈ [a, b]`. -/
private theorem intervalIntegrable_right {a b c d : ℝ} {f : ℝ → ℝ → ℝ} (hcd : c ≤ d)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d)) {x : ℝ}
    (hx : x ∈ Icc a b) : IntervalIntegrable (f x) volume c d := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hcd]
  exact hf.comp (continuous_const.prodMk continuous_id).continuousOn fun y hy ↦ ⟨hx, hy⟩

/-- A function continuous on `[a, b] × [c, d]` is integrable on `[a, b]` in its first variable, for
every `y ∈ [c, d]`. -/
private theorem intervalIntegrable_left {a b c d : ℝ} {f : ℝ → ℝ → ℝ} (hab : a ≤ b)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d)) {y : ℝ}
    (hy : y ∈ Icc c d) : IntervalIntegrable (fun x ↦ f x y) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact hf.comp (continuous_id.prodMk continuous_const).continuousOn fun x hx ↦ ⟨hx, hy⟩

/-- A function of two variables that is continuous at every point other than the origin is
continuous on every closed rectangle avoiding the origin. -/
private theorem continuousOn_of_avoids {a b c d : ℝ} {f : ℝ → ℝ → ℝ}
    (hf : ∀ x y, x ^ 2 + y ^ 2 ≠ 0 → ContinuousAt (Function.uncurry f) (x, y))
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ContinuousOn (Function.uncurry f) (Icc a b ×ˢ Icc c d) := fun p hp ↦
  (hf p.1 p.2 (sq_add_sq_ne_zero h0 hp.1 hp.2)).continuousWithinAt

/-- The corner-sum formula on a rectangle avoiding the origin, inner integral in `y`. -/
private theorem integral_integral_eq_cornerSum_of_avoids {k k₁ H : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0)
    (hk : ∀ x y, x ^ 2 + y ^ 2 ≠ 0 → HasDerivAt (k₁ x) (k x y) y)
    (hH : ∀ x y, x ^ 2 + y ^ 2 ≠ 0 → HasDerivAt (fun x ↦ H x y) (k₁ x y) x)
    (hkc : ∀ x y, x ^ 2 + y ^ 2 ≠ 0 → ContinuousAt (Function.uncurry k) (x, y))
    (hk₁c : ∀ x y, x ^ 2 + y ^ 2 ≠ 0 → ContinuousAt (Function.uncurry k₁) (x, y)) :
    ∫ x in a..b, ∫ y in c..d, k x y = cornerSum H a b c d := by
  have hk' := continuousOn_of_avoids hkc h0
  have hk₁' := continuousOn_of_avoids hk₁c h0
  refine integral_integral_eq_cornerSum (k₁ := k₁) (fun x hx y hy ↦ ?_) (fun x hx ↦ ?_)
    (fun x hx ↦ ?_) (fun x hx ↦ ?_) ?_ ?_
  · rw [uIcc_of_le hab] at hx; rw [uIcc_of_le hcd] at hy
    exact hk x y (sq_add_sq_ne_zero h0 hx hy)
  · rw [uIcc_of_le hab] at hx; exact intervalIntegrable_right hcd hk' hx
  · rw [uIcc_of_le hab] at hx
    exact hH x c (sq_add_sq_ne_zero h0 hx ⟨le_rfl, hcd⟩)
  · rw [uIcc_of_le hab] at hx
    exact hH x d (sq_add_sq_ne_zero h0 hx ⟨hcd, le_rfl⟩)
  · exact intervalIntegrable_left hab hk₁' ⟨le_rfl, hcd⟩
  · exact intervalIntegrable_left hab hk₁' ⟨hcd, le_rfl⟩

/-- A quotient `f / g` of continuous functions on `ℝ × ℝ` is continuous at every point where `g ≠
0`. -/
private theorem continuousAt_div {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {p : ℝ × ℝ} (h : g p ≠ 0) : ContinuousAt (fun p ↦ f p / g p) p :=
  hf.continuousAt.div hg.continuousAt h

/-- `2 (x² + y²)ⁿ ≠ 0` whenever `x² + y² ≠ 0`. -/
private theorem two_mul_ne {x y : ℝ} (h : x ^ 2 + y ^ 2 ≠ 0) (n : ℕ) :
    (2 : ℝ) * (x ^ 2 + y ^ 2) ^ n ≠ 0 :=
  mul_ne_zero two_ne_zero (pow_ne_zero n h)

/-- On a closed rectangle avoiding the origin, `∫_a^b ∫_c^d x y / (x² + y²)² dy dx` is the corner
sum of `-(1/4) log (u² + v²)`. -/
private theorem integral_integral_kernelOne {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ x in a..b, ∫ y in c..d, x * y / (x ^ 2 + y ^ 2) ^ 2 =
      cornerSum (fun u v ↦ -Real.log (u ^ 2 + v ^ 2) / 4) a b c d :=
  integral_integral_eq_cornerSum_of_avoids (k₁ := fun x y ↦ -x / (2 * (x ^ 2 + y ^ 2))) hab hcd
    h0 (fun _ _ h ↦ hasDerivAt_neg_div_right h) (fun _ _ h ↦ hasDerivAt_log_left h)
    (fun _ _ h ↦ continuousAt_div (f := fun p ↦ p.1 * p.2)
      (g := fun p ↦ (p.1 ^ 2 + p.2 ^ 2) ^ 2) (by fun_prop) (by fun_prop) (pow_ne_zero 2 h))
    (fun _ _ h ↦ continuousAt_div (f := fun p ↦ -p.1)
      (g := fun p ↦ 2 * (p.1 ^ 2 + p.2 ^ 2)) (by fun_prop) (by fun_prop)
      (by simpa using two_mul_ne h 1))

/-- On a closed rectangle avoiding the origin, `∫_a^b ∫_c^d (x² - y²) / (2 (x² + y²)²) dy dx` is the
corner sum of `(1/2) arctan (u / v)`. -/
private theorem integral_integral_kernelTwo {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ x in a..b, ∫ y in c..d, (x ^ 2 - y ^ 2) / (2 * (x ^ 2 + y ^ 2) ^ 2) =
      cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d :=
  integral_integral_eq_cornerSum_of_avoids (k₁ := fun x y ↦ y / (2 * (x ^ 2 + y ^ 2))) hab hcd
    h0 (fun _ _ h ↦ hasDerivAt_div_right h) (fun x y _ ↦ hasDerivAt_arctan_div_left x y)
    (fun _ _ h ↦ continuousAt_div (f := fun p ↦ p.1 ^ 2 - p.2 ^ 2)
      (g := fun p ↦ 2 * (p.1 ^ 2 + p.2 ^ 2) ^ 2) (by fun_prop) (by fun_prop) (two_mul_ne h 2))
    (fun _ _ h ↦ continuousAt_div (f := fun p ↦ p.2)
      (g := fun p ↦ 2 * (p.1 ^ 2 + p.2 ^ 2)) (by fun_prop) (by fun_prop)
      (by simpa using two_mul_ne h 1))

/-- On a closed rectangle avoiding the origin, `∫_a^b ∫_c^d y (y² - 3x²) / (x² + y²)³ dy dx` is the
corner sum of `-u / (2 (u² + v²))`. -/
private theorem integral_integral_thirdOne {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ x in a..b, ∫ y in c..d, y * (y ^ 2 - 3 * x ^ 2) / (x ^ 2 + y ^ 2) ^ 3 =
      cornerSum (fun u v ↦ -u / (2 * (u ^ 2 + v ^ 2))) a b c d :=
  integral_integral_eq_cornerSum_of_avoids
    (k₁ := fun x y ↦ (x ^ 2 - y ^ 2) / (2 * (x ^ 2 + y ^ 2) ^ 2)) hab hcd h0
    (fun _ _ h ↦ hasDerivAt_kernelTwo_right h) (fun _ _ h ↦ hasDerivAt_neg_div_self_left h)
    (fun _ _ h ↦ continuousAt_div (f := fun p ↦ p.2 * (p.2 ^ 2 - 3 * p.1 ^ 2))
      (g := fun p ↦ (p.1 ^ 2 + p.2 ^ 2) ^ 3) (by fun_prop) (by fun_prop) (pow_ne_zero 3 h))
    (fun _ _ h ↦ continuousAt_div (f := fun p ↦ p.1 ^ 2 - p.2 ^ 2)
      (g := fun p ↦ 2 * (p.1 ^ 2 + p.2 ^ 2) ^ 2) (by fun_prop) (by fun_prop) (two_mul_ne h 2))

/-- On a closed rectangle avoiding the origin, `∫_a^b ∫_c^d x (x² - 3y²) / (x² + y²)³ dy dx` is the
corner sum of `-v / (2 (u² + v²))`. -/
private theorem integral_integral_thirdTwo {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ x in a..b, ∫ y in c..d, x * (x ^ 2 - 3 * y ^ 2) / (x ^ 2 + y ^ 2) ^ 3 =
      cornerSum (fun u v ↦ -v / (2 * (u ^ 2 + v ^ 2))) a b c d :=
  integral_integral_eq_cornerSum_of_avoids (k₁ := fun x y ↦ x * y / (x ^ 2 + y ^ 2) ^ 2) hab hcd
    h0 (fun _ _ h ↦ hasDerivAt_kernelOne_right h) (fun _ _ h ↦ hasDerivAt_neg_div_left h)
    (fun _ _ h ↦ continuousAt_div (f := fun p ↦ p.1 * (p.1 ^ 2 - 3 * p.2 ^ 2))
      (g := fun p ↦ (p.1 ^ 2 + p.2 ^ 2) ^ 3) (by fun_prop) (by fun_prop) (pow_ne_zero 3 h))
    (fun _ _ h ↦ continuousAt_div (f := fun p ↦ p.1 * p.2)
      (g := fun p ↦ (p.1 ^ 2 + p.2 ^ 2) ^ 2) (by fun_prop) (by fun_prop) (pow_ne_zero 2 h))

/-! ### Rectangles of the plane -/

/-- `π gradientKernel 0 (p, q) = -p / (2 (p² + q²))`: the kernel `∂₁G` in coordinates. -/
private theorem gradientKernel_zero_toLp (p q : ℝ) :
    Real.pi * gradientKernel 0 !₂[p, q] = -p / (2 * (p ^ 2 + q ^ 2)) := by
  rw [gradientKernel_eq_div, norm_sq_vec]
  have := Real.pi_pos.ne'
  simp only [Matrix.cons_val_zero]
  field_simp

/-- Every point of a closed rectangle `[a, b] × [c, d]` avoiding the origin is nonzero. -/
theorem ne_zero_of_mem_coordinateRectangle {a b c d : ℝ} (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0)
    {z : ℝ^2} (hz : z ∈ coordinateRectangle a b c d) : z ≠ 0 := by
  rintro rfl
  have h := sq_add_sq_ne_zero h0 hz.1 hz.2
  simp at h

/-- The Hessian kernel `kᵢⱼ` is continuous on every closed rectangle avoiding the origin. -/
theorem continuousOn_hessianKernel (i j : Fin 2) {a b c d : ℝ}
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ContinuousOn (hessianKernel i j) (coordinateRectangle a b c d) := fun _ hz ↦
  ((contDiffAt_hessianKernel i j (ne_zero_of_mem_coordinateRectangle h0 hz) (n := 0)).continuousAt
    ).continuousWithinAt

/-- The gradient kernel `gradientKernel j` is continuous on every closed rectangle avoiding the
origin. -/
theorem continuousOn_gradientKernel (j : Fin 2) {a b c d : ℝ}
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ContinuousOn (gradientKernel j) (coordinateRectangle a b c d) := fun _ hz ↦
  ((contDiffAt_gradientKernel j (ne_zero_of_mem_coordinateRectangle h0 hz) (n := 0)).continuousAt
    ).continuousWithinAt

/-- **`K₁` over a rectangle, in coordinates**: for a closed rectangle `[a, b] × [c, d]` avoiding
the origin, `∫_a^b ∫_c^d K₁ = Σ ± G` at the corners, `G(u, v) = -(1/4) log (u² + v²)`. -/
theorem integral_integral_hessianKernel_zero_one {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ x in a..b, ∫ y in c..d, hessianKernel 0 1 !₂[x, y] =
      cornerSum (fun u v ↦ -Real.log (u ^ 2 + v ^ 2) / 4) a b c d := by
  simp only [hessianKernel_zero_one_toLp]
  exact integral_integral_kernelOne hab hcd h0

/-- **`K₂` over a rectangle, in coordinates**: for a closed rectangle `[a, b] × [c, d]` avoiding
the origin, `∫_a^b ∫_c^d K₂ = Σ ± (1/2) arctan (u / v)` at the corners. -/
theorem integral_integral_hessianKernel_zero_zero {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ x in a..b, ∫ y in c..d, hessianKernel 0 0 !₂[x, y] =
      cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d := by
  simp only [hessianKernel_zero_zero_toLp]
  exact integral_integral_kernelTwo hab hcd h0

/-- The inner integral of `K₂` in the second coordinate:
`∫_c^d K₂(u, v) dv = d / (2 (u² + d²)) - c / (2 (u² + c²))` when the segment avoids the origin. -/
theorem integral_hessianKernel_zero_zero_right {u c d : ℝ}
    (h : ∀ v ∈ uIcc c d, u ^ 2 + v ^ 2 ≠ 0) :
    ∫ v in c..d, hessianKernel 0 0 !₂[u, v] =
      d / (2 * (u ^ 2 + d ^ 2)) - c / (2 * (u ^ 2 + c ^ 2)) := by
  simp only [hessianKernel_zero_zero_toLp]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v hv ↦ hasDerivAt_div_right (h v hv))
    (ContinuousOn.intervalIntegrable fun v hv ↦ ?_)
  exact (continuousAt_div (f := fun p : ℝ × ℝ ↦ p.1 ^ 2 - p.2 ^ 2)
    (g := fun p ↦ 2 * (p.1 ^ 2 + p.2 ^ 2) ^ 2) (by fun_prop) (by fun_prop) (two_mul_ne (h v hv) 2)
    |>.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt

/-- The inner integral of `K₂` in the first coordinate:
`∫_a^b K₂(u, v) du = -b / (2 (b² + v²)) + a / (2 (a² + v²))` when the segment avoids the origin. -/
theorem integral_hessianKernel_zero_zero_left {v a b : ℝ}
    (h : ∀ u ∈ uIcc a b, u ^ 2 + v ^ 2 ≠ 0) :
    ∫ u in a..b, hessianKernel 0 0 !₂[u, v] =
      -b / (2 * (b ^ 2 + v ^ 2)) + a / (2 * (a ^ 2 + v ^ 2)) := by
  simp only [hessianKernel_zero_zero_toLp]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu ↦ hasDerivAt_neg_div_self_left (h u hu))
    (ContinuousOn.intervalIntegrable fun u hu ↦ ?_)]
  · ring
  exact (continuousAt_div (f := fun p : ℝ × ℝ ↦ p.1 ^ 2 - p.2 ^ 2)
    (g := fun p ↦ 2 * (p.1 ^ 2 + p.2 ^ 2) ^ 2) (by fun_prop) (by fun_prop) (two_mul_ne (h u hu) 2)
    |>.comp (continuous_id.prodMk continuous_const).continuousAt).continuousWithinAt

/-- **`K₁` over a rectangle**: `∫_Q K₁ = Σ ± G` at the corners of `Q`, with
`G(u, v) = -(1/4) log (u² + v²)`, for every closed rectangle `Q` avoiding the origin. -/
theorem integral_rectangle_hessianKernel_zero_one_eq_cornerSum {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ y in coordinateRectangle a b c d, hessianKernel 0 1 y =
      cornerSum (fun u v ↦ -Real.log (u ^ 2 + v ^ 2) / 4) a b c d := by
  rw [setIntegral_coordinateRectangle hab hcd (continuousOn_hessianKernel 0 1 h0)]
  exact integral_integral_hessianKernel_zero_one hab hcd h0

/-- **`K₂` over a rectangle**: `∫_Q K₂ = Σ ± (1/2) arctan (u / v)` at the corners `(u, v)` of `Q`,
for every closed rectangle `Q` avoiding the origin, with `arctan (u / 0) = 0` at corners on the
axis `v = 0`. -/
theorem integral_rectangle_hessianKernel_zero_zero_eq_cornerSum {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ y in coordinateRectangle a b c d, hessianKernel 0 0 y =
      cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d := by
  rw [setIntegral_coordinateRectangle hab hcd (continuousOn_hessianKernel 0 0 h0)]
  exact integral_integral_hessianKernel_zero_zero hab hcd h0

/-- The inner integral of `∂₁G` along a vertical segment, for every abscissa (zero on `p = 0`). -/
private theorem integral_gradientOne_inner (p c d : ℝ) :
    ∫ q in c..d, -p / (2 * (p ^ 2 + q ^ 2)) =
      -Real.arctan (d / p) / 2 - -Real.arctan (c / p) / 2 := by
  rcases eq_or_ne p 0 with hp | hp
  · subst hp; simp
  · have hd : ∀ q ∈ uIcc c d, HasDerivAt (fun q ↦ -Real.arctan (q / p) / 2)
        (-p / (2 * (p ^ 2 + q ^ 2))) q := by
      intro q _
      have h := (((Real.hasDerivAt_arctan (q / p)).comp q
        ((hasDerivAt_id' q).div_const p)).neg).div_const 2
      refine h.congr_deriv ?_
      have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp
      rw [div_pow, show 1 + q ^ 2 / p ^ 2 = (p ^ 2 + q ^ 2) / p ^ 2 by
        rw [add_div, div_self hp2, add_comm]]
      have : p ^ 2 + q ^ 2 ≠ 0 := by positivity
      field_simp
    have hp2 : 0 < p ^ 2 := lt_of_le_of_ne (sq_nonneg p) (Ne.symm (pow_ne_zero 2 hp))
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd (ContinuousOn.intervalIntegrable
      fun q _ ↦ (continuousAt_const.div (continuousAt_const.mul (continuousAt_const.add
        (continuousAt_id.pow 2))) (mul_ne_zero two_ne_zero
          (ne_of_gt (add_pos_of_pos_of_nonneg hp2 (sq_nonneg q))))).continuousWithinAt)

/-- `|p arctan (y / p)| ≤ (π / 2) |p|`. -/
private theorem abs_mul_arctan_le (p y : ℝ) : |p * Real.arctan (y / p)| ≤ Real.pi / 2 * |p| := by
  rw [abs_mul, mul_comm]
  gcongr
  exact (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _, Real.arctan_lt_pi_div_two _⟩).le

/-- `p ↦ p arctan (y / p)` is continuous, with the value `0` at `p = 0`. -/
private theorem continuous_mul_arctan (y : ℝ) :
    Continuous fun p : ℝ ↦ p * Real.arctan (y / p) := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases eq_or_ne p 0 with hp | hp
  · subst hp
    have h : Filter.Tendsto (fun p : ℝ ↦ p * Real.arctan (y / p)) (nhds 0) (nhds 0) := by
      refine squeeze_zero_norm (fun p ↦ ?_) (by simpa using
        ((continuous_abs.tendsto (0 : ℝ)).const_mul (Real.pi / 2)))
      simpa [Real.norm_eq_abs] using abs_mul_arctan_le p y
    simpa [ContinuousAt] using h
  · exact continuousAt_id.mul (Real.continuous_arctan.continuousAt.comp
      (continuousAt_const.div continuousAt_id hp))

/-- `p ↦ -(1/2) arctan (y / p)` is integrable on every interval, also across `p = 0`. -/
private theorem intervalIntegrable_arctan_div (y a b : ℝ) :
    IntervalIntegrable (fun p ↦ -Real.arctan (y / p) / 2) volume a b := by
  refine intervalIntegrable_iff.mpr (Measure.integrableOn_of_bounded (M := Real.pi)
    (by simp) ?_ (Filter.Eventually.of_forall fun p ↦ ?_))
  · exact ((Real.continuous_arctan.measurable.comp
      (measurable_const.div measurable_id)).neg.div_const 2).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_div, abs_neg, abs_two]
    have := (abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan (y / p),
      Real.arctan_lt_pi_div_two (y / p)⟩).le
    linarith [Real.pi_pos]

/-- The outer integral `∫_a^b -(1/2) arctan (y / p) dp`, through `p = 0`: the primitive
`-(2p arctan (y/p) + y log (p² + y²))/4` is continuous and differentiable off `p = 0`. -/
private theorem integral_gradientOne_outer (y a b : ℝ) (hab : a ≤ b) :
    ∫ p in a..b, -Real.arctan (y / p) / 2 =
      -(2 * (b * Real.arctan (y / b)) + y * Real.log (b ^ 2 + y ^ 2)) / 4 -
        -(2 * (a * Real.arctan (y / a)) + y * Real.log (a ^ 2 + y ^ 2)) / 4 := by
  rcases eq_or_ne y 0 with hy | hy
  · subst hy; simp
  have hy2 : 0 < y ^ 2 := lt_of_le_of_ne (sq_nonneg y) (Ne.symm (pow_ne_zero 2 hy))
  have hc : ContinuousOn
      (fun p ↦ -(2 * (p * Real.arctan (y / p)) + y * Real.log (p ^ 2 + y ^ 2)) / 4) (Icc a b) :=
    (((continuous_mul_arctan y).const_smul (2 : ℝ)).add (continuous_const.mul
      ((continuous_pow 2 |>.add continuous_const).log fun p ↦
        ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg p) hy2)))).neg.div_const 4
      |>.continuousOn
  have hd : ∀ p ∈ Ioo a b \ {0}, HasDerivAt
      (fun p ↦ -(2 * (p * Real.arctan (y / p)) + y * Real.log (p ^ 2 + y ^ 2)) / 4)
      (-Real.arctan (y / p) / 2) p := by
    intro p hp
    have hp0 : p ≠ 0 := hp.2
    have hpy : p ^ 2 + y ^ 2 ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg p) hy2)
    have h1 : HasDerivAt (fun p ↦ Real.arctan (y / p)) (-(y / (p ^ 2 + y ^ 2))) p := by
      have h := (Real.hasDerivAt_arctan (y / p)).comp p ((hasDerivAt_inv hp0).const_mul y)
      have hp2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp0
      convert h using 1
      · funext p; simp [div_eq_mul_inv]
      · field_simp
    have h2 : HasDerivAt (fun p ↦ p ^ 2 + y ^ 2) (2 * p) p := by
      simpa using (hasDerivAt_pow 2 p).add_const (y ^ 2)
    have h := ((((hasDerivAt_id' p).mul h1).const_mul 2).add
      ((h2.log hpy).const_mul y)).neg.div_const 4
    refine h.congr_deriv ?_
    field_simp
    ring
  exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le _ _ hab
    (Set.countable_singleton 0) hc hd (intervalIntegrable_arctan_div y a b)

/-- **`∂₁G` over a rectangle**: for every closed rectangle `Q`, also one containing the pole,
`π ∫_Q gradientKernel 0 = ∫_Q ∂₁G` is the corner sum of
`-(2u arctan (v/u) + v log (u² + v²))/4` (Chen–Hou II, Supp. (5.4), whose primitive has
the extra term `v/2`). The kernel is locally integrable; its primitive is continuous. -/
theorem integral_rectangle_gradientKernel_zero_eq_cornerSum {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) :
    Real.pi * ∫ y in coordinateRectangle a b c d, gradientKernel 0 y =
      cornerSum (fun u v ↦ -(2 * (u * Real.arctan (v / u)) + v * Real.log (u ^ 2 + v ^ 2)) / 4)
        a b c d := by
  have hint : IntegrableOn (gradientKernel 0) (coordinateRectangle a b c d) :=
    (locallyIntegrable_gradientKernel 0).integrableOn_isCompact
      (isCompact_coordinateRectangle a b c d)
  rw [← integral_const_mul, setIntegral_coordinateRectangle_of_integrableOn hab hcd
    (hint.const_mul Real.pi)]
  simp only [gradientKernel_zero_toLp, integral_gradientOne_inner]
  rw [intervalIntegral.integral_sub (intervalIntegrable_arctan_div d a b)
    (intervalIntegrable_arctan_div c a b), integral_gradientOne_outer d a b hab,
    integral_gradientOne_outer c a b hab]
  unfold cornerSum
  ring

/-- **`∂₂G` over a rectangle**: for every closed rectangle `Q`, also one containing the pole,
`π ∫_Q gradientKernel 1 = ∫_Q ∂₂G` is the corner sum of
`-(2v arctan (u/v) + u log (u² + v²))/4` (Chen–Hou II, Supp. (5.4), whose primitive has
the extra term `u/2`). -/
theorem integral_rectangle_gradientKernel_one_eq_cornerSum {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) :
    Real.pi * ∫ y in coordinateRectangle a b c d, gradientKernel 1 y =
      cornerSum (fun u v ↦ -(2 * (v * Real.arctan (u / v)) + u * Real.log (u ^ 2 + v ^ 2)) / 4)
        a b c d := by
  rw [← setIntegral_coordinateRectangle_swap]
  have hswap : ∀ y : ℝ^2, gradientKernel 1
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) y) =
        gradientKernel 0 y := by
    intro y
    rw [gradientKernel_eq_div, gradientKernel_eq_div, LinearIsometryEquiv.norm_map]
    simp [LinearIsometryEquiv.piLpCongrLeft_apply]
  simp only [hswap]
  rw [integral_rectangle_gradientKernel_zero_eq_cornerSum hcd hab, ← cornerSum_swap]
  congr 1
  funext u v
  rw [add_comm (v ^ 2)]

/-- For continuous `f`, the quotient `f(y) / |y|ⁿ` is continuous on every closed rectangle avoiding
the origin. -/
private theorem continuousOn_third {a b c d : ℝ} (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0)
    {f : ℝ^2 → ℝ} (hf : Continuous f) (n : ℕ) :
    ContinuousOn (fun y : ℝ^2 ↦ f y / ‖y‖ ^ n) (coordinateRectangle a b c d) :=
  fun _ hz ↦ (hf.continuousAt.div (by fun_prop) (pow_ne_zero n
    (norm_ne_zero_iff.mpr (ne_zero_of_mem_coordinateRectangle h0 hz)))).continuousWithinAt

/-- `|(p, q)|⁶ = (p² + q²)³`. -/
private theorem norm_toLp_pow_six (p q : ℝ) : ‖(!₂[p, q] : ℝ^2)‖ ^ 6 = (p ^ 2 + q ^ 2) ^ 3 := by
  rw [show ‖(!₂[p, q] : ℝ^2)‖ ^ 6 = (‖(!₂[p, q] : ℝ^2)‖ ^ 2) ^ 3 by ring, norm_sq_vec]

/-- `∂₀K₁(p, q) = q (q² - 3p²) / (p² + q²)³` off the origin. -/
theorem hasDerivAt_hessianKernel_zero_one_left {p q : ℝ} (h : p ^ 2 + q ^ 2 ≠ 0) :
    HasDerivAt (fun t ↦ hessianKernel 0 1 !₂[t, q]) (q * (q ^ 2 - 3 * p ^ 2) / (p ^ 2 + q ^ 2) ^ 3)
      p := by
  have h' : q ^ 2 + p ^ 2 ≠ 0 := by rwa [add_comm]
  have := hasDerivAt_kernelOne_right (x := q) (y := p) h'
  simp only [hessianKernel_zero_one_toLp]
  convert this using 1
  · funext t; ring
  · rw [add_comm (q ^ 2)]

/-- `∂₁K₁(p, q) = p (p² - 3q²) / (p² + q²)³` off the origin. -/
theorem hasDerivAt_hessianKernel_zero_one_right {p q : ℝ} (h : p ^ 2 + q ^ 2 ≠ 0) :
    HasDerivAt (fun t ↦ hessianKernel 0 1 !₂[p, t]) (p * (p ^ 2 - 3 * q ^ 2) / (p ^ 2 + q ^ 2) ^ 3)
      q := by
  simp only [hessianKernel_zero_one_toLp]
  exact hasDerivAt_kernelOne_right h

/-- `∂₁K₂(p, q) = q (q² - 3p²) / (p² + q²)³ = ∂₀K₁(p, q)` off the origin. -/
theorem hasDerivAt_hessianKernel_zero_zero_right {p q : ℝ} (h : p ^ 2 + q ^ 2 ≠ 0) :
    HasDerivAt (fun t ↦ hessianKernel 0 0 !₂[p, t]) (q * (q ^ 2 - 3 * p ^ 2) / (p ^ 2 + q ^ 2) ^ 3)
      q := by
  simp only [hessianKernel_zero_zero_toLp]
  exact hasDerivAt_kernelTwo_right h

/-- `∂₀K₂(p, q) = -p (p² - 3q²) / (p² + q²)³ = -∂₁K₁(p, q)` off the origin. -/
theorem hasDerivAt_hessianKernel_zero_zero_left {p q : ℝ} (h : p ^ 2 + q ^ 2 ≠ 0) :
    HasDerivAt (fun t ↦ hessianKernel 0 0 !₂[t, q])
      (-(p * (p ^ 2 - 3 * q ^ 2) / (p ^ 2 + q ^ 2) ^ 3)) p := by
  have h' : q ^ 2 + p ^ 2 ≠ 0 := by rwa [add_comm]
  have := hasDerivAt_kernelTwo_right (x := q) (y := p) h'
  simp only [hessianKernel_zero_zero_toLp]
  refine (this.neg.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
  · rw [add_comm (q ^ 2)]
  · simp only [Pi.neg_apply]; ring

/-- **`∂₀K₁ = ∂₁K₂` over a rectangle**: the integrand `y₁ (y₁² - 3y₀²) / |y|⁶` is
`∂₀K₁ = ∂₁K₂ = ∂₀²∂₁G` off the origin (`hasDerivAt_hessianKernel_zero_one_left`,
`hasDerivAt_hessianKernel_zero_zero_right`); its integral over a closed rectangle avoiding the
origin is the corner sum of `-u / (2 (u² + v²))`. -/
private theorem integral_rectangle_deriv_zero_hessianKernel_zero_one {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ y in coordinateRectangle a b c d, y 1 * (y 1 ^ 2 - 3 * y 0 ^ 2) / ‖y‖ ^ 6 =
      cornerSum (fun u v ↦ -u / (2 * (u ^ 2 + v ^ 2))) a b c d := by
  rw [setIntegral_coordinateRectangle hab hcd
    (continuousOn_third h0 (f := fun y ↦ y 1 * (y 1 ^ 2 - 3 * y 0 ^ 2)) (by fun_prop) 6)]
  simp only [norm_toLp_pow_six, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  exact integral_integral_thirdOne hab hcd h0

/-- **`∂₁K₁ = -∂₀K₂` over a rectangle**: the integrand `y₀ (y₀² - 3y₁²) / |y|⁶` is
`∂₁K₁ = -∂₀K₂ = -∂₀³G` off the origin (`hasDerivAt_hessianKernel_zero_one_right`,
`hasDerivAt_hessianKernel_zero_zero_left`); its integral over a closed rectangle avoiding the
origin is the corner sum of `-v / (2 (u² + v²))`. -/
private theorem integral_rectangle_deriv_one_hessianKernel_zero_one {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ y in coordinateRectangle a b c d, y 0 * (y 0 ^ 2 - 3 * y 1 ^ 2) / ‖y‖ ^ 6 =
      cornerSum (fun u v ↦ -v / (2 * (u ^ 2 + v ^ 2))) a b c d := by
  rw [setIntegral_coordinateRectangle hab hcd
    (continuousOn_third h0 (f := fun y ↦ y 0 * (y 0 ^ 2 - 3 * y 1 ^ 2)) (by fun_prop) 6)]
  simp only [norm_toLp_pow_six, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  exact integral_integral_thirdTwo hab hcd h0

/-- `z₀² + z₁² ≠ 0` for `z ≠ 0`. -/
private theorem norm_sq_ne_zero {z : ℝ^2} (hz : z ≠ 0) : z 0 ^ 2 + z 1 ^ 2 ≠ 0 := by
  rw [← EuclideanSpace.norm_sq_fin_two]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)

/-- `|z|⁶ = (z₀² + z₁²)³`. -/
private theorem norm_pow_six_eq (z : ℝ^2) : ‖z‖ ^ 6 = (z 0 ^ 2 + z 1 ^ 2) ^ 3 := by
  rw [show ‖z‖ ^ 6 = (‖z‖ ^ 2) ^ 3 by ring, EuclideanSpace.norm_sq_fin_two]

/-- Along the coordinate line of index `0` through `z`, the function `k` is `t ↦ k(t, z₁)`. -/
private theorem comp_coordinateLine_zero (k : ℝ^2 → ℝ) (z : ℝ^2) :
    k ∘ coordinateLine 0 z = fun t ↦ k !₂[t, z 1] := by
  funext t; simp only [Function.comp_apply]; congr 1; ext i; fin_cases i <;> simp [coordinateLine]

/-- Along the coordinate line of index `1` through `z`, the function `k` is `t ↦ k(z₀, t)`. -/
private theorem comp_coordinateLine_one (k : ℝ^2 → ℝ) (z : ℝ^2) :
    k ∘ coordinateLine 1 z = fun t ↦ k !₂[z 0, t] := by
  funext t; simp only [Function.comp_apply]; congr 1; ext i; fin_cases i <;> simp [coordinateLine]

/-- `∂₀K₁(z) = z₁ (z₁² - 3z₀²) / |z|⁶` off the origin. -/
theorem partialDeriv_zero_hessianKernel_zero_one {z : ℝ^2} (hz : z ≠ 0) :
    (∂[0] (hessianKernel 0 1)) z = z 1 * (z 1 ^ 2 - 3 * z 0 ^ 2) / ‖z‖ ^ 6 := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine 0 z
    ((contDiffAt_hessianKernel 0 1 hz (n := 1)).differentiableAt one_ne_zero),
    comp_coordinateLine_zero, (hasDerivAt_hessianKernel_zero_one_left (norm_sq_ne_zero hz)).deriv,
    norm_pow_six_eq]

/-- `∂₁K₁(z) = z₀ (z₀² - 3z₁²) / |z|⁶` off the origin. -/
theorem partialDeriv_one_hessianKernel_zero_one {z : ℝ^2} (hz : z ≠ 0) :
    (∂[1] (hessianKernel 0 1)) z = z 0 * (z 0 ^ 2 - 3 * z 1 ^ 2) / ‖z‖ ^ 6 := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine 1 z
    ((contDiffAt_hessianKernel 0 1 hz (n := 1)).differentiableAt one_ne_zero),
    comp_coordinateLine_one, (hasDerivAt_hessianKernel_zero_one_right (norm_sq_ne_zero hz)).deriv,
    norm_pow_six_eq]

/-- `∂₀K₂(z) = -∂₁K₁(z)` off the origin. -/
theorem partialDeriv_zero_hessianKernel_zero_zero {z : ℝ^2} (hz : z ≠ 0) :
    (∂[0] (hessianKernel 0 0)) z = -(z 0 * (z 0 ^ 2 - 3 * z 1 ^ 2) / ‖z‖ ^ 6) := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine 0 z
    ((contDiffAt_hessianKernel 0 0 hz (n := 1)).differentiableAt one_ne_zero),
    comp_coordinateLine_zero, (hasDerivAt_hessianKernel_zero_zero_left (norm_sq_ne_zero hz)).deriv,
    norm_pow_six_eq]

/-- `∂₁K₂(z) = ∂₀K₁(z)` off the origin. -/
theorem partialDeriv_one_hessianKernel_zero_zero {z : ℝ^2} (hz : z ≠ 0) :
    (∂[1] (hessianKernel 0 0)) z = z 1 * (z 1 ^ 2 - 3 * z 0 ^ 2) / ‖z‖ ^ 6 := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine 1 z
    ((contDiffAt_hessianKernel 0 0 hz (n := 1)).differentiableAt one_ne_zero),
    comp_coordinateLine_one, (hasDerivAt_hessianKernel_zero_zero_right (norm_sq_ne_zero hz)).deriv,
    norm_pow_six_eq]

/-- **`∂₀K₁ = ∂₁K₂` over a rectangle**: for a closed rectangle avoiding the origin, `∫_Q ∂₀K₁` is
the corner sum of `-u / (2 (u² + v²))`. -/
theorem integral_rectangle_partialDeriv_zero_hessianKernel_zero_one {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ y in coordinateRectangle a b c d, (∂[0] (hessianKernel 0 1)) y =
      cornerSum (fun u v ↦ -u / (2 * (u ^ 2 + v ^ 2))) a b c d := by
  rw [setIntegral_congr_fun (measurableSet_coordinateRectangle a b c d) fun y hy ↦
    partialDeriv_zero_hessianKernel_zero_one (ne_zero_of_mem_coordinateRectangle h0 hy)]
  exact integral_rectangle_deriv_zero_hessianKernel_zero_one hab hcd h0

/-- **`∂₁K₁ = -∂₀K₂` over a rectangle**: for a closed rectangle avoiding the origin, `∫_Q ∂₁K₁` is
the corner sum of `-v / (2 (u² + v²))`. -/
theorem integral_rectangle_partialDeriv_one_hessianKernel_zero_one {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ y in coordinateRectangle a b c d, (∂[1] (hessianKernel 0 1)) y =
      cornerSum (fun u v ↦ -v / (2 * (u ^ 2 + v ^ 2))) a b c d := by
  rw [setIntegral_congr_fun (measurableSet_coordinateRectangle a b c d) fun y hy ↦
    partialDeriv_one_hessianKernel_zero_one (ne_zero_of_mem_coordinateRectangle h0 hy)]
  exact integral_rectangle_deriv_one_hessianKernel_zero_one hab hcd h0

/-- `∫_Q ∂₀K₂ = -∫_Q ∂₁K₁`: the corner sum of `v / (2 (u² + v²))`. -/
theorem integral_rectangle_partialDeriv_zero_hessianKernel_zero_zero {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ y in coordinateRectangle a b c d, (∂[0] (hessianKernel 0 0)) y =
      cornerSum (fun u v ↦ v / (2 * (u ^ 2 + v ^ 2))) a b c d := by
  rw [setIntegral_congr_fun (measurableSet_coordinateRectangle a b c d) fun y hy ↦
    partialDeriv_zero_hessianKernel_zero_zero (ne_zero_of_mem_coordinateRectangle h0 hy),
    integral_neg, integral_rectangle_deriv_one_hessianKernel_zero_one hab hcd h0]
  unfold cornerSum
  ring

/-- `∫_Q ∂₁K₂ = ∫_Q ∂₀K₁`: the corner sum of `-u / (2 (u² + v²))`. -/
theorem integral_rectangle_partialDeriv_one_hessianKernel_zero_zero {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    ∫ y in coordinateRectangle a b c d, (∂[1] (hessianKernel 0 0)) y =
      cornerSum (fun u v ↦ -u / (2 * (u ^ 2 + v ^ 2))) a b c d := by
  rw [setIntegral_congr_fun (measurableSet_coordinateRectangle a b c d) fun y hy ↦
    partialDeriv_one_hessianKernel_zero_zero (ne_zero_of_mem_coordinateRectangle h0 hy)]
  exact integral_rectangle_deriv_zero_hessianKernel_zero_one hab hcd h0

/-! ### Symmetrized kernels -/

/-- `x - R₀ (p, q) = (x₀ + p, x₁ - q)`. -/
private theorem sub_reflect_zero_toLp (x : ℝ^2) (p q : ℝ) :
    x - PDE.Common.coordinateReflection 0 !₂[p, q] = !₂[x 0 + p, x 1 - q] := by
  ext i; fin_cases i
  · simp [PDE.Common.coordinateReflection_apply_same]
  · simp

/-- `x - R₁ (p, q) = (x₀ - p, x₁ + q)`. -/
private theorem sub_reflect_one_toLp (x : ℝ^2) (p q : ℝ) :
    x - PDE.Common.coordinateReflection 1 !₂[p, q] = !₂[x 0 - p, x 1 + q] := by
  ext i; fin_cases i
  · simp
  · simp [PDE.Common.coordinateReflection_apply_same]

/-- `x + (p, q) = (x₀ + p, x₁ + q)`. -/
private theorem add_toLp (x : ℝ^2) (p q : ℝ) : x + !₂[p, q] = !₂[x 0 + p, x 1 + q] := by
  ext i; fin_cases i <;> simp

/-- The substitution `(p, q) ↦ (u - p, v - q)` turns the iterated integral over `[a, b] × [c, d]`
into the one over `[u - b, u - a] × [v - d, v - c]`. -/
private theorem integral_sub_sub (g : ℝ → ℝ → ℝ) (a b c d u v : ℝ) :
    ∫ p in a..b, ∫ q in c..d, g (u - p) (v - q) =
      ∫ p in u - b..u - a, ∫ q in v - d..v - c, g p q := by
  have h (p : ℝ) : ∫ q in c..d, g (u - p) (v - q) = ∫ q in v - d..v - c, g (u - p) q :=
    intervalIntegral.integral_comp_sub_left (g (u - p)) v
  simp only [h]
  exact intervalIntegral.integral_comp_sub_left (fun p ↦ ∫ q in v - d..v - c, g p q) u

/-- The substitution `(p, q) ↦ (u + p, v - q)` turns the iterated integral over `[a, b] × [c, d]`
into the one over `[u + a, u + b] × [v - d, v - c]`. -/
private theorem integral_add_sub (g : ℝ → ℝ → ℝ) (a b c d u v : ℝ) :
    ∫ p in a..b, ∫ q in c..d, g (u + p) (v - q) =
      ∫ p in u + a..u + b, ∫ q in v - d..v - c, g p q := by
  have h (p : ℝ) : ∫ q in c..d, g (u + p) (v - q) = ∫ q in v - d..v - c, g (u + p) q :=
    intervalIntegral.integral_comp_sub_left (g (u + p)) v
  simp only [h]
  exact intervalIntegral.integral_comp_add_left (fun p ↦ ∫ q in v - d..v - c, g p q) u

/-- The substitution `(p, q) ↦ (u - p, v + q)` turns the iterated integral over `[a, b] × [c, d]`
into the one over `[u - b, u - a] × [v + c, v + d]`. -/
private theorem integral_sub_add (g : ℝ → ℝ → ℝ) (a b c d u v : ℝ) :
    ∫ p in a..b, ∫ q in c..d, g (u - p) (v + q) =
      ∫ p in u - b..u - a, ∫ q in v + c..v + d, g p q := by
  have h (p : ℝ) : ∫ q in c..d, g (u - p) (v + q) = ∫ q in v + c..v + d, g (u - p) q :=
    intervalIntegral.integral_comp_add_left (g (u - p)) v
  simp only [h]
  exact intervalIntegral.integral_comp_sub_left (fun p ↦ ∫ q in v + c..v + d, g p q) u

/-- The substitution `(p, q) ↦ (u + p, v + q)` turns the iterated integral over `[a, b] × [c, d]`
into the one over `[u + a, u + b] × [v + c, v + d]`. -/
private theorem integral_add_add (g : ℝ → ℝ → ℝ) (a b c d u v : ℝ) :
    ∫ p in a..b, ∫ q in c..d, g (u + p) (v + q) =
      ∫ p in u + a..u + b, ∫ q in v + c..v + d, g p q := by
  have h (p : ℝ) : ∫ q in c..d, g (u + p) (v + q) = ∫ q in v + c..v + d, g (u + p) q :=
    intervalIntegral.integral_comp_add_left (g (u + p)) v
  simp only [h]
  exact intervalIntegral.integral_comp_add_left (fun p ↦ ∫ q in v + c..v + d, g p q) u

/-- If `k` is continuous on `T` and the continuous map `e` sends `S` into `T`, then `k ∘ e` is
continuous on `S`. -/
private theorem continuousOn_comp_rectangle {k : ℝ^2 → ℝ} {e : ℝ^2 → ℝ^2} (he : Continuous e)
    {S T : Set (ℝ^2)} (hk : ContinuousOn k T) (hST : MapsTo e S T) :
    ContinuousOn (fun y ↦ k (e y)) S :=
  hk.comp he.continuousOn hST

/-- **Integral of a symmetrized kernel over a rectangle.** For `Q = [a, b] × [c, d]` and a kernel
`k` continuous on the four rectangles `x - Q`, `x - R₀ Q`, `x - R₁ Q` and `x + Q`,
`∫_Q kₛ(x, y) dy` is the alternating sum of the integrals of `k` over them. -/
theorem integral_rectangle_symmetrizedKernel {k : ℝ^2 → ℝ} (x : ℝ^2) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (h₁ : ContinuousOn k (coordinateRectangle (x 0 - b) (x 0 - a) (x 1 - d) (x 1 - c)))
    (h₂ : ContinuousOn k (coordinateRectangle (x 0 + a) (x 0 + b) (x 1 - d) (x 1 - c)))
    (h₃ : ContinuousOn k (coordinateRectangle (x 0 - b) (x 0 - a) (x 1 + c) (x 1 + d)))
    (h₄ : ContinuousOn k (coordinateRectangle (x 0 + a) (x 0 + b) (x 1 + c) (x 1 + d))) :
    ∫ y in coordinateRectangle a b c d, GreenFunction.symmetrizedKernel k x y =
      (∫ z in coordinateRectangle (x 0 - b) (x 0 - a) (x 1 - d) (x 1 - c), k z) -
        (∫ z in coordinateRectangle (x 0 + a) (x 0 + b) (x 1 - d) (x 1 - c), k z) -
        (∫ z in coordinateRectangle (x 0 - b) (x 0 - a) (x 1 + c) (x 1 + d), k z) +
        ∫ z in coordinateRectangle (x 0 + a) (x 0 + b) (x 1 + c) (x 1 + d), k z := by
  set R := coordinateRectangle a b c d
  have hR := isCompact_coordinateRectangle a b c d
  have c₁ : ContinuousOn (fun y ↦ k (x - y)) R :=
    continuousOn_comp_rectangle (e := fun y ↦ x - y) (by fun_prop) h₁ fun y hy ↦ by
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [PiLp.sub_apply] <;> linarith
  have c₂ : ContinuousOn (fun y ↦ k (x - PDE.Common.coordinateReflection 0 y)) R :=
    continuousOn_comp_rectangle (e := fun y ↦ x - PDE.Common.coordinateReflection 0 y)
      (continuous_const.sub (PDE.Common.coordinateReflectionLinearIsometryEquiv 0).continuous)
      h₂ fun y hy ↦ by
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
      have e0 := PDE.Common.coordinateReflection_apply_same 0 y
      have e1 := PDE.Common.coordinateReflection_apply_of_ne (0 : Fin 2) 1 (by decide) y
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [PiLp.sub_apply, e0, e1] <;> linarith
  have c₃ : ContinuousOn (fun y ↦ k (x - PDE.Common.coordinateReflection 1 y)) R :=
    continuousOn_comp_rectangle (e := fun y ↦ x - PDE.Common.coordinateReflection 1 y)
      (continuous_const.sub (PDE.Common.coordinateReflectionLinearIsometryEquiv 1).continuous)
      h₃ fun y hy ↦ by
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
      have e0 := PDE.Common.coordinateReflection_apply_of_ne (1 : Fin 2) 0 (by decide) y
      have e1 := PDE.Common.coordinateReflection_apply_same 1 y
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [PiLp.sub_apply, e0, e1] <;> linarith
  have c₄ : ContinuousOn (fun y ↦ k (x + y)) R :=
    continuousOn_comp_rectangle (e := fun y ↦ x + y) (by fun_prop) h₄ fun y hy ↦ by
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hy
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [PiLp.add_apply] <;> linarith
  unfold GreenFunction.symmetrizedKernel
  have i₁ : IntegrableOn (fun y ↦ k (x - y)) R := c₁.integrableOn_compact hR
  have i₂ : IntegrableOn (fun y ↦ k (x - PDE.Common.coordinateReflection 0 y)) R :=
    c₂.integrableOn_compact hR
  have i₃ : IntegrableOn (fun y ↦ k (x - PDE.Common.coordinateReflection 1 y)) R :=
    c₃.integrableOn_compact hR
  have i₄ : IntegrableOn (fun y ↦ k (x + y)) R := c₄.integrableOn_compact hR
  have i₁₂ : IntegrableOn (fun y ↦ k (x - y) - k (x - PDE.Common.coordinateReflection 0 y)) R :=
    i₁.sub i₂
  have i₁₂₃ : IntegrableOn (fun y ↦ k (x - y) - k (x - PDE.Common.coordinateReflection 0 y) -
      k (x - PDE.Common.coordinateReflection 1 y)) R := i₁₂.sub i₃
  rw [integral_add i₁₂₃ i₄, integral_sub i₁₂ i₃, integral_sub i₁ i₂]
  rw [setIntegral_coordinateRectangle hab hcd c₁,
    setIntegral_coordinateRectangle hab hcd c₂,
    setIntegral_coordinateRectangle hab hcd c₃, setIntegral_coordinateRectangle hab hcd c₄,
    setIntegral_coordinateRectangle (by linarith) (by linarith) h₁,
    setIntegral_coordinateRectangle (by linarith) (by linarith) h₂,
    setIntegral_coordinateRectangle (by linarith) (by linarith) h₃,
    setIntegral_coordinateRectangle (by linarith) (by linarith) h₄]
  simp only [sub_vec, sub_reflect_zero_toLp, sub_reflect_one_toLp, add_toLp]
  rw [integral_sub_sub (fun p q ↦ k !₂[p, q]), integral_add_sub (fun p q ↦ k !₂[p, q]),
    integral_sub_add (fun p q ↦ k !₂[p, q]), integral_add_add (fun p q ↦ k !₂[p, q])]

/-- The alternating sum of the corner sums of `H` over the four rectangles `x - Q`, `x - R₀ Q`,
`x - R₁ Q` and `x + Q` of `Q = [a, b] × [c, d]`: the integral of a symmetrized kernel over `Q`
when `H` is a mixed primitive of the kernel (`integral_rectangle_symmetrizedKernel_zero_one`). -/
def symmetrizedCornerSum (H : ℝ → ℝ → ℝ) (x : ℝ^2) (a b c d : ℝ) : ℝ :=
  cornerSum H (x 0 - b) (x 0 - a) (x 1 - d) (x 1 - c) -
    cornerSum H (x 0 + a) (x 0 + b) (x 1 - d) (x 1 - c) -
    cornerSum H (x 0 - b) (x 0 - a) (x 1 + c) (x 1 + d) +
    cornerSum H (x 0 + a) (x 0 + b) (x 1 + c) (x 1 + d)

/-- **`K₁ₛ` over a rectangle.** If the four rectangles `x - Q`, `x - R₀ Q`, `x - R₁ Q`, `x + Q` of
`Q = [a, b] × [c, d]` avoid the origin, `∫_Q K₁ₛ(x, y) dy` is the symmetrized corner sum of
`G(u, v) = -(1/4) log (u² + v²)`. -/
theorem integral_rectangle_symmetrizedKernel_zero_one (x : ℝ^2) {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h₁ : 0 < x 0 - b ∨ x 0 - a < 0 ∨ 0 < x 1 - d ∨ x 1 - c < 0)
    (h₂ : 0 < x 0 + a ∨ x 0 + b < 0 ∨ 0 < x 1 - d ∨ x 1 - c < 0)
    (h₃ : 0 < x 0 - b ∨ x 0 - a < 0 ∨ 0 < x 1 + c ∨ x 1 + d < 0)
    (h₄ : 0 < x 0 + a ∨ x 0 + b < 0 ∨ 0 < x 1 + c ∨ x 1 + d < 0) :
    ∫ y in coordinateRectangle a b c d, GreenFunction.symmetrizedKernel (hessianKernel 0 1) x y =
      symmetrizedCornerSum (fun u v ↦ -Real.log (u ^ 2 + v ^ 2) / 4) x a b c d := by
  rw [integral_rectangle_symmetrizedKernel x hab hcd (continuousOn_hessianKernel 0 1 h₁)
    (continuousOn_hessianKernel 0 1 h₂) (continuousOn_hessianKernel 0 1 h₃)
    (continuousOn_hessianKernel 0 1 h₄),
    integral_rectangle_hessianKernel_zero_one_eq_cornerSum (by linarith) (by linarith) h₁,
    integral_rectangle_hessianKernel_zero_one_eq_cornerSum (by linarith) (by linarith) h₂,
    integral_rectangle_hessianKernel_zero_one_eq_cornerSum (by linarith) (by linarith) h₃,
    integral_rectangle_hessianKernel_zero_one_eq_cornerSum (by linarith) (by linarith) h₄]
  rfl

/-- **`K₂ₛ` over a rectangle.** If the four rectangles `x - Q`, `x - R₀ Q`, `x - R₁ Q`, `x + Q` of
`Q = [a, b] × [c, d]` avoid the origin, `∫_Q K₂ₛ(x, y) dy` is the symmetrized corner sum of
`(1/2) arctan (u / v)`. -/
theorem integral_rectangle_symmetrizedKernel_zero_zero (x : ℝ^2) {a b c d : ℝ} (hab : a ≤ b)
    (hcd : c ≤ d) (h₁ : 0 < x 0 - b ∨ x 0 - a < 0 ∨ 0 < x 1 - d ∨ x 1 - c < 0)
    (h₂ : 0 < x 0 + a ∨ x 0 + b < 0 ∨ 0 < x 1 - d ∨ x 1 - c < 0)
    (h₃ : 0 < x 0 - b ∨ x 0 - a < 0 ∨ 0 < x 1 + c ∨ x 1 + d < 0)
    (h₄ : 0 < x 0 + a ∨ x 0 + b < 0 ∨ 0 < x 1 + c ∨ x 1 + d < 0) :
    ∫ y in coordinateRectangle a b c d, GreenFunction.symmetrizedKernel (hessianKernel 0 0) x y =
      symmetrizedCornerSum (fun u v ↦ Real.arctan (u / v) / 2) x a b c d := by
  rw [integral_rectangle_symmetrizedKernel x hab hcd (continuousOn_hessianKernel 0 0 h₁)
    (continuousOn_hessianKernel 0 0 h₂) (continuousOn_hessianKernel 0 0 h₃)
    (continuousOn_hessianKernel 0 0 h₄),
    integral_rectangle_hessianKernel_zero_zero_eq_cornerSum (by linarith) (by linarith) h₁,
    integral_rectangle_hessianKernel_zero_zero_eq_cornerSum (by linarith) (by linarith) h₂,
    integral_rectangle_hessianKernel_zero_zero_eq_cornerSum (by linarith) (by linarith) h₃,
    integral_rectangle_hessianKernel_zero_zero_eq_cornerSum (by linarith) (by linarith) h₄]
  rfl

/-! ### One logarithm and one arctangent -/

/-- The cross ratio `(b² + d²)(a² + c²) / ((a² + d²)(b² + c²))` of the corners of
`[a, b] × [c, d]`. -/
def crossRatio {K : Type*} [Field K] (a b c d : K) : K :=
  (b ^ 2 + d ^ 2) * (a ^ 2 + c ^ 2) / ((a ^ 2 + d ^ 2) * (b ^ 2 + c ^ 2))

/-- The cross ratio of rational corners, cast to `ℝ`, is the cross ratio of the cast corners. -/
theorem cast_crossRatio (a b c d : ℚ) :
    ((crossRatio a b c d : ℚ) : ℝ) = crossRatio (a : ℝ) b c d := by
  simp [crossRatio]

/-- Every corner `(u, v)` of a closed rectangle avoiding the origin has `u² + v² > 0`. -/
private theorem corner_pos {a b c d : ℝ} (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) {u v : ℝ}
    (hu : u = a ∨ u = b) (hv : v = c ∨ v = d) (hab : a ≤ b) (hcd : c ≤ d) :
    0 < u ^ 2 + v ^ 2 := by
  rcases lt_or_eq_of_le (by positivity : (0 : ℝ) ≤ u ^ 2 + v ^ 2) with h | h
  · exact h
  · exfalso
    have hu0 : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    have hv0 : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases h0 with h | h | h | h <;>
      linarith

/-- The corner sum of `-(1/4) log (u² + v²)` is `-(1/4) log` of the cross ratio. -/
theorem cornerSum_log_eq_neg_log_crossRatio {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) :
    cornerSum (fun u v ↦ -Real.log (u ^ 2 + v ^ 2) / 4) a b c d =
      -Real.log (crossRatio a b c d) / 4 := by
  have hac := corner_pos h0 (Or.inl rfl) (Or.inl rfl) hab hcd
  have had := corner_pos h0 (Or.inl rfl) (Or.inr rfl) hab hcd
  have hbc := corner_pos h0 (Or.inr rfl) (Or.inl rfl) hab hcd
  have hbd := corner_pos h0 (Or.inr rfl) (Or.inr rfl) hab hcd
  rw [cornerSum, crossRatio, Real.log_div (by positivity) (by positivity),
    Real.log_mul hbd.ne' hac.ne', Real.log_mul had.ne' hbc.ne']
  ring

/-- The rational `Z` with `∫_Q K₂ = (1/2) arctan Z` on `Q = [a, b] × [c, d]` in the first
quadrant. -/
def quadrantArg {K : Type*} [Field K] (a b c d : K) : K :=
  (b - a) * (d - c) * (a * b - c * d) / ((d ^ 2 + a * b) * (c ^ 2 + a * b) + (b - a) ^ 2 * c * d)

/-- `quadrantArg` of rational corners, cast to `ℝ`, is `quadrantArg` of the cast corners. -/
theorem cast_quadrantArg (a b c d : ℚ) :
    ((quadrantArg a b c d : ℚ) : ℝ) = quadrantArg (a : ℝ) b c d := by
  simp [quadrantArg]

/-- For `a, b ≥ 0` and `t > 0`, `arctan (b / t) - arctan (a / t) = arctan ((b - a) t / (t² + a b))`.
-/
private theorem arctan_div_sub_arctan_div {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) :
    Real.arctan (b / t) - Real.arctan (a / t) = Real.arctan ((b - a) * t / (t ^ 2 + a * b)) := by
  have hxy : b / t * -(a / t) < 1 := by
    have : 0 ≤ b / t * (a / t) := by positivity
    linarith [show b / t * -(a / t) = -(b / t * (a / t)) by ring]
  rw [sub_eq_add_neg, ← Real.arctan_neg, Real.arctan_add hxy]
  congr 1
  have h1 : 0 < t ^ 2 + a * b := by positivity
  have ht' : t ≠ 0 := ht.ne'
  have e1 : b / t + -(a / t) = (b - a) / t := by ring
  have e2 : 1 - b / t * -(a / t) = (t ^ 2 + a * b) / t ^ 2 := by field_simp; ring
  rw [e1, e2, div_div_eq_mul_div]
  field_simp

/-- On rectangles `0 ≤ a ≤ b`, `0 < c ≤ d` of the first quadrant, the corner sum of `(1/2) arctan (u
/ v)` is `(1/2) arctan Z` with `Z = quadrantArg a b c d`. -/
private theorem cornerSum_arctan_eq_arctan_quadrantArg_of_pos {a b c d : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) :
    cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d =
      Real.arctan (quadrantArg a b c d) / 2 := by
  have hb : 0 ≤ b := ha.trans hab
  have hd : 0 < d := hc.trans_le hcd
  have hX := arctan_div_sub_arctan_div ha hb hd
  have hY := arctan_div_sub_arctan_div hb ha hc
  set α := (b - a) * d / (d ^ 2 + a * b)
  set β := (a - b) * c / (c ^ 2 + b * a)
  have hα : 0 ≤ α := div_nonneg (mul_nonneg (by linarith) hd.le) (by positivity)
  have hβ : β ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith)
    hc.le) (by positivity)
  have hαβ : α * β < 1 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hα hβ]
  have hsum : cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d =
      (Real.arctan α + Real.arctan β) / 2 := by
    rw [← hX, ← hY]; unfold cornerSum; ring
  rw [hsum, Real.arctan_add hαβ]
  congr 2
  have h1 : (d ^ 2 + a * b) ≠ 0 := by positivity
  have h2 : (c ^ 2 + b * a) ≠ 0 := by positivity
  have e3 : α + β = (b - a) * (d - c) * (a * b - c * d) / ((d ^ 2 + a * b) * (c ^ 2 + b * a)) := by
    simp only [α, β]; field_simp; ring
  have e4 : 1 - α * β = ((d ^ 2 + a * b) * (c ^ 2 + a * b) + (b - a) ^ 2 * c * d) /
      ((d ^ 2 + a * b) * (c ^ 2 + b * a)) := by
    simp only [α, β]; field_simp; ring
  rw [e3, e4, div_div_div_cancel_right₀ (mul_ne_zero h1 h2), quadrantArg]

/-- **`∫_Q K₂` with one arctangent** on rectangles `0 ≤ a ≤ b`, `0 ≤ c ≤ d` of the closed first
quadrant avoiding the origin: the corner sum of `(1/2) arctan (u / v)` is `(1/2) arctan Z`. -/
theorem cornerSum_arctan_eq_arctan_quadrantArg {a b c d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 ≤ c) (hcd : c ≤ d) (h0 : 0 < a ∨ 0 < c) :
    cornerSum (fun u v ↦ Real.arctan (u / v) / 2) a b c d =
      Real.arctan (quadrantArg a b c d) / 2 := by
  rcases lt_or_eq_of_le hc with hc' | hc'
  · exact cornerSum_arctan_eq_arctan_quadrantArg_of_pos ha hab hc' hcd
  subst hc'
  have ha' : 0 < a := h0.resolve_right (lt_irrefl 0)
  have hb : 0 < b := ha'.trans_le hab
  rcases lt_or_eq_of_le hcd with hd | hd
  · rw [cornerSum]
    simp only [div_zero, Real.arctan_zero, zero_div, sub_zero, add_zero]
    have h := arctan_div_sub_arctan_div ha hb.le hd
    have e : quadrantArg a b 0 d = (b - a) * d / (d ^ 2 + a * b) := by
      have : 0 < a * b := mul_pos ha' hb
      have : 0 < d ^ 2 + a * b := by positivity
      simp only [quadrantArg]
      field_simp
      ring
    rw [e, ← h]
    ring
  · subst hd
    simp [cornerSum, quadrantArg]

/-- The cross ratio of the symmetrized kernel: `R₁ R₄ / (R₂ R₃)` for the four rectangles
`x - Q`, `x - R₀ Q`, `x - R₁ Q`, `x + Q`. -/
def symmetrizedCrossRatio {K : Type*} [Field K] (x₀ x₁ a b c d : K) : K :=
  crossRatio (x₀ - b) (x₀ - a) (x₁ - d) (x₁ - c) * crossRatio (x₀ + a) (x₀ + b) (x₁ + c) (x₁ + d) /
    (crossRatio (x₀ + a) (x₀ + b) (x₁ - d) (x₁ - c) *
      crossRatio (x₀ - b) (x₀ - a) (x₁ + c) (x₁ + d))

/-- The cross ratio of a closed rectangle avoiding the origin is positive. -/
theorem crossRatio_pos {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h0 : 0 < a ∨ b < 0 ∨ 0 < c ∨ d < 0) : 0 < crossRatio a b c d := by
  have hac := corner_pos h0 (Or.inl rfl) (Or.inl rfl) hab hcd
  have had := corner_pos h0 (Or.inl rfl) (Or.inr rfl) hab hcd
  have hbc := corner_pos h0 (Or.inr rfl) (Or.inl rfl) hab hcd
  have hbd := corner_pos h0 (Or.inr rfl) (Or.inr rfl) hab hcd
  unfold crossRatio; positivity

/-- **`∫_Q K₁ₛ(x, ·)` with one logarithm**: the symmetrized corner sum of
`-(1/4) log (u² + v²)` is `-(1/4) log (R₁ R₄ / (R₂ R₃))`. -/
theorem symmetrizedCornerSum_log_eq_neg_log_symmetrizedCrossRatio {x : ℝ^2} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (h₁ : 0 < x 0 - b ∨ x 0 - a < 0 ∨ 0 < x 1 - d ∨ x 1 - c < 0)
    (h₂ : 0 < x 0 + a ∨ x 0 + b < 0 ∨ 0 < x 1 - d ∨ x 1 - c < 0)
    (h₃ : 0 < x 0 - b ∨ x 0 - a < 0 ∨ 0 < x 1 + c ∨ x 1 + d < 0)
    (h₄ : 0 < x 0 + a ∨ x 0 + b < 0 ∨ 0 < x 1 + c ∨ x 1 + d < 0) :
    symmetrizedCornerSum (fun u v ↦ -Real.log (u ^ 2 + v ^ 2) / 4) x a b c d =
      -Real.log (symmetrizedCrossRatio (x 0) (x 1) a b c d) / 4 := by
  have e₁ : x 0 - b ≤ x 0 - a := by linarith
  have e₂ : x 1 - d ≤ x 1 - c := by linarith
  have e₃ : x 0 + a ≤ x 0 + b := by linarith
  have e₄ : x 1 + c ≤ x 1 + d := by linarith
  have r₁ := crossRatio_pos e₁ e₂ h₁
  have r₂ := crossRatio_pos e₃ e₂ h₂
  have r₃ := crossRatio_pos e₁ e₄ h₃
  have r₄ := crossRatio_pos e₃ e₄ h₄
  rw [symmetrizedCornerSum, cornerSum_log_eq_neg_log_crossRatio e₁ e₂ h₁,
    cornerSum_log_eq_neg_log_crossRatio e₃ e₂ h₂, cornerSum_log_eq_neg_log_crossRatio e₁ e₄ h₃,
    cornerSum_log_eq_neg_log_crossRatio e₃ e₄ h₄, symmetrizedCrossRatio,
    Real.log_div (by positivity) (by positivity), Real.log_mul r₁.ne' r₄.ne',
    Real.log_mul r₂.ne' r₃.ne']
  ring

end PotentialTheory.Planar
