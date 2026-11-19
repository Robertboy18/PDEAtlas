/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Fluid.Incompressible.HalfPlane.SharpHolder.StrainKernel

/-!
# The kernel of the Hölder estimates of `u_y` and `v_x`

The gradient components `u_y` and `v_x` of the half-plane velocity have the kernel
`K₂(y) = (y₁² - y₂²) / (2 |y|⁴)` (Chen and Hou, Part I, (3.1)), `shearDensity a b` in coordinates.
After scaling the two points to `(± 1, ·)`, their differences have the kernel

`Δ(y₁, y₂) = K₂(y₁ + 1, y₂) - K₂(y₁ - 1, y₂)`

(`shearDifference`, Part I, (B.6) and (B.44)). Its sign is carried by the quartic
`y₁⁴ - 2 y₁² y₂² - 2 y₁² - 3 y₂⁴ - 2 y₂² + 1` (`shearQuartic`): for `y₁ > 0`,
`Δ = -2 y₁ Q / (((y₁ + 1)² + y₂²)² ((y₁ - 1)² + y₂²)²)`. The zero set of `Q` in the first quadrant
is described by the sign functions of Part I, (B.62): for `y₁ > 0`, `Δ > 0` exactly when
`|y₂| > s_c(y₁)` (Part I, (B.5)), and exactly when `h_c^-(|y₂|) < y₁ < h_c^+(|y₂|)`
(Part I, (B.46)).

## Main definitions

* `shearDensity`: the kernel `K₂(a, b) = (a² - b²) / (2 (a² + b²)²)`.
* `shearDifference`: the difference kernel `Δ(y₁, y₂)`.
* `shearQuartic`: the quartic `Q` carrying the sign of `Δ`.
* `shearThreshold`: `s_c(y₁) = ((-(y₁² + 1) + 2 (y₁⁴ - y₁² + 1)^{1/2}) / 3)^{1/2}`.
* `lowerShearThreshold`, `upperShearThreshold`:
  `h_c^±(y₂) = (y₂² + 1 ± 2 y₂ (y₂² + 1)^{1/2})^{1/2}`.

## Main results

* `shearDifference_eq`: `Δ = -2 y₁ Q / (((y₁ + 1)² + y₂²)² ((y₁ - 1)² + y₂²)²)` off the poles
  `(± 1, 0)`.
* `shearQuartic_eq_upper_lower`: `Q = (y₁² - h_c^+(y₂)²)(y₁² - h_c^-(y₂)²)`.
* `shearQuartic_eq_threshold`: `Q = -3 (y₂² - s_c(y₁)²)(y₂² - v₋)` with `v₋ < 0`.
* `shearDifference_pos_iff`, `shearDifference_neg_iff`: for `y₁ > 0` off the pole `(1, 0)`,
  `Δ(y₁, y₂) > 0` exactly when `|y₂| > s_c(y₁)`, and `Δ(y₁, y₂) < 0` exactly when
  `|y₂| < s_c(y₁)`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, (3.1), p. 27, Appendix B.1.1, (B.5)
  and (B.6), p. 131, Appendix B.2, (B.44) and (B.46), p. 137, and Appendix B.3.1, (B.62), p. 141.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set

namespace IncompressibleFlow.SharpHolder

/-- The kernel `K₂(a, b) = (a² - b²) / (2 (a² + b²)²)` of Chen and Hou, Part I, (3.1), in
coordinates: the planar Hessian kernel `hessianKernel 0 0` at `(a, b)`. Its value at the origin
is `0`. -/
def shearDensity (a b : ℝ) : ℝ :=
  PotentialTheory.Planar.hessianKernel 0 0 !₂[a, b]

/-- `K₂(a, b) = (a² - b²) / (2 (a² + b²)²)`. -/
theorem shearDensity_eq (a b : ℝ) :
    shearDensity a b = (a ^ 2 - b ^ 2) / (2 * (a ^ 2 + b ^ 2) ^ 2) :=
  PotentialTheory.Planar.hessianKernel_zero_zero_toLp a b

/-- `K₂` is even in its first argument. -/
theorem shearDensity_neg_left (a b : ℝ) : shearDensity (-a) b = shearDensity a b := by
  simp only [shearDensity_eq, neg_sq]

/-- `K₂` is even in its second argument. -/
theorem shearDensity_neg_right (a b : ℝ) : shearDensity a (-b) = shearDensity a b := by
  simp only [shearDensity_eq, neg_sq]

/-- `K₂` is odd under the exchange of its arguments. -/
theorem shearDensity_comm (a b : ℝ) : shearDensity a b = -shearDensity b a := by
  simp only [shearDensity_eq]
  ring

/-- The difference kernel `Δ(y₁, y₂) = K₂(y₁ + 1, y₂) - K₂(y₁ - 1, y₂)` of Chen and Hou,
Part I, (B.44). -/
def shearDifference (y₁ y₂ : ℝ) : ℝ :=
  shearDensity (y₁ + 1) y₂ - shearDensity (y₁ - 1) y₂

/-- The quartic `y₁⁴ - 2 y₁² y₂² - 2 y₁² - 3 y₂⁴ - 2 y₂² + 1` carrying the sign of `Δ`. -/
def shearQuartic (y₁ y₂ : ℝ) : ℝ :=
  y₁ ^ 4 - 2 * y₁ ^ 2 * y₂ ^ 2 - 2 * y₁ ^ 2 - 3 * y₂ ^ 4 - 2 * y₂ ^ 2 + 1

/-- `Δ` is odd in `y₁`. -/
theorem shearDifference_neg_left (y₁ y₂ : ℝ) :
    shearDifference (-y₁) y₂ = -shearDifference y₁ y₂ := by
  simp only [shearDifference]
  rw [show -y₁ + 1 = -(y₁ - 1) by ring, show -y₁ - 1 = -(y₁ + 1) by ring, shearDensity_neg_left,
    shearDensity_neg_left]
  ring

/-- `Δ` is even in `y₂`. -/
theorem shearDifference_neg_right (y₁ y₂ : ℝ) :
    shearDifference y₁ (-y₂) = shearDifference y₁ y₂ := by
  simp only [shearDifference, shearDensity_neg_right]

/-- `Δ = -2 y₁ Q / (((y₁ + 1)² + y₂²)² ((y₁ - 1)² + y₂²)²)` off the poles `(± 1, 0)`. -/
theorem shearDifference_eq {y₁ y₂ : ℝ} (h₁ : (y₁ + 1) ^ 2 + y₂ ^ 2 ≠ 0)
    (h₂ : (y₁ - 1) ^ 2 + y₂ ^ 2 ≠ 0) :
    shearDifference y₁ y₂ = -2 * y₁ * shearQuartic y₁ y₂ /
      (((y₁ + 1) ^ 2 + y₂ ^ 2) ^ 2 * ((y₁ - 1) ^ 2 + y₂ ^ 2) ^ 2) := by
  simp only [shearDifference, shearDensity_eq, shearQuartic]
  field_simp
  ring

/-- The sign threshold `s_c(y₁) = ((-(y₁² + 1) + 2 (y₁⁴ - y₁² + 1)^{1/2}) / 3)^{1/2}` of Chen and
Hou, Part I, (B.62). -/
def shearThreshold (y₁ : ℝ) : ℝ :=
  Real.sqrt ((-(y₁ ^ 2 + 1) + 2 * Real.sqrt (y₁ ^ 4 - y₁ ^ 2 + 1)) / 3)

/-- The lower threshold `h_c^-(y₂) = (y₂² + 1 - 2 y₂ (y₂² + 1)^{1/2})^{1/2}` of Chen and Hou,
Part I, (B.62). -/
def lowerShearThreshold (y₂ : ℝ) : ℝ :=
  Real.sqrt (y₂ ^ 2 + 1 - 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1))

/-- The upper threshold `h_c^+(y₂) = (y₂² + 1 + 2 y₂ (y₂² + 1)^{1/2})^{1/2}` of Chen and Hou,
Part I, (B.62). -/
def upperShearThreshold (y₂ : ℝ) : ℝ :=
  Real.sqrt (y₂ ^ 2 + 1 + 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1))

/-- `((y² + 1)^{1/2})² = y² + 1`. -/
private theorem sqrt_sq_add_one (y : ℝ) :
    Real.sqrt (y ^ 2 + 1) ^ 2 = y ^ 2 + 1 := Real.sq_sqrt (by positivity)

/-- `Q = (y₁² - u₊)(y₁² - u₋)` with `u± = y₂² + 1 ± 2 y₂ (y₂² + 1)^{1/2}`, the squares of
`h_c^±`. -/
theorem shearQuartic_eq_upper_lower (y₁ y₂ : ℝ) :
    shearQuartic y₁ y₂ = (y₁ ^ 2 - (y₂ ^ 2 + 1 + 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1))) *
      (y₁ ^ 2 - (y₂ ^ 2 + 1 - 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1))) := by
  rw [shearQuartic]
  linear_combination (4 * y₂ ^ 2 : ℝ) * sqrt_sq_add_one y₂

/-- `h_c^+(y₂)² = y₂² + 1 + 2 y₂ (y₂² + 1)^{1/2}` for `y₂ ≥ 0`. -/
theorem upperShearThreshold_sq {y₂ : ℝ} (h : 0 ≤ y₂) :
    upperShearThreshold y₂ ^ 2 = y₂ ^ 2 + 1 + 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1) :=
  Real.sq_sqrt (by positivity)

/-- `h_c^-(y₂)² = y₂² + 1 - 2 y₂ (y₂² + 1)^{1/2}` for `0 ≤ y₂ ≤ 3^{-1/2}`, the range where the
lower sign change exists; `h_c^-(3^{-1/2}) = 0`. -/
theorem lowerShearThreshold_sq {y₂ : ℝ} (h' : 3 * y₂ ^ 2 ≤ 1) :
    lowerShearThreshold y₂ ^ 2 = y₂ ^ 2 + 1 - 2 * y₂ * Real.sqrt (y₂ ^ 2 + 1) := by
  refine Real.sq_sqrt ?_
  have h2 : 2 * y₂ ≤ Real.sqrt (y₂ ^ 2 + 1) := Real.le_sqrt_of_sq_le (by nlinarith)
  rcases le_or_gt 0 y₂ with h | h
  · nlinarith [Real.sqrt_nonneg (y₂ ^ 2 + 1), sqrt_sq_add_one y₂]
  · nlinarith [Real.sqrt_nonneg (y₂ ^ 2 + 1), sq_nonneg y₂]

/-- `(y₁² + 1)/2 ≤ (y₁⁴ - y₁² + 1)^{1/2}`, so the radicand of `s_c(y₁)²` is nonnegative. -/
private theorem sqrt_quartic_ge (y₁ : ℝ) :
    (y₁ ^ 2 + 1) / 2 ≤ Real.sqrt (y₁ ^ 4 - y₁ ^ 2 + 1) :=
  Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (y₁ ^ 2 - 1)])

/-- The square of `s_c`. -/
theorem shearThreshold_sq (y₁ : ℝ) :
    shearThreshold y₁ ^ 2 = (-(y₁ ^ 2 + 1) + 2 * Real.sqrt (y₁ ^ 4 - y₁ ^ 2 + 1)) / 3 := by
  rw [shearThreshold, Real.sq_sqrt]
  have := sqrt_quartic_ge y₁
  linarith

/-- `Q = -3 (y₂² - s_c(y₁)²)(y₂² - v₋)` with
`v₋ = (-(y₁² + 1) - 2 (y₁⁴ - y₁² + 1)^{1/2}) / 3 < 0`. -/
theorem shearQuartic_eq_threshold (y₁ y₂ : ℝ) :
    shearQuartic y₁ y₂ = -3 * (y₂ ^ 2 - shearThreshold y₁ ^ 2) *
      (y₂ ^ 2 - (-(y₁ ^ 2 + 1) - 2 * Real.sqrt (y₁ ^ 4 - y₁ ^ 2 + 1)) / 3) := by
  have hw := Real.sq_sqrt (show (0 : ℝ) ≤ y₁ ^ 4 - y₁ ^ 2 + 1 by nlinarith [sq_nonneg (y₁ ^ 2 - 1)])
  rw [shearThreshold_sq, shearQuartic]
  linear_combination (-4 / 3 : ℝ) * hw

/-- `y₂² - v₋ > 0` for the negative root `v₋ = (-(y₁² + 1) - 2 (y₁⁴ - y₁² + 1)^{1/2}) / 3` of
`Q(y₁, ·)` as a quadratic in `y₂²`. -/
private theorem sq_sub_negRoot_pos (y₁ y₂ : ℝ) :
    0 < y₂ ^ 2 - (-(y₁ ^ 2 + 1) - 2 * Real.sqrt (y₁ ^ 4 - y₁ ^ 2 + 1)) / 3 := by
  have := Real.sqrt_nonneg (y₁ ^ 4 - y₁ ^ 2 + 1)
  nlinarith [sq_nonneg y₂, sq_nonneg y₁]

/-- For `y₁ > 0` off the pole `(1, 0)`, `Δ(y₁, y₂) > 0` exactly when `|y₂| > s_c(y₁)`, Chen and
Hou, Part I, (B.5). -/
theorem shearDifference_pos_iff {y₁ y₂ : ℝ} (h₁ : 0 < y₁) (h₂ : (y₁ - 1) ^ 2 + y₂ ^ 2 ≠ 0) :
    0 < shearDifference y₁ y₂ ↔ shearThreshold y₁ < |y₂| := by
  have h₃ : (y₁ + 1) ^ 2 + y₂ ^ 2 ≠ 0 := by positivity
  have hd : 0 < ((y₁ + 1) ^ 2 + y₂ ^ 2) ^ 2 * ((y₁ - 1) ^ 2 + y₂ ^ 2) ^ 2 := by positivity
  rw [shearDifference_eq h₃ h₂, div_pos_iff_of_pos_right hd, shearQuartic_eq_threshold]
  have ha := sq_sub_negRoot_pos y₁ y₂
  have hs : 0 ≤ shearThreshold y₁ := Real.sqrt_nonneg _
  have hy := sq_abs y₂
  constructor
  · intro hpos
    by_contra hle
    push Not at hle
    have : y₂ ^ 2 ≤ shearThreshold y₁ ^ 2 := by nlinarith [abs_nonneg y₂]
    nlinarith [mul_nonneg (mul_nonneg h₁.le (sub_nonneg.2 this)) ha.le]
  · intro hlt
    have : shearThreshold y₁ ^ 2 < y₂ ^ 2 := by nlinarith [abs_nonneg y₂]
    have := mul_pos (mul_pos h₁ (sub_pos.2 this)) ha
    nlinarith

/-- For `y₁ > 0` off the pole `(1, 0)`, `Δ(y₁, y₂) < 0` exactly when `|y₂| < s_c(y₁)`. -/
theorem shearDifference_neg_iff {y₁ y₂ : ℝ} (h₁ : 0 < y₁) (h₂ : (y₁ - 1) ^ 2 + y₂ ^ 2 ≠ 0) :
    shearDifference y₁ y₂ < 0 ↔ |y₂| < shearThreshold y₁ := by
  have h₃ : (y₁ + 1) ^ 2 + y₂ ^ 2 ≠ 0 := by positivity
  have hd : 0 < ((y₁ + 1) ^ 2 + y₂ ^ 2) ^ 2 * ((y₁ - 1) ^ 2 + y₂ ^ 2) ^ 2 := by positivity
  rw [shearDifference_eq h₃ h₂, div_neg_iff, shearQuartic_eq_threshold]
  have ha := sq_sub_negRoot_pos y₁ y₂
  have hs : 0 ≤ shearThreshold y₁ := Real.sqrt_nonneg _
  have hy := sq_abs y₂
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact absurd hd (not_lt.2 h.le)
    · by_contra hle
      push Not at hle
      have : shearThreshold y₁ ^ 2 ≤ y₂ ^ 2 := by nlinarith [abs_nonneg y₂]
      nlinarith [mul_nonneg (mul_nonneg h₁.le (sub_nonneg.2 this)) ha.le]
  · intro hlt
    have : y₂ ^ 2 < shearThreshold y₁ ^ 2 := by nlinarith [abs_nonneg y₂]
    have := mul_pos (mul_pos h₁ (sub_pos.2 this)) ha
    exact Or.inr ⟨by nlinarith, hd⟩

end IncompressibleFlow.SharpHolder
