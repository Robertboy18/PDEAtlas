/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.Directional
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Hölder quotients, products and rectangular paths

Pointwise bookkeeping for two-point Hölder estimates of real functions on a metric space, following
Chen and Hou (Part I, Section 5.4.1, (5.37)-(5.42), and Supplementary material I, Sections 8.2 and
8.9). On a coordinate line the Hölder quotient `δ(f, x, z)` is the directional quotient `δ_i` of
(5.37). The product estimate `δ(f, g, x, z)` of (5.39) is the better of the two splittings
`(fg)(x) - (fg)(z) = (f(x) - f(z)) g(a) + (g(x) - g(z)) f(b)` with `(a, b) = (x, z)` or `(z, x)`. In
the plane, `δ_□(f, g, x, z, s)` of (5.41) is the better of the two rectangular paths from `x` to `z`
through `(z₁, x₂)` and `(x₁, z₂)`, with the side lengths taken from a separate vector `s`, so that
`δ_□(f, g, x, z, s) g(s)` is homogeneous of degree zero in `s` for a `(-α)`-homogeneous weight `g`.

The last section records elementary facts behind the piecewise bounds of Supplementary
material I, Sections 8.9.2 and 8.9.3: `t ↦ t^α` is `α`-Hölder with constant one, so
`[|x|^α]_{C^α} ≤ 1`; on a horizontal line `|y| - |x|` and `|y|^{1/2} - |x|^{1/2}` factor
through `(y₁ - x₁)(y₁ + x₁)`, as in (8.75); `b^p - a^p ≤ p (b - a)(a^{p-1} + b^{p-1}) / 2` for
`p ≥ 2`; and `(1 - λ)(1 + λ)² ≤ 32/27`, as in (8.73).

## Main definitions

* `holderQuotient`: the Hölder quotient `δ(f, x, z) = |f x - f z| / |x - z|^α`.
* `productQuotient`: the product estimate `δ(f, g, x, z)` of (5.39).
* `boxBound`: the rectangular path estimate `δ_□(f, g, x, z, s)` of (5.41).

## Main results

* `holderQuotient_mul_le`: `δ(fg, x, z) ≤ δ(f, g, x, z)`, (5.38b).
* `abs_mul_sub_le_boxBound`: `|(fg)(x) - (fg)(z)| ≤ δ_□(f, g, x, z, x - z)`, (5.42).
* `boxBound_comm`: `δ_□` is symmetric in the two points.
* `boxBound_smul`: `δ_□(f, g, x, z, t s) = t^α δ_□(f, g, x, z, s)` for `t ≥ 0`.
* `boxBound_le`: local upper bounds of the product estimates on the legs of a rectangular path
  bound `δ_□`.
* `holderWith_norm_rpow`: `y ↦ ‖y‖^α` is `α`-Hölder with constant one for `0 < α ≤ 1`.
* `rpow_sub_rpow_le_mul_add`: `b^p - a^p ≤ p (b - a)(a^{p-1} + b^{p-1}) / 2` for `p ≥ 2` and
  `0 ≤ a ≤ b`.
* `one_sub_mul_one_add_sq_le`: `(1 - λ)(1 + λ)² ≤ 32/27` for `λ ≥ -5/3`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 5.4.1, (5.37)-(5.42);
  Supplementary material I (in the same PDF), Sections 8.2, 8.9.2 and 8.9.3.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

open Set
open scoped ENNReal NNReal

namespace HolderSpace

section Quotient

variable {X : Type*} [MetricSpace X] {α : ℝ} {f g : X → ℝ} {x z : X}

/-- The Hölder quotient `|f x - f z| / |x - z|^α`; it is zero when `x = z`. On a coordinate
line with `α = 1/2` it is the directional quotient `δ_i` of Chen and Hou (5.37). -/
def holderQuotient (α : ℝ) (f : X → ℝ) (x z : X) : ℝ :=
  |f x - f z| / dist x z ^ α

/-- The Hölder quotient is nonnegative. -/
theorem holderQuotient_nonneg : 0 ≤ holderQuotient α f x z :=
  div_nonneg (abs_nonneg _) (Real.rpow_nonneg dist_nonneg _)

/-- The Hölder quotient is symmetric in the two points. -/
theorem holderQuotient_comm : holderQuotient α f x z = holderQuotient α f z x := by
  rw [holderQuotient, holderQuotient, abs_sub_comm, dist_comm]

/-- A difference is the Hölder quotient times the distance to the power `α`. -/
theorem abs_sub_eq_holderQuotient_mul :
    |f x - f z| = holderQuotient α f x z * dist x z ^ α := by
  rcases eq_or_ne x z with rfl | hxz
  · simp [holderQuotient]
  · rw [holderQuotient, div_mul_cancel₀]
    exact (Real.rpow_pos_of_pos (dist_pos.2 hxz) _).ne'

/-- The Hölder quotient is at most `C` when the Hölder bound with constant `C` holds. -/
theorem holderQuotient_le {C : ℝ} (hC : 0 ≤ C) (h : |f x - f z| ≤ C * dist x z ^ α) :
    holderQuotient α f x z ≤ C := by
  rcases eq_or_ne x z with rfl | hxz
  · simpa [holderQuotient] using hC
  · exact div_le_of_le_mul₀ (Real.rpow_nonneg dist_nonneg _) hC h

/-- The product estimate `δ(f, g, x, z)` of Chen and Hou (5.39): the smaller of
`δ(f) |g x| + δ(g) |f z|` and `δ(f) |g z| + δ(g) |f x|`. -/
def productQuotient (α : ℝ) (f g : X → ℝ) (x z : X) : ℝ :=
  min (holderQuotient α f x z * |g x| + holderQuotient α g x z * |f z|)
    (holderQuotient α f x z * |g z| + holderQuotient α g x z * |f x|)

/-- The product estimate is nonnegative. -/
theorem productQuotient_nonneg : 0 ≤ productQuotient α f g x z :=
  le_min
    (add_nonneg (mul_nonneg holderQuotient_nonneg (abs_nonneg _))
      (mul_nonneg holderQuotient_nonneg (abs_nonneg _)))
    (add_nonneg (mul_nonneg holderQuotient_nonneg (abs_nonneg _))
      (mul_nonneg holderQuotient_nonneg (abs_nonneg _)))

/-- The product estimate is symmetric in the two points. -/
theorem productQuotient_comm : productQuotient α f g x z = productQuotient α f g z x := by
  rw [productQuotient, productQuotient, holderQuotient_comm (x := x), holderQuotient_comm (x := x),
    min_comm]

/-- With `g = 1` the product estimate is the Hölder quotient of `f`. -/
@[simp]
theorem productQuotient_one : productQuotient α f 1 x z = holderQuotient α f x z := by
  simp [productQuotient, holderQuotient]

omit [MetricSpace X] in
/-- The two product splittings (Chen and Hou (5.38a)) in absolute value:
`|(fg)(x) - (fg)(z)|` is at most both `|δf| |g x| + |δg| |f z|` and `|δf| |g z| + |δg| |f x|`. -/
theorem abs_mul_sub_mul_le :
    |f x * g x - f z * g z| ≤
      min (|f x - f z| * |g x| + |g x - g z| * |f z|)
        (|f x - f z| * |g z| + |g x - g z| * |f x|) := by
  refine le_min ?_ ?_
  · calc |f x * g x - f z * g z| = |(f x - f z) * g x + (g x - g z) * f z| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
  · calc |f x * g x - f z * g z| = |(f x - f z) * g z + (g x - g z) * f x| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])

/-- The product rule of Chen and Hou (5.38b): `δ(fg, x, z) ≤ δ(f, g, x, z)`. -/
theorem holderQuotient_mul_le : holderQuotient α (f * g) x z ≤ productQuotient α f g x z := by
  have hd : 0 ≤ dist x z ^ α := Real.rpow_nonneg dist_nonneg _
  calc holderQuotient α (f * g) x z = |f x * g x - f z * g z| / dist x z ^ α := rfl
    _ ≤ min (|f x - f z| * |g x| + |g x - g z| * |f z|)
          (|f x - f z| * |g z| + |g x - g z| * |f x|) / dist x z ^ α := by
        gcongr
        exact abs_mul_sub_mul_le
    _ = productQuotient α f g x z := by
        rw [productQuotient, holderQuotient, holderQuotient, ← min_div_div_right hd]
        congr 1 <;> ring

end Quotient

section Box

variable {α : ℝ} {f g : ℝ^2 → ℝ} {x z : ℝ^2}

/-- The rectangular path estimate `δ_□(f, g, x, z, s)` of Chen and Hou (5.41): the smaller of
the estimates along the paths `x → (z₁, x₂) → z` and `x → (x₁, z₂) → z`, with side lengths
`|s₁|`, `|s₂|`. -/
def boxBound (α : ℝ) (f g : ℝ^2 → ℝ) (x z s : ℝ^2) : ℝ :=
  min (productQuotient α f g x !₂[z 0, x 1] * |s 0| ^ α +
      productQuotient α f g !₂[z 0, x 1] z * |s 1| ^ α)
    (productQuotient α f g x !₂[x 0, z 1] * |s 1| ^ α +
      productQuotient α f g !₂[x 0, z 1] z * |s 0| ^ α)

/-- One leg of a rectangular path: `|(fg)(p) - (fg)(q)| ≤ δ(f, g, p, q) |p_i - q_i|^α` when
`p` and `q` differ only in the coordinate `i`. -/
private theorem abs_mul_sub_le_leg {i : Fin 2} {p q : ℝ^2} (h : ∀ j ≠ i, p j = q j) :
    |f p * g p - f q * g q| ≤ productQuotient α f g p q * |p i - q i| ^ α := by
  have := abs_sub_eq_holderQuotient_mul (α := α) (f := f * g) (x := p) (z := q)
  simp only [Pi.mul_apply] at this
  rw [this, dist_eq_dist_apply h, Real.dist_eq]
  exact mul_le_mul_of_nonneg_right holderQuotient_mul_le (Real.rpow_nonneg (abs_nonneg _) _)

/-- The rectangular path estimate of Chen and Hou (5.42) for a product:
`|(fg)(x) - (fg)(z)| ≤ δ_□(f, g, x, z, x - z)`. -/
theorem abs_mul_sub_le_boxBound :
    |f x * g x - f z * g z| ≤ boxBound α f g x z (x - z) := by
  set w : ℝ^2 := !₂[z 0, x 1]
  set w' : ℝ^2 := !₂[x 0, z 1]
  have hxw : ∀ j ≠ (0 : Fin 2), x j = w j := by
    intro j hj; fin_cases j
    · exact absurd rfl hj
    · simp [w]
  have hwz : ∀ j ≠ (1 : Fin 2), w j = z j := by
    intro j hj; fin_cases j
    · simp [w]
    · exact absurd rfl hj
  have hxw' : ∀ j ≠ (1 : Fin 2), x j = w' j := by
    intro j hj; fin_cases j
    · simp [w']
    · exact absurd rfl hj
  have hw'z : ∀ j ≠ (0 : Fin 2), w' j = z j := by
    intro j hj; fin_cases j
    · exact absurd rfl hj
    · simp [w']
  refine le_min ?_ ?_
  · calc |f x * g x - f z * g z|
        ≤ |f x * g x - f w * g w| + |f w * g w - f z * g z| := abs_sub_le _ _ _
      _ ≤ productQuotient α f g x w * |x 0 - w 0| ^ α +
            productQuotient α f g w z * |w 1 - z 1| ^ α :=
          add_le_add (abs_mul_sub_le_leg hxw) (abs_mul_sub_le_leg hwz)
      _ = _ := by simp [w]
  · calc |f x * g x - f z * g z|
        ≤ |f x * g x - f w' * g w'| + |f w' * g w' - f z * g z| := abs_sub_le _ _ _
      _ ≤ productQuotient α f g x w' * |x 1 - w' 1| ^ α +
            productQuotient α f g w' z * |w' 0 - z 0| ^ α :=
          add_le_add (abs_mul_sub_le_leg hxw') (abs_mul_sub_le_leg hw'z)
      _ = _ := by simp [w']

/-- The rectangular path estimate of Chen and Hou (5.42):
`|f x - f z| ≤ δ_□(f, x, z, x - z)`, with `δ_□(f, x, z, s) = δ_□(f, 1, x, z, s)`. -/
theorem abs_sub_le_boxBound : |f x - f z| ≤ boxBound α f 1 x z (x - z) := by
  simpa using abs_mul_sub_le_boxBound (α := α) (f := f) (g := 1) (x := x) (z := z)

/-- The rectangular path estimate is symmetric in the two points: exchanging `x` and `z`
exchanges the two paths. -/
theorem boxBound_comm (s : ℝ^2) : boxBound α f g x z s = boxBound α f g z x s := by
  rw [boxBound, boxBound, min_comm]
  congr 1 <;> rw [add_comm, productQuotient_comm (x := x), productQuotient_comm (z := z)]

/-- The rectangular path estimate scales like `|s|^α`:
`δ_□(f, g, x, z, t s) = t^α δ_□(f, g, x, z, s)` for `t ≥ 0`, so `δ_□(f, g, x, z, s) g(s)` is
homogeneous of degree zero in `s` for a `(-α)`-homogeneous weight `g`. -/
theorem boxBound_smul {t : ℝ} (ht : 0 ≤ t) (s : ℝ^2) :
    boxBound α f g x z (t • s) = t ^ α * boxBound α f g x z s := by
  simp only [boxBound, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht,
    Real.mul_rpow ht (abs_nonneg _)]
  rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg ht _)]
  congr 1 <;> ring

/-- Local upper bounds of the product estimates on the legs of one rectangular path bound the
rectangular path estimate. -/
theorem boxBound_le {s : ℝ^2} {A₀ A₁ : ℝ}
    (h₀ : productQuotient α f g x !₂[z 0, x 1] ≤ A₀)
    (h₁ : productQuotient α f g !₂[z 0, x 1] z ≤ A₁) :
    boxBound α f g x z s ≤ A₀ * |s 0| ^ α + A₁ * |s 1| ^ α :=
  (min_le_left _ _).trans (add_le_add
    (mul_le_mul_of_nonneg_right h₀ (Real.rpow_nonneg (abs_nonneg _) _))
    (mul_le_mul_of_nonneg_right h₁ (Real.rpow_nonneg (abs_nonneg _) _)))

/-- Local upper bounds of the product estimates on the legs of the other rectangular path bound
the rectangular path estimate. -/
theorem boxBound_le' {s : ℝ^2} {A₀ A₁ : ℝ}
    (h₁ : productQuotient α f g x !₂[x 0, z 1] ≤ A₁)
    (h₀ : productQuotient α f g !₂[x 0, z 1] z ≤ A₀) :
    boxBound α f g x z s ≤ A₀ * |s 0| ^ α + A₁ * |s 1| ^ α :=
  (min_le_right _ _).trans (by
    rw [add_comm]
    exact add_le_add
      (mul_le_mul_of_nonneg_right h₀ (Real.rpow_nonneg (abs_nonneg _) _))
      (mul_le_mul_of_nonneg_right h₁ (Real.rpow_nonneg (abs_nonneg _) _)))

end Box

section Power

/-- The power `t ↦ t^α` with `α ∈ [0, 1]` is `α`-Hölder on `[0, ∞)` with constant one:
`|a^α - b^α| ≤ |a - b|^α`. -/
theorem abs_rpow_sub_rpow_le {a b α : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hα₀ : 0 ≤ α)
    (hα₁ : α ≤ 1) : |a ^ α - b ^ α| ≤ |a - b| ^ α := by
  wlog hba : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]
    exact this hb ha (le_of_not_ge hba)
  have hsub := Real.rpow_add_le_add_rpow (sub_nonneg.2 hba) hb hα₀ hα₁
  rw [sub_add_cancel] at hsub
  rw [abs_of_nonneg (sub_nonneg.2 (Real.rpow_le_rpow hb hba hα₀)),
    abs_of_nonneg (sub_nonneg.2 hba)]
  linarith

/-- The function `y ↦ ‖y‖^α` with `α ∈ (0, 1]` is `α`-Hölder with constant one, so its
directional and `C^α` seminorms are at most one. Chen and Hou bound the quotients of `|x|^{1/2}`
piecewise in Supplementary material I, Section 8.9.3. -/
theorem holderWith_norm_rpow {E : Type*} [SeminormedAddCommGroup E] {α : ℝ≥0} (hα : α ≤ 1) :
    HolderWith 1 α fun y : E ↦ ‖y‖ ^ (α : ℝ) := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.coe_one, one_mul,
    ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg α)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.dist_eq, dist_eq_norm]
  exact (abs_rpow_sub_rpow_le (norm_nonneg _) (norm_nonneg _) α.2 (by exact_mod_cast hα)).trans
    (Real.rpow_le_rpow (abs_nonneg _) (abs_norm_sub_norm_le x y) α.2)

/-- The tangent line of the convex power `u ↦ u^q`, `q ≥ 1`, at `t ≥ 0` lies below the graph:
`t^q + q t^{q-1} (a - t) ≤ a^q` for `a ≥ 0`. -/
theorem rpow_add_mul_sub_le {q a t : ℝ} (hq : 1 ≤ q) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    t ^ q + q * t ^ (q - 1) * (a - t) ≤ a ^ q := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · rw [Real.zero_rpow (by linarith), sub_zero, zero_add]
    rcases eq_or_lt_of_le hq with rfl | hq'
    · simp
    · rw [Real.zero_rpow (by linarith), mul_zero, zero_mul]
      exact Real.rpow_nonneg ha _
  · have hs : -1 ≤ (a - t) / t := by
      rw [le_div_iff₀ htpos]
      linarith
    have h := one_add_mul_self_le_rpow_one_add hs hq
    have h1 : 1 + (a - t) / t = a / t := by field_simp; ring
    rw [h1, Real.div_rpow ha htpos.le, le_div_iff₀ (Real.rpow_pos_of_pos htpos _)] at h
    have h2 : t ^ (q - 1) = t ^ q / t := Real.rpow_sub_one htpos.ne' q
    rw [h2]
    have h3 : q * (t ^ q / t) * (a - t) = q * ((a - t) / t) * t ^ q := by
      field_simp
    rw [h3]
    linarith

/-- The endpoint estimate of Chen and Hou (Supplementary material I, Section 8.9.3): for `p ≥ 2`
and `0 ≤ a ≤ b`, `b^p - a^p ≤ p (b - a) (a^{p-1} + b^{p-1}) / 2`, the trapezoid bound for the
convex integrand `p t^{p-1}`. -/
theorem rpow_sub_rpow_le_mul_add {a b p : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hp : 2 ≤ p) :
    b ^ p - a ^ p ≤ p * (b - a) / 2 * (a ^ (p - 1) + b ^ (p - 1)) := by
  set F : ℝ → ℝ := fun t ↦ p * (t - a) / 2 * (a ^ (p - 1) + t ^ (p - 1)) - (t ^ p - a ^ p)
  have hderiv : ∀ t, HasDerivAt F (p * 1 / 2 * (a ^ (p - 1) + t ^ (p - 1)) +
      p * (t - a) / 2 * ((p - 1) * t ^ (p - 1 - 1)) - p * t ^ (p - 1)) t := fun t ↦ by
    have h₁ : HasDerivAt (fun t : ℝ ↦ t ^ (p - 1)) ((p - 1) * t ^ (p - 1 - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inr (by linarith))
    have h₂ : HasDerivAt (fun t : ℝ ↦ t ^ p) (p * t ^ (p - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inr (by linarith))
    exact (((((hasDerivAt_id t).sub_const a).const_mul p).div_const 2).mul
      (h₁.const_add _)).sub (h₂.sub_const _)
  have hmono : MonotoneOn F (Ici a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici a)
      (fun t _ ↦ (hderiv t).continuousAt.continuousWithinAt)
      (fun t _ ↦ (hderiv t).differentiableAt.differentiableWithinAt) fun t ht ↦ ?_
    rw [interior_Ici] at ht
    have hta : a < t := ht
    rw [(hderiv t).deriv]
    have htan := rpow_add_mul_sub_le (q := p - 1) (by linarith) ha (ha.trans hta.le)
    have hp0 : 0 ≤ p := by linarith
    have hsplit : t ^ (p - 1 - 1) * t = t ^ (p - 1) := by
      rw [← Real.rpow_add_one (by linarith : t ≠ 0)]
      ring_nf
    nlinarith [mul_nonneg hp0 (sub_nonneg.2 htan)]
  have h := hmono self_mem_Ici hab hab
  simp only [F, sub_self, mul_zero, zero_div, zero_mul] at h
  linarith

section Line

variable {x y : ℝ^2}

/-- On a horizontal line `|y|² - |x|² = (y₁ - x₁)(y₁ + x₁)`. -/
theorem norm_sq_sub_norm_sq_of_eq (h : x 1 = y 1) :
    ‖y‖ ^ 2 - ‖x‖ ^ 2 = (y 0 - x 0) * (y 0 + x 0) := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    Fin.sum_univ_two, h]
  ring

/-- On a horizontal line `|y| - |x| = (y₁ - x₁) M` with `M = (y₁ + x₁) / (|x| + |y|)`, the
factorization of Chen and Hou (Supplementary material I, (8.75)). -/
theorem norm_sub_norm_eq_of_eq (h : x 1 = y 1) (hxy : 0 < ‖x‖ + ‖y‖) :
    ‖y‖ - ‖x‖ = (y 0 - x 0) * ((y 0 + x 0) / (‖x‖ + ‖y‖)) := by
  rw [mul_div_assoc', eq_div_iff hxy.ne', ← norm_sq_sub_norm_sq_of_eq h]
  ring

/-- The factor `M = (y₁ + x₁) / (|x| + |y|)` is at most one in absolute value. -/
theorem abs_add_div_norm_add_le (hxy : 0 < ‖x‖ + ‖y‖) :
    |(y 0 + x 0) / (‖x‖ + ‖y‖)| ≤ 1 := by
  rw [abs_div, abs_of_pos hxy, div_le_one hxy]
  have hx : |x 0| ≤ ‖x‖ := by
    simpa using PiLp.norm_apply_le x 0
  have hy : |y 0| ≤ ‖y‖ := by
    simpa using PiLp.norm_apply_le y 0
  calc |y 0 + x 0| ≤ |y 0| + |x 0| := abs_add_le _ _
    _ ≤ ‖x‖ + ‖y‖ := by linarith

/-- On a horizontal line
`|y|^{1/2} - |x|^{1/2} = (y₁ - x₁)(y₁ + x₁) / ((|x| + |y|)(|x|^{1/2} + |y|^{1/2}))`, the
identity `M M₁` of Chen and Hou (Supplementary material I, (8.75)). -/
theorem sqrt_norm_sub_sqrt_norm_eq_of_eq (h : x 1 = y 1) (hxy : 0 < ‖x‖ + ‖y‖) :
    √‖y‖ - √‖x‖ = (y 0 - x 0) * (y 0 + x 0) / ((‖x‖ + ‖y‖) * (√‖x‖ + √‖y‖)) := by
  have hs : 0 < √‖x‖ + √‖y‖ := by
    by_cases hx : 0 < ‖x‖
    · exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 hx) (Real.sqrt_nonneg _)
    · have hy : 0 < ‖y‖ := by linarith [norm_nonneg x, not_lt.1 hx]
      exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (Real.sqrt_pos.2 hy)
  rw [← norm_sq_sub_norm_sq_of_eq h, eq_div_iff (mul_pos hxy hs).ne']
  have h₁ := Real.sq_sqrt (norm_nonneg x)
  have h₂ := Real.sq_sqrt (norm_nonneg y)
  nlinarith [h₁, h₂]

end Line

/-- The elementary bound `(1 - λ)(1 + λ)² ≤ 32/27` for `λ ≥ -5/3`, with equality at `λ = 1/3`.
Chen and Hou use it for `λ ∈ [0, 1]` (Supplementary material I, (8.73)). -/
theorem one_sub_mul_one_add_sq_le {l : ℝ} (hl : -5 / 3 ≤ l) :
    (1 - l) * (1 + l) ^ 2 ≤ 32 / 27 := by
  nlinarith [mul_nonneg (sq_nonneg (l - 1 / 3)) (by linarith : (0 : ℝ) ≤ l + 5 / 3)]

end Power

end HolderSpace
