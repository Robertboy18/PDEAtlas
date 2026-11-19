/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.PolynomialRemainder

/-!
# Tensor Lagrange interpolation on a cell

Chen and Hou, Part II, Supplementary Sec 8.2. With Lagrange cardinal functions `pᵢ` at nodes
`x₁, …, x_k` and `q_j` at `y₁, …, y_k'` (`(8.10)`, `Lagrange.basis`), a function on
`[a, b] × [c, d]` splits as `f = I + II`, `I = ∑ pᵢ(x) q_j(y) f(xᵢ, y_j)`,
`II = R₁(x, y) + ∑ᵢ pᵢ(x) R₂(xᵢ, y)` (8.11), with the one-dimensional remainders `R₁` in `x` and
`R₂` in `y` (8.12). The Lebesgue sums `Λₓ = ∑ |pᵢ(x)|`, `Λ_y = ∑ |q_j(y)|` amplify bounded data
(8.14): `|II| ≤ |R₁| + Λₓ max |R₂|` (`abs_sub_tensorLagrange_le`) and, for any centre `m`,
`|I| ≤ |m| + Λₓ Λ_y max |f(xᵢ, y_j) - m|` (`abs_tensor_weighted_le`); the midrange is the best
centre (8.15, `abs_sub_midrange_le`, in the upper-bound form that the proof uses). The
two-stage centring of (8.16) is `abs_tensor_weighted_le_of_centres`. The Lebesgue constants of
particular node sets and the nodal-product constant do not enter the statements.

## Main results

* `abs_sum_mul_le`: a weighted sum is at most the sum of the absolute weights times a bound of the
  values (8.14).
* `abs_sub_midrange_le`: every value is within half the range of the midrange (8.15).
* `abs_tensor_weighted_le`: for weights summing to one and any centre `m`,
  `|∑ᵢ ∑ⱼ pᵢ qⱼ aᵢⱼ| ≤ |m| + Λₓ Λ_y B` when `|aᵢⱼ - m| ≤ B`.
* `abs_tensor_weighted_le_of_centres`: the two-stage centring (8.16),
  `|∑ⱼ qⱼ ∑ᵢ pᵢ aᵢⱼ| ≤ |ā| + Λ_y B₁ + Λ_y Λₓ B₂`.
* `sum_eval_lagrangeBasis`: the cardinal functions at distinct nodes sum to one.
* `abs_sub_tensorLagrange_le`: the remainder `II` of the tensor interpolant (8.11)-(8.12).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II (in the same PDF), Section 8.2, (8.10)-(8.16).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

open Set Finset Polynomial

/-- **Supp II (8.14).** A weighted sum is at most the sum of the absolute weights times a bound
of the values. -/
theorem abs_sum_mul_le {ι : Type*} (s : Finset ι) (p c : ι → ℝ) {B : ℝ}
    (hc : ∀ i ∈ s, |c i| ≤ B) : |∑ i ∈ s, p i * c i| ≤ (∑ i ∈ s, |p i|) * B := by
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hc i hi) (abs_nonneg _)

/-- **Supp II (8.15).** Every value is within half the range of the midrange
`(max + min) / 2`. -/
theorem abs_sub_midrange_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (b : ι → ℝ) {i : ι}
    (hi : i ∈ s) : |b i - (s.sup' hs b + s.inf' hs b) / 2| ≤ (s.sup' hs b - s.inf' hs b) / 2 := by
  have h1 := le_sup' b hi
  have h2 := inf'_le b hi
  rw [abs_le]
  constructor <;> linarith

/-- **Supp II, the bound of `I` before (8.15).** For weights summing to one and any centre `m`,
`|∑ᵢ ∑ⱼ pᵢ qⱼ aᵢⱼ| ≤ |m| + Λₓ Λ_y B` when `|aᵢⱼ - m| ≤ B`. -/
theorem abs_tensor_weighted_le {ι κ : Type*} (s : Finset ι) (t : Finset κ) (p : ι → ℝ)
    (q : κ → ℝ) (hp : ∑ i ∈ s, p i = 1) (hq : ∑ j ∈ t, q j = 1) (a : ι → κ → ℝ) {m B : ℝ}
    (hB : ∀ i ∈ s, ∀ j ∈ t, |a i j - m| ≤ B) :
    |∑ i ∈ s, ∑ j ∈ t, p i * q j * a i j| ≤
      |m| + (∑ i ∈ s, |p i|) * (∑ j ∈ t, |q j|) * B := by
  have hcentre : ∀ i, ∑ j ∈ t, q j * (a i j - m) = ∑ j ∈ t, q j * a i j - m := by
    intro i
    rw [show ∑ j ∈ t, q j * (a i j - m) = ∑ j ∈ t, q j * a i j - (∑ j ∈ t, q j) * m by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun j _ ↦ by ring, hq, one_mul]
  have hid : ∑ i ∈ s, ∑ j ∈ t, p i * q j * a i j =
      m + ∑ i ∈ s, p i * ∑ j ∈ t, q j * (a i j - m) := by
    symm
    calc m + ∑ i ∈ s, p i * ∑ j ∈ t, q j * (a i j - m) =
          m + ∑ i ∈ s, (p i * ∑ j ∈ t, q j * a i j - p i * m) := by
          congr 1
          exact sum_congr rfl fun i _ ↦ by rw [hcentre i, mul_sub]
      _ = m + (∑ i ∈ s, p i * ∑ j ∈ t, q j * a i j - (∑ i ∈ s, p i) * m) := by
          rw [sum_sub_distrib, sum_mul]
      _ = ∑ i ∈ s, p i * ∑ j ∈ t, q j * a i j := by rw [hp]; ring
      _ = ∑ i ∈ s, ∑ j ∈ t, p i * q j * a i j :=
          sum_congr rfl fun i _ ↦ by rw [mul_sum]; exact sum_congr rfl fun j _ ↦ by ring
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  have hinner : ∀ i ∈ s, |∑ j ∈ t, q j * (a i j - m)| ≤ (∑ j ∈ t, |q j|) * B :=
    fun i hi ↦ abs_sum_mul_le t q _ fun j hj ↦ hB i hi j hj
  calc |∑ i ∈ s, p i * ∑ j ∈ t, q j * (a i j - m)| ≤
        (∑ i ∈ s, |p i|) * ((∑ j ∈ t, |q j|) * B) := abs_sum_mul_le s p _ hinner
    _ = _ := by ring

/-- **Supp II (8.16).** Centring first along each line and then across lines: with centres
`āⱼ` and `ā`, `|∑ⱼ qⱼ ∑ᵢ pᵢ aᵢⱼ| ≤ |ā| + Λ_y B₁ + Λ_y Λₓ B₂` when `|āⱼ - ā| ≤ B₁` and
`|aᵢⱼ - āⱼ| ≤ B₂`. With midranges, `B₁` and `B₂` are half the ranges, as in (8.16). -/
theorem abs_tensor_weighted_le_of_centres {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∑ i ∈ s, p i = 1) (hq : ∑ j ∈ t, q j = 1) (a : ι → κ → ℝ)
    (c : κ → ℝ) {m B₁ B₂ : ℝ} (hB₁ : ∀ j ∈ t, |c j - m| ≤ B₁)
    (hB₂ : ∀ i ∈ s, ∀ j ∈ t, |a i j - c j| ≤ B₂) :
    |∑ j ∈ t, q j * ∑ i ∈ s, p i * a i j| ≤
      |m| + (∑ j ∈ t, |q j|) * B₁ + (∑ j ∈ t, |q j|) * ((∑ i ∈ s, |p i|) * B₂) := by
  have e1 : ∀ j, ∑ i ∈ s, p i * (a i j - c j) = ∑ i ∈ s, p i * a i j - c j := by
    intro j
    rw [show ∑ i ∈ s, p i * (a i j - c j) = ∑ i ∈ s, p i * a i j - (∑ i ∈ s, p i) * c j by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ ↦ by ring, hp, one_mul]
  have e2 : ∑ j ∈ t, q j * (c j - m) = ∑ j ∈ t, q j * c j - m := by
    rw [show ∑ j ∈ t, q j * (c j - m) = ∑ j ∈ t, q j * c j - (∑ j ∈ t, q j) * m by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun j _ ↦ by ring, hq, one_mul]
  have hid : ∑ j ∈ t, q j * ∑ i ∈ s, p i * a i j =
      m + ∑ j ∈ t, q j * (c j - m) + ∑ j ∈ t, q j * ∑ i ∈ s, p i * (a i j - c j) := by
    have e3 : ∑ j ∈ t, q j * ∑ i ∈ s, p i * (a i j - c j) =
        ∑ j ∈ t, q j * ∑ i ∈ s, p i * a i j - ∑ j ∈ t, q j * c j := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ ↦ by rw [e1 j, mul_sub]
    rw [e2, e3]
    ring
  rw [hid]
  have h1 := abs_sum_mul_le t q _ hB₁
  have h2 := abs_sum_mul_le t q _ fun j hj ↦ abs_sum_mul_le s p _ fun i hi ↦ hB₂ i hi j hj
  calc _ ≤ |m + ∑ j ∈ t, q j * (c j - m)| + |∑ j ∈ t, q j * ∑ i ∈ s, p i * (a i j - c j)| :=
        abs_add_le _ _
    _ ≤ |m| + |∑ j ∈ t, q j * (c j - m)| + |∑ j ∈ t, q j * ∑ i ∈ s, p i * (a i j - c j)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by linarith

/-- The cardinal functions at distinct nodes sum to one. -/
theorem sum_eval_lagrangeBasis {k : ℕ} (xs : Fin (k + 1) → ℝ) (hxs : Function.Injective xs)
    (x : ℝ) : ∑ i, (Lagrange.basis univ xs i).eval x = 1 := by
  rw [← eval_finsetSum, Lagrange.sum_basis hxs.injOn univ_nonempty, eval_one]

/-- The Lagrange interpolant in cardinal form. -/
theorem eval_interpolate_eq_sum {k : ℕ} (xs : Fin (k + 1) → ℝ) (r : Fin (k + 1) → ℝ) (x : ℝ) :
    (Lagrange.interpolate univ xs r).eval x = ∑ i, r i * (Lagrange.basis univ xs i).eval x := by
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  simp [eval_mul, eval_C]

/-- **Supp II (8.11)-(8.12), the remainder `II`.** Interpolating `f` first in `x` at `k + 1`
distinct nodes of `[a, b]` and then each `f(xᵢ, ·)` in `y` at `k' + 1` distinct nodes of
`[c, d]`, the tensor interpolant differs from `f` by at most
`Lₓ / (k + 1)! |∏ᵢ (x - xᵢ)| + (∑ᵢ |pᵢ(x)|) L_y / (k' + 1)! |∏ⱼ (y - yⱼ)|`, for `L`-Lipschitz top
derivatives of the chains `Φx y` (in `x`, for each `y`) and `Φy x` (in `y`, for each `x`). -/
theorem abs_sub_tensorLagrange_le {k k' : ℕ} {a b c d Lx Ly : ℝ} (f : ℝ → ℝ → ℝ)
    (xs : Fin (k + 1) → ℝ) (ys : Fin (k' + 1) → ℝ) (hxs : Function.Injective xs)
    (hys : Function.Injective ys) (hxm : ∀ i, xs i ∈ Icc a b) (hym : ∀ j, ys j ∈ Icc c d)
    (Φx : ℝ → ℕ → ℝ → ℝ) (hΦx : ∀ y, Φx y 0 = fun x ↦ f x y)
    (hcontX : ∀ y ∈ Icc c d, ∀ j < k, ContinuousOn (Φx y j) (Icc a b))
    (hderivX : ∀ y ∈ Icc c d, ∀ j < k, ∀ z ∈ Ioo a b, HasDerivAt (Φx y j) (Φx y (j + 1) z) z)
    (hlipX : ∀ y ∈ Icc c d, ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
      |Φx y k u - Φx y k v| ≤ Lx * |u - v|)
    (Φy : ℝ → ℕ → ℝ → ℝ) (hΦy : ∀ x, Φy x 0 = f x)
    (hcontY : ∀ x ∈ Icc a b, ∀ j < k', ContinuousOn (Φy x j) (Icc c d))
    (hderivY : ∀ x ∈ Icc a b, ∀ j < k', ∀ z ∈ Ioo c d, HasDerivAt (Φy x j) (Φy x (j + 1) z) z)
    (hlipY : ∀ x ∈ Icc a b, ∀ u ∈ Icc c d, ∀ v ∈ Icc c d,
      |Φy x k' u - Φy x k' v| ≤ Ly * |u - v|)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d) :
    |f x y - ∑ i, ∑ j, (Lagrange.basis univ xs i).eval x * (Lagrange.basis univ ys j).eval y *
        f (xs i) (ys j)| ≤
      Lx / (k + 1).factorial * |∏ i, (x - xs i)| +
        (∑ i, |(Lagrange.basis univ xs i).eval x|) *
          (Ly / (k' + 1).factorial * |∏ j, (y - ys j)|) := by
  set p : Fin (k + 1) → ℝ := fun i ↦ (Lagrange.basis univ xs i).eval x
  set q : Fin (k' + 1) → ℝ := fun j ↦ (Lagrange.basis univ ys j).eval y
  -- `R₁` in `x` at height `y`
  have hR₁ := abs_sub_interpolate_le (Φx y) (hcontX y hy) (hderivX y hy) (hlipX y hy) xs hxs
    hxm hx
  simp only [hΦx, eval_interpolate_eq_sum] at hR₁
  -- `R₂` in `y` at each node `xᵢ`
  have hR₂ : ∀ i, |f (xs i) y - ∑ j, f (xs i) (ys j) * q j| ≤
      Ly / (k' + 1).factorial * |∏ j, (y - ys j)| := by
    intro i
    have h := abs_sub_interpolate_le (Φy (xs i)) (hcontY _ (hxm i)) (hderivY _ (hxm i))
      (hlipY _ (hxm i)) ys hys hym hy
    simpa only [hΦy, eval_interpolate_eq_sum] using h
  have hid : f x y - ∑ i, ∑ j, p i * q j * f (xs i) (ys j) =
      (f x y - ∑ i, f (xs i) y * p i) + ∑ i, p i * (f (xs i) y - ∑ j, f (xs i) (ys j) * q j) := by
    have : ∑ i, p i * (f (xs i) y - ∑ j, f (xs i) (ys j) * q j) =
        ∑ i, f (xs i) y * p i - ∑ i, ∑ j, p i * q j * f (xs i) (ys j) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [mul_sub, mul_sum, mul_comm (p i) (f (xs i) y)]
      congr 1
      refine sum_congr rfl fun j _ ↦ ?_
      ring
    rw [this]
    ring
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add hR₁ ?_)
  exact abs_sum_mul_le univ p _ fun i _ ↦ hR₂ i

end PDE.Analysis.Approximation
