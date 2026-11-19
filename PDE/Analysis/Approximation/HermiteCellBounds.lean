/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.HermiteSlopeBounds
public import PDE.Analysis.Approximation.LinearInterpolation

/-!
# Hermite interpolation on a rectangular cell

Chen and Hou, Part II, Supplementary Sec 8.4. On `[x₀, x₁] × [y₀, y₁]` with `h₁ = x₁ - x₀`,
`t = (x - x₀) / h₁`, the Hermite interpolant in `x` at height `y` is
`H₄(x, y) = f(x₀, y)(1 - t) + f(x₁, y) t + t²(t - 1) M₁(y) + (t - 1)² t M₀(y)` with
`Mᵢ(y) = h₁ ∂ₓ f(xᵢ, y) - (f(x₁, y) - f(x₀, y))` ((8.38), (8.42)). Interpolating the coefficients in
`y` (Hermite for `f(xᵢ, ·)`, linear or quadratic for `Mᵢ`) gives a polynomial
`P(x, y) = A₀(y)(1 - t) + A₁(y) t + t²(t - 1) q₁(y) + t (t - 1)² q₀(y)` (`hermiteCell`, (8.47),
(8.61)). The coefficient errors are small because `Mᵢ` is a second difference in `x`, so
`∂_y^k Mᵢ` is `O(h₁²)` times a mixed derivative.

The fourth-order estimate of Supp II Sec 8.4.3,
`|P₄ - f| ≤ (h₁⁴ ‖∂ₓ⁴f‖ + h₂⁴ ‖∂_y⁴f‖) / 384 + h₁² h₂² ‖∂ₓ²∂_y²f‖ / 64`, is the combination of
`abs_sub_hermiteCell_le` with the one-dimensional bounds `abs_sub_hermiteCubic_le_left` (in `x` and
in `y`), the linear interpolation bound `h₂²/8` for `Mᵢ - qᵢ` and `abs_mul_deriv_sub_sub_le`
for `∂_y² Mᵢ` (`abs_sub_hermiteCell_le_of_chains`, with the bound `K` of `∂_y² Mᵢ` left as a
hypothesis; `K = h₁² ‖∂ₓ²∂_y²f‖ / 2` by (8.45) gives the constant `h₁² h₂² / 64` of
Sec 8.4.3).

## Main definitions

* `hermiteCell`: the cell interpolant `A₀(1 - t) + A₁ t + t²(t - 1) q₁ + t (t - 1)² q₀`.

## Main results

* `abs_sub_hermiteCell_le`:
  `|f - P| ≤ |f - H₄| + max_i |f(xᵢ, y) - Aᵢ(y)| + ¼ max_i |Mᵢ(y) - qᵢ(y)|`, since
  `|t²(t - 1)| + |t (t - 1)²| = t (1 - t) ≤ 1/4`.
* `abs_hermiteCell_le`: `|P| ≤ max_i |Aᵢ| + (4/27) max(|q₁ - q₀|, |q₀|, |q₁|)` (8.49)-(8.50).
* `abs_sub_hermiteCell_le_of_quartic`: for the fifth-order interpolant `H₅` in `x` (with the value
  at `x₂ = x₀ + 2h₁`), `|f - P| ≤ |f - H₅| + |f(x₂, y) - H₄(x₂, y)| / 64 +
  max_i |f(xᵢ, y) - Aᵢ(y)| + ¼ max_i |Mᵢ(y) - qᵢ(y)|` (8.48).
* `abs_le_max_add_half_mul`: if `g` is continuous on `[a, b]` and differentiable on `(a, b)`
  with `|g'| ≤ K` there, then `|g| ≤ max(|g a|, |g b|) + K (b - a) / 2` on `[a, b]`, the
  first-order endpoint bound behind (8.46); it bounds the middle term of (8.48) on `[y₀, y₁]`.
* `abs_mul_deriv_sub_sub_le`: `|(b - a) g'(c) - (g(b) - g(a))| ≤ L (b - a)² / 2` at an endpoint
  `c` for `L`-Lipschitz `g'` (8.45).
* `abs_sub_hermiteCell_le_of_chains`: the fourth-order cell estimate of Sec 8.4.3, with the bound
  of `∂_y² Mᵢ` as a hypothesis.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Supplementary
  material II (in the same PDF), Section 8.4.1, (8.38)-(8.50), and Section 8.4.3, (8.61)-(8.63).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis.Approximation

open Set Polynomial

/-- The cell interpolant `A₀(1 - t) + A₁ t + t²(t - 1) q₁ + t (t - 1)² q₀`. -/
def hermiteCell (A₀ A₁ q₀ q₁ t : ℝ) : ℝ :=
  A₀ * (1 - t) + A₁ * t + t ^ 2 * (t - 1) * q₁ + t * (t - 1) ^ 2 * q₀

/-- The cubic Hermite interpolant in `x` is the cell interpolant with the exact coefficients. -/
theorem hermiteCubic_eq_hermiteCell (l₀ l₁ m₀ m₁ t : ℝ) :
    hermiteCubic l₀ l₁ m₀ m₁ t = hermiteCell l₀ l₁ (m₀ - (l₁ - l₀)) (m₁ - (l₁ - l₀)) t := by
  unfold hermiteCubic hermiteCell
  ring

/-- **Supp II (8.47)-(8.48), (8.61)-(8.63), assembly.** For `t ∈ [0, 1]`, two cell interpolants
differ by at most the largest difference of the values plus a quarter of the largest difference
of the bubble coefficients. -/
theorem abs_hermiteCell_sub_le {A₀ A₁ q₀ q₁ B₀ B₁ r₀ r₁ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |hermiteCell A₀ A₁ q₀ q₁ t - hermiteCell B₀ B₁ r₀ r₁ t| ≤
      max |A₀ - B₀| |A₁ - B₁| + max |q₀ - r₀| |q₁ - r₁| / 4 := by
  obtain ⟨h0, h1⟩ := ht
  have hid : hermiteCell A₀ A₁ q₀ q₁ t - hermiteCell B₀ B₁ r₀ r₁ t =
      ((A₀ - B₀) + t * ((A₁ - B₁) - (A₀ - B₀))) +
        (t ^ 2 * (t - 1) * (q₁ - r₁) + t * (t - 1) ^ 2 * (q₀ - r₀)) := by
    unfold hermiteCell
    ring
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add (abs_lerp_le ⟨h0, h1⟩) ?_)
  set D := max |q₀ - r₀| |q₁ - r₁|
  have hD₀ : |q₀ - r₀| ≤ D := le_max_left _ _
  have hD₁ : |q₁ - r₁| ≤ D := le_max_right _ _
  have ha : |t ^ 2 * (t - 1)| = t ^ 2 * (1 - t) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg t), abs_of_nonpos (by linarith)]
    ring
  have hb : |t * (t - 1) ^ 2| = t * (1 - t) ^ 2 := by
    rw [abs_mul, abs_of_nonneg h0, abs_of_nonneg (sq_nonneg _)]
    ring
  calc |t ^ 2 * (t - 1) * (q₁ - r₁) + t * (t - 1) ^ 2 * (q₀ - r₀)| ≤
        t ^ 2 * (1 - t) * D + t * (1 - t) ^ 2 * D := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul (t ^ 2 * (t - 1)), abs_mul (t * (t - 1) ^ 2), ha, hb]
        exact add_le_add (mul_le_mul_of_nonneg_left hD₁ (by nlinarith))
          (mul_le_mul_of_nonneg_left hD₀ (by nlinarith))
    _ = t * (1 - t) * D := by ring
    _ ≤ 1 / 4 * D := by
        have hD : 0 ≤ D := (abs_nonneg _).trans hD₀
        nlinarith [sq_nonneg (t - 1 / 2)]
    _ = D / 4 := by ring

/-- **Supp II, the error of the cell interpolant.** If `f` differs from its Hermite interpolant
in `x` by at most `Eₓ`, the values `f(xᵢ, y)` from `Aᵢ` by at most `E_A` and the coefficients
`Mᵢ` from `qᵢ` by at most `E_M`, then `|f - P| ≤ Eₓ + E_A + E_M / 4`. -/
theorem abs_sub_hermiteCell_le {F l₀ l₁ m₀ m₁ A₀ A₁ q₀ q₁ t Ex EA EM : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hx : |F - hermiteCubic l₀ l₁ m₀ m₁ t| ≤ Ex)
    (hA₀ : |l₀ - A₀| ≤ EA) (hA₁ : |l₁ - A₁| ≤ EA)
    (hM₀ : |m₀ - (l₁ - l₀) - q₀| ≤ EM) (hM₁ : |m₁ - (l₁ - l₀) - q₁| ≤ EM) :
    |F - hermiteCell A₀ A₁ q₀ q₁ t| ≤ Ex + EA + EM / 4 := by
  have h := abs_hermiteCell_sub_le (A₀ := l₀) (A₁ := l₁) (q₀ := m₀ - (l₁ - l₀))
    (q₁ := m₁ - (l₁ - l₀)) (B₀ := A₀) (B₁ := A₁) (r₀ := q₀) (r₁ := q₁) ht
  rw [← hermiteCubic_eq_hermiteCell] at h
  have h1 : max |l₀ - A₀| |l₁ - A₁| ≤ EA := max_le hA₀ hA₁
  have h2 : max |m₀ - (l₁ - l₀) - q₀| |m₁ - (l₁ - l₀) - q₁| ≤ EM := max_le hM₀ hM₁
  calc |F - hermiteCell A₀ A₁ q₀ q₁ t| ≤ |F - hermiteCubic l₀ l₁ m₀ m₁ t| +
        |hermiteCubic l₀ l₁ m₀ m₁ t - hermiteCell A₀ A₁ q₀ q₁ t| := abs_sub_le _ _ _
    _ ≤ Ex + (EA + EM / 4) := add_le_add hx (h.trans (by linarith))
    _ = Ex + EA + EM / 4 := by ring

/-- **Supp II (8.49)-(8.50).** On `[0, 1]`,
`|P| ≤ max(|A₀|, |A₁|) + (4/27) max(|q₁ - q₀|, |q₁|, |q₀|)`. -/
theorem abs_hermiteCell_le {A₀ A₁ q₀ q₁ t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |hermiteCell A₀ A₁ q₀ q₁ t| ≤
      max |A₀| |A₁| + 4 / 27 * max (max |q₁ - q₀| |q₁|) |q₀| := by
  have h := abs_hermiteCubic_le (l₀ := 0) (l₁ := 0) (m₀ := q₀) (m₁ := q₁) ht
  have hid : hermiteCell A₀ A₁ q₀ q₁ t =
      (A₀ + t * (A₁ - A₀)) + hermiteCubic 0 0 q₀ q₁ t := by
    unfold hermiteCell hermiteCubic
    ring
  rw [hid]
  refine (abs_add_le _ _).trans (add_le_add (abs_lerp_le ht) ?_)
  simpa [hermiteCubicBound] using h

/-- **Supp II (8.45).** For `g` with an `L`-Lipschitz derivative on `[a, b]`, the derivative at an
endpoint `c ∈ {a, b}` matches the slope: `|(b - a) g'(c) - (g(b) - g(a))| ≤ L (b - a)² / 2`. -/
theorem abs_mul_deriv_sub_sub_le {g g' : ℝ → ℝ} {a b c L : ℝ} (hab : a < b)
    (hcont : ContinuousOn g (Icc a b)) (hderiv : ∀ z ∈ Ioo a b, HasDerivAt g (g' z) z)
    (hlip : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |g' x - g' y| ≤ L * |x - y|) (hc : c = a ∨ c = b) :
    |(b - a) * g' c - (g b - g a)| ≤ L * (b - a) ^ 2 / 2 := by
  set Φ : ℕ → ℝ → ℝ := fun k ↦ if k = 0 then g else g'
  have hΦc : ∀ k < 1, ContinuousOn (Φ k) (Icc a b) := fun k hk ↦ by
    obtain rfl : k = 0 := by omega
    simpa [Φ] using hcont
  have hΦd : ∀ k < 1, ∀ z ∈ Ioo a b, HasDerivAt (Φ k) (Φ (k + 1) z) z := fun k hk z hz ↦ by
    obtain rfl : k = 0 := by omega
    simpa [Φ] using hderiv z hz
  have hΦl : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |Φ 1 x - Φ 1 y| ≤ L * |x - y| := by
    simpa [Φ] using hlip
  have hcm : c ∈ Icc a b := by rcases hc with rfl | rfl <;> constructor <;> linarith
  -- the tangent line at `c` agrees with `g` to first order at the double node `c`
  have hrem := fun (x : ℝ) (hx : x ∈ Icc a b) ↦ abs_sub_eval_le_of_lipschitz (n := 1) Φ hΦc hΦd hΦl
    (C (g c) + C (g' c) * (X - C c)) (by compute_degree) (c ::ₘ c ::ₘ 0) (by simp)
    (fun z hz ↦ by simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hz
                   rcases hz with rfl | rfl <;> exact hcm)
    (fun z hz k hk ↦ by
      simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false, or_self] at hz
      subst hz
      rw [Multiset.count_cons_self, Multiset.count_cons_self, Multiset.count_zero] at hk
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · simp [Φ]
      · simp [Φ]) hx
  have hprod : ∀ x, ((c ::ₘ c ::ₘ 0).map fun z ↦ x - z).prod = (x - c) ^ 2 := fun x ↦ by
    simp only [Multiset.map_cons, Multiset.map_zero, Multiset.prod_cons, Multiset.prod_zero]
    ring
  have h2 : ((1 + 1).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rcases hc with rfl | rfl
  · have := hrem b ⟨hab.le, le_rfl⟩
    simp only [Φ, ↓reduceIte, eval_add, eval_C, eval_mul, eval_sub, eval_X, hprod, h2] at this
    rw [abs_of_nonneg (sq_nonneg (b - c))] at this
    rw [abs_sub_comm]
    calc |g b - g c - (b - c) * g' c| = |g b - (g c + g' c * (b - c))| := by
          congr 1
          ring
      _ ≤ L / 2 * (b - c) ^ 2 := this
      _ = L * (b - c) ^ 2 / 2 := by ring
  · have := hrem a ⟨le_rfl, hab.le⟩
    simp only [Φ, ↓reduceIte, eval_add, eval_C, eval_mul, eval_sub, eval_X, hprod, h2] at this
    rw [abs_of_nonneg (sq_nonneg (a - c))] at this
    calc |(c - a) * g' c - (g c - g a)| = |g a - (g c + g' c * (a - c))| := by
          congr 1
          ring
      _ ≤ L / 2 * (a - c) ^ 2 := this
      _ = L * (c - a) ^ 2 / 2 := by ring

/-- **Supp II Sec 8.4.3, the fourth-order cell estimate.** Let `f` on
`[x₀, x₀ + h₁] × [y₀, y₀ + h₂]` have, for each `y`, a derivative chain in `x` of order `3` with
`Lₓ`-Lipschitz top derivative, and
at `x₀`, `x₁ = x₀ + h₁` a derivative chain in `y` of order `3` with `L_y`-Lipschitz top derivative;
let `Mᵢ(y) = h₁ ∂ₓf(xᵢ, y) - (f(x₁, y) - f(x₀, y))` have second derivative at most `K`. With
`Aᵢ` the Hermite interpolant of `f(xᵢ, ·)` in `y` and `λᵢ` the linear interpolant of `Mᵢ`,
`|f - P₄| ≤ Lₓ h₁⁴ / 384 + L_y h₂⁴ / 384 + K h₂² / 32`. -/
theorem abs_sub_hermiteCell_le_of_chains {x₀ y₀ h₁ h₂ Lx Ly K : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (Φx : ℝ → ℕ → ℝ → ℝ) (Φy : ℝ → ℕ → ℝ → ℝ) (hxy : ∀ y u, Φx y 0 u = Φy u 0 y)
    (hcx : ∀ y ∈ Icc y₀ (y₀ + h₂), ∀ j < 3, ContinuousOn (Φx y j) (Icc x₀ (x₀ + h₁)))
    (hdx : ∀ y ∈ Icc y₀ (y₀ + h₂), ∀ j < 3, ∀ z ∈ Ioo x₀ (x₀ + h₁),
      HasDerivAt (Φx y j) (Φx y (j + 1) z) z)
    (hlx : ∀ y ∈ Icc y₀ (y₀ + h₂), ∀ u ∈ Icc x₀ (x₀ + h₁), ∀ v ∈ Icc x₀ (x₀ + h₁),
      |Φx y 3 u - Φx y 3 v| ≤ Lx * |u - v|)
    (hcy : ∀ u ∈ ({x₀, x₀ + h₁} : Set ℝ), ∀ j < 3, ContinuousOn (Φy u j) (Icc y₀ (y₀ + h₂)))
    (hdy : ∀ u ∈ ({x₀, x₀ + h₁} : Set ℝ), ∀ j < 3, ∀ z ∈ Ioo y₀ (y₀ + h₂),
      HasDerivAt (Φy u j) (Φy u (j + 1) z) z)
    (hly : ∀ u ∈ ({x₀, x₀ + h₁} : Set ℝ), ∀ v ∈ Icc y₀ (y₀ + h₂), ∀ w ∈ Icc y₀ (y₀ + h₂),
      |Φy u 3 v - Φy u 3 w| ≤ Ly * |v - w|)
    (M M' M'' : Fin 2 → ℝ → ℝ)
    (hM : ∀ i y, M i y = h₁ * Φx y 1 (x₀ + i * h₁) - (Φx y 0 (x₀ + h₁) - Φx y 0 x₀))
    (hMc : ∀ i, ContinuousOn (M i) (Icc y₀ (y₀ + h₂)))
    (hMd : ∀ i, ∀ z ∈ Ioo y₀ (y₀ + h₂), HasDerivAt (M i) (M' i z) z)
    (hMd' : ∀ i, ∀ z ∈ Ioo y₀ (y₀ + h₂), HasDerivAt (M' i) (M'' i z) z)
    (hK : ∀ i, ∀ z ∈ Ioo y₀ (y₀ + h₂), |M'' i z| ≤ K)
    {x y : ℝ} (hx : x ∈ Icc x₀ (x₀ + h₁)) (hy : y ∈ Icc y₀ (y₀ + h₂)) :
    |Φx y 0 x - hermiteCell
        (hermiteCubic (Φy x₀ 0 y₀) (Φy x₀ 0 (y₀ + h₂)) (h₂ * Φy x₀ 1 y₀)
          (h₂ * Φy x₀ 1 (y₀ + h₂)) ((y - y₀) / h₂))
        (hermiteCubic (Φy (x₀ + h₁) 0 y₀) (Φy (x₀ + h₁) 0 (y₀ + h₂)) (h₂ * Φy (x₀ + h₁) 1 y₀)
          (h₂ * Φy (x₀ + h₁) 1 (y₀ + h₂)) ((y - y₀) / h₂))
        (linearInterpolant y₀ (y₀ + h₂) (M 0 y₀) (M 0 (y₀ + h₂)) y)
        (linearInterpolant y₀ (y₀ + h₂) (M 1 y₀) (M 1 (y₀ + h₂)) y) ((x - x₀) / h₁)| ≤
      Lx * h₁ ^ 4 / 384 + Ly * h₂ ^ 4 / 384 + K * h₂ ^ 2 / 32 := by
  have hm₀ : x₀ ∈ ({x₀, x₀ + h₁} : Set ℝ) := by simp
  have hm₁ : x₀ + h₁ ∈ ({x₀, x₀ + h₁} : Set ℝ) := by simp
  -- the Hermite interpolant in `x` at height `y`
  have hEx := abs_sub_hermiteCubic_le_left hh₁ (Φx y) (hcx y hy) (hdx y hy) (hlx y hy) hx
  -- the Hermite interpolants of `f(xᵢ, ·)` in `y`
  have hA (u : ℝ) (hu : u ∈ ({x₀, x₀ + h₁} : Set ℝ)) :=
    abs_sub_hermiteCubic_le_left hh₂ (Φy u) (hcy u hu) (hdy u hu) (hly u hu) hy
  -- the linear interpolants of the `Mᵢ`
  have hMl (i : Fin 2) : |M i y - linearInterpolant y₀ (y₀ + h₂) (M i y₀) (M i (y₀ + h₂)) y| ≤
      K * h₂ ^ 2 / 8 := by
    have := abs_sub_linearInterpolant_le_uniform (by linarith : y₀ < y₀ + h₂) (hMc i)
      (hMd i) (hMd' i) (hK i) hy
    simpa using this
  have hl₀ := hMl 0
  have hl₁ := hMl 1
  rw [hM 0 y] at hl₀
  rw [hM 1 y] at hl₁
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_mul,
    add_zero, one_mul] at hl₀ hl₁
  have ht := unitInterval.div_mem (sub_nonneg.2 hx.1) hh₁.le (sub_le_iff_le_add'.2 hx.2)
  refine (abs_sub_hermiteCell_le (EA := Ly * h₂ ^ 4 / 384) (EM := K * h₂ ^ 2 / 8) ht hEx
    ?_ ?_ hl₀ hl₁).trans (le_of_eq (by ring))
  · rw [hxy]
    exact hA x₀ hm₀
  · rw [hxy]
    exact hA (x₀ + h₁) hm₁

/-- **Supp II (8.48).** With the quartic interpolant in `x`, the cell interpolant has error at most
`E₅ + |l₂ - G₄(2)| / 64 + E_A + E_M / 4`. -/
theorem abs_sub_hermiteCell_le_of_quartic {F l₀ l₁ l₂ m₀ m₁ A₀ A₁ q₀ q₁ t E5 EA EM : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (h5 : |F - hermiteQuartic l₀ l₁ l₂ m₀ m₁ t| ≤ E5)
    (hA₀ : |l₀ - A₀| ≤ EA) (hA₁ : |l₁ - A₁| ≤ EA)
    (hM₀ : |m₀ - (l₁ - l₀) - q₀| ≤ EM) (hM₁ : |m₁ - (l₁ - l₀) - q₁| ≤ EM) :
    |F - hermiteCell A₀ A₁ q₀ q₁ t| ≤
      E5 + |l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2| / 64 + EA + EM / 4 := by
  have h4 := abs_sub_hermiteCell_le (F := hermiteCubic l₀ l₁ m₀ m₁ t) (Ex := 0) ht
    (by simp) hA₀ hA₁ hM₀ hM₁
  have h54 : |hermiteQuartic l₀ l₁ l₂ m₀ m₁ t - hermiteCubic l₀ l₁ m₀ m₁ t| ≤
      |l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2| / 64 := by
    have h := abs_hermiteQuartic_le (l₀ := 0) (l₁ := 0) (l₂ := l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2)
      (m₀ := 0) (m₁ := 0) ht
    have e1 : hermiteQuartic 0 0 (l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2) 0 0 t =
        hermiteQuartic l₀ l₁ l₂ m₀ m₁ t - hermiteCubic l₀ l₁ m₀ m₁ t := by
      simp only [hermiteQuartic, hermiteCubic]
      ring
    have e2 : hermiteCubic 0 0 0 0 t = 0 := by simp [hermiteCubic]
    have e3 : hermiteCubic 0 0 0 0 2 = 0 := by simp [hermiteCubic]
    rw [e1, e2, e3, abs_zero, zero_add, sub_zero] at h
    exact h
  calc |F - hermiteCell A₀ A₁ q₀ q₁ t| ≤ |F - hermiteQuartic l₀ l₁ l₂ m₀ m₁ t| +
        |hermiteQuartic l₀ l₁ l₂ m₀ m₁ t - hermiteCubic l₀ l₁ m₀ m₁ t| +
        |hermiteCubic l₀ l₁ m₀ m₁ t - hermiteCell A₀ A₁ q₀ q₁ t| := by
        have := abs_sub_le (F) (hermiteQuartic l₀ l₁ l₂ m₀ m₁ t) (hermiteCell A₀ A₁ q₀ q₁ t)
        have := abs_sub_le (hermiteQuartic l₀ l₁ l₂ m₀ m₁ t) (hermiteCubic l₀ l₁ m₀ m₁ t)
          (hermiteCell A₀ A₁ q₀ q₁ t)
        linarith
    _ ≤ E5 + |l₂ - hermiteCubic l₀ l₁ m₀ m₁ 2| / 64 + (0 + EA + EM / 4) := by gcongr
    _ = _ := by ring

/-- **The first-order endpoint bound (Supp II (8.46)).** If `g` is continuous on `[a, b]` and
has derivative `g'` on `(a, b)` with `|g'| ≤ K` there, then on `[a, b]`,
`|g| ≤ max(|g a|, |g b|) + K (b - a) / 2`. -/
theorem abs_le_max_add_half_mul {g g' : ℝ → ℝ} {a b K : ℝ} (hcont : ContinuousOn g (Icc a b))
    (hderiv : ∀ z ∈ Ioo a b, HasDerivAt g (g' z) z) (hK : ∀ z ∈ Ioo a b, |g' z| ≤ K)
    {y : ℝ} (hy : y ∈ Icc a b) : |g y| ≤ max |g a| |g b| + K * (b - a) / 2 := by
  have hab : a ≤ b := hy.1.trans hy.2
  rcases hab.eq_or_lt with hab' | hab'
  · have hya : y = a := le_antisymm (hab' ▸ hy.2) hy.1
    subst hya
    rw [← hab', sub_self, mul_zero, zero_div, add_zero]
    exact le_max_left _ _
  have hKnn : 0 ≤ K := (abs_nonneg _).trans (hK ((a + b) / 2) ⟨by linarith, by linarith⟩)
  have hlip := lipschitz_of_abs_deriv_le hcont hderiv hK
  rcases le_total (y - a) (b - y) with h | h
  · have := hlip y hy a ⟨le_rfl, hab⟩
    have hK0 : 0 ≤ K * |y - a| := le_trans (abs_nonneg _) this
    rw [abs_of_nonneg (by linarith [hy.1] : 0 ≤ y - a)] at this hK0
    have hm := le_max_left |g a| |g b|
    have : |g y| ≤ |g a| + K * (y - a) := by
      have := abs_sub_abs_le_abs_sub (g y) (g a)
      linarith
    have hK' : K * (y - a) ≤ K * (b - a) / 2 := by nlinarith
    linarith
  · have := hlip y hy b ⟨hab, le_rfl⟩
    have hK0 : 0 ≤ K * |y - b| := le_trans (abs_nonneg _) this
    rw [abs_of_nonpos (by linarith [hy.2] : y - b ≤ 0)] at this hK0
    have hm := le_max_right |g a| |g b|
    have : |g y| ≤ |g b| + K * -(y - b) := by
      have := abs_sub_abs_le_abs_sub (g y) (g b)
      linarith
    have hK' : K * -(y - b) ≤ K * (b - a) / 2 := by nlinarith
    linarith

end PDE.Analysis.Approximation
