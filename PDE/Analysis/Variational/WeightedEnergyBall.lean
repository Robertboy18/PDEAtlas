/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Variational.ValidatedNonlinear
import PDE.Analysis.Evolution.Galerkin.Restriction

/-!
# Validated transport solutions in a weighted energy ball

A semi-implicit transport iteration has coercivity `a ‖u‖² + b ‖∇u‖²`, a residual of size `ε`
and a quadratic load of size `M ‖u‖²`, all measured in the value norm. We find one ball of the
weighted energy `η ‖u‖² + ‖∇u‖²` that the iteration maps to itself, so the fixed-point theorem
gives a solution in it, and we bound what such a solution satisfies beyond the radius of the
ball. Everything holds in every Hilbert space, for all forms and all constants. The continuity
constant and the transport constant may depend on the domain, and nothing here bounds them.

## Main results

* `weightedEnergyBall`, with `convex_weightedEnergyBall`, `isClosed_weightedEnergyBall` and
  `norm_le_of_mem_weightedEnergyBall`: the ball, and what the fixed-point theorem needs of it.
* `weighted_energy_le_of_budget`: the scalar invariance step.
* `exists_solution_of_weighted_energy_transport`: a solution in the weighted energy ball, and
  `exists_solution_of_weighted_energy_transport_on_submodule`, the same in a closed subspace.
* `add_le_of_quadratic_constraint`: the support function of the ellipse
  `a x² + b y² - c x y ≤ ε x`, and `add_le_of_isSolution_of_split_energy`, the bound it gives at
  a solution.
* `weighted_energy_le_of_quadratic_constraint`, `weighted_energy_lt_of_capacity`: the weighted
  energy on that ellipse, and a strict bound from a capacity condition.
* `mul_add_mul_le_of_weighted_energy_le`, `weighted_energy_le_of_forall_mul_add_mul_le`: a
  weighted energy ball and its support function `r √(p² / η + q²)` determine each other.

## How it works

Test the iteration with its output `u`. Transport cancels, so
`a ‖u‖² + b ‖∇u‖² ≤ (ε + M ‖w‖²) ‖u‖` for the input `w`. If `η b ≤ a`, the left side is at least
`b (η ‖u‖² + ‖∇u‖²)`, and `‖u‖ ≤ η^{-1/2} (η ‖u‖² + ‖∇u‖²)^{1/2}` on the right. So the ball of
radius `r` is invariant as soon as `ε + (M / η) r² ≤ b √η r`. The ball is closed, convex and
bounded, and `exists_solution_of_transport_cancellation_on` gives a solution in it.
`exists_solution_of_split_energy_transport` is the same argument on a box with separate radii
for `‖u‖` and `‖∇u‖`.

At a solution one can do better than the ball. If the load at the solution, tested with the
solution, is at most `c ‖u‖ ‖∇u‖`, then `a ‖u‖² + b ‖∇u‖² - c ‖u‖ ‖∇u‖ ≤ ε ‖u‖`. For
`4 a b > c²` this confines `(‖u‖, ‖∇u‖)` to an ellipse through the origin, and every linear
combination `p ‖u‖ + q ‖∇u‖` is at most the support function of that ellipse.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 4.3: the a priori
  estimate (4.30), Assumption 6 with (4.34) and (4.35), and the refined bounds (4.42) and
  (4.43); Section 4.4: Assumption 7 with (4.59) and (4.62). <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Variational

section Scalars

/-- **The invariance step of a weighted energy ball** (Hou, Wang and Yang, the estimate after
(4.35)). If `a x² + b y² ≤ (ε + M m²) x` with `η b ≤ a`, the input satisfies `η m² ≤ r²`, and
`ε + (M / η) r² ≤ b √η r`, then `η x² + y² ≤ r²`. -/
theorem weighted_energy_le_of_budget {a b η r ε M x y m : ℝ} (hb : 0 < b) (hη : 0 < η)
    (hηb : η * b ≤ a) (hr : 0 ≤ r) (hx : 0 ≤ x) (hM : 0 ≤ M) (hm : η * m ^ 2 ≤ r ^ 2)
    (hbudget : ε + M / η * r ^ 2 ≤ b * √η * r)
    (henergy : a * x ^ 2 + b * y ^ 2 ≤ (ε + M * m ^ 2) * x) :
    η * x ^ 2 + y ^ 2 ≤ r ^ 2 := by
  set n := √(η * x ^ 2 + y ^ 2) with hn
  have hn0 : 0 ≤ η * x ^ 2 + y ^ 2 := by positivity
  have hnsq : n ^ 2 = η * x ^ 2 + y ^ 2 := Real.sq_sqrt hn0
  have hxn : √η * x ≤ n := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [mul_pow, Real.sq_sqrt hη.le]
    linarith [sq_nonneg y]
  have hMm : M * m ^ 2 ≤ M / η * r ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hη]
    nlinarith
  -- `b n² ≤ (ε + (M / η) r²) x ≤ b √η r x ≤ b r n`.
  have hkey : b * n ^ 2 ≤ b * r * n := by
    calc
      b * n ^ 2 ≤ a * x ^ 2 + b * y ^ 2 := by
        rw [hnsq]
        nlinarith [sq_nonneg x]
      _ ≤ (ε + M * m ^ 2) * x := henergy
      _ ≤ (b * √η * r) * x := mul_le_mul_of_nonneg_right (by linarith) hx
      _ = b * r * (√η * x) := by ring
      _ ≤ b * r * n := mul_le_mul_of_nonneg_left hxn (by positivity)
  have hnr : n ≤ r := by
    rcases (Real.sqrt_nonneg (η * x ^ 2 + y ^ 2)).eq_or_lt with h0 | hpos
    · rw [hn, ← h0]
      exact hr
    · have : n * n ≤ r * n := by
        have h := (mul_le_mul_iff_of_pos_left hb).mp (by linarith : b * (n * n) ≤ b * (r * n))
        exact h
      exact le_of_mul_le_mul_right this hpos
  rw [← hnsq]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hnr 2

/-- **The support function of an ellipse through the origin** (Hou, Wang and Yang, (4.43)). If
`a x² + b y² - c x y ≤ ε x` with `b > 0` and `c² < 4 a b`, then for all `p`, `q`

`p x + q y ≤ 2 ε / (4 a b - c²) (b p + c q / 2 + √(b (b p² + c p q + a q²)))`.

The constraint is `(z - z₀)ᵀ A (z - z₀) ≤ ε² b / (4 a b - c²)` for the centre
`z₀ = (2 ε b, ε c) / (4 a b - c²)`, and the Cauchy–Schwarz inequality of the form `A` bounds
`p (x - x₀) + q (y - y₀)`. The bound is the value of the supremum, so nothing is lost. -/
theorem add_le_of_quadratic_constraint {a b c ε p q x y : ℝ} (hb : 0 < b)
    (hD : c ^ 2 < 4 * a * b) (hε : 0 ≤ ε)
    (h : a * x ^ 2 + b * y ^ 2 - c * x * y ≤ ε * x) :
    p * x + q * y ≤ 2 * ε / (4 * a * b - c ^ 2) *
      (b * p + c * q / 2 + √(b * (b * p ^ 2 + c * p * q + a * q ^ 2))) := by
  set D := 4 * a * b - c ^ 2 with hDdef
  have hDpos : 0 < D := by linarith
  set u := x - 2 * ε * b / D with hu
  set v := y - ε * c / D with hv
  set W := b * p ^ 2 + c * p * q + a * q ^ 2 with hWdef
  -- The constraint, centred.
  have hcon : a * u ^ 2 - c * u * v + b * v ^ 2 ≤ ε ^ 2 * b / D := by
    have hid : a * u ^ 2 - c * u * v + b * v ^ 2 =
        (a * x ^ 2 + b * y ^ 2 - c * x * y - ε * x) + ε ^ 2 * b / D := by
      simp only [hu, hv]
      field_simp
      simp only [hDdef]
      ring
    linarith
  -- The Cauchy–Schwarz inequality of the form, as an identity with a square.
  have hcs : (p * u + q * v) ^ 2 * D ≤ 4 * W * (a * u ^ 2 - c * u * v + b * v ^ 2) := by
    have hid : 4 * W * (a * u ^ 2 - c * u * v + b * v ^ 2) - (p * u + q * v) ^ 2 * D =
        (p * (2 * b * v - c * u) - q * (2 * a * u - c * v)) ^ 2 := by
      simp only [hDdef, hWdef]
      ring
    linarith [sq_nonneg (p * (2 * b * v - c * u) - q * (2 * a * u - c * v))]
  have hW : 0 ≤ W := by
    have hid : b * W = (b * p + c * q / 2) ^ 2 + D / 4 * q ^ 2 := by
      simp only [hDdef, hWdef]
      ring
    have : 0 ≤ b * W := by
      rw [hid]
      positivity
    exact nonneg_of_mul_nonneg_right this hb
  have hbW : 0 ≤ b * W := mul_nonneg hb.le hW
  have hs : 0 ≤ 2 * ε / D * √(b * W) := by positivity
  have hpuv : p * u + q * v ≤ 2 * ε / D * √(b * W) := by
    refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ hs)
    rw [mul_pow, Real.sq_sqrt hbW, div_pow]
    have h1 : (p * u + q * v) ^ 2 * D ≤ 4 * W * (ε ^ 2 * b / D) :=
      hcs.trans (mul_le_mul_of_nonneg_left hcon (by positivity))
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have h2 : (p * u + q * v) ^ 2 * D * D ≤ 4 * W * (ε ^ 2 * b / D) * D :=
      mul_le_mul_of_nonneg_right h1 hDpos.le
    have h3 : 4 * W * (ε ^ 2 * b / D) * D = 4 * W * (ε ^ 2 * b) := by
      field_simp
    nlinarith
  have hsplit : p * x + q * y = p * u + q * v + 2 * ε / D * (b * p + c * q / 2) := by
    simp only [hu, hv]
    field_simp
    ring
  have hexp : 2 * ε / D * (b * p + c * q / 2 + √(b * W)) =
      2 * ε / D * (b * p + c * q / 2) + 2 * ε / D * √(b * W) := by ring
  rw [hsplit, hexp]
  linarith

/-- **The weighted energy on an ellipse** (Hou, Wang and Yang, the estimate after (4.62)). Let
`a x² + b y² - c x y ≤ ε x` with `c ≥ 0`, `b > c / (2 √η)` and `a > η b`. Then

`η x² + y² ≤ ε² / (4 (a - η b) (b - c / (2 √η)))`.

One uses `2 √η |x| |y| ≤ η x² + y²` for the mixed term and completes the square in `x`. -/
theorem weighted_energy_le_of_quadratic_constraint {a b c η ε x y : ℝ} (hη : 0 < η)
    (hc : 0 ≤ c) (hb : c / (2 * √η) < b) (ha : η * b < a)
    (h : a * x ^ 2 + b * y ^ 2 - c * x * y ≤ ε * x) :
    η * x ^ 2 + y ^ 2 ≤ ε ^ 2 / (4 * (a - η * b) * (b - c / (2 * √η))) := by
  have hsη : 0 < √η := Real.sqrt_pos.mpr hη
  set β := b - c / (2 * √η) with hβ
  have hβpos : 0 < β := sub_pos.mpr hb
  have hα : 0 < a - η * b := sub_pos.mpr ha
  set n := η * x ^ 2 + y ^ 2 with hn
  -- The mixed term: `c x y ≤ c / (2 √η) (η x² + y²)`.
  have hmixed : c * x * y ≤ c / (2 * √η) * n := by
    have hsq : 2 * √η * (x * y) ≤ n := by
      have := sq_nonneg (√η * x - y)
      have hs := Real.sq_sqrt hη.le
      nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  -- Completing the square in `x`: `ε x - (a - η b) x² ≤ ε² / (4 (a - η b))`.
  have hquad : ε * x - (a - η * b) * x ^ 2 ≤ ε ^ 2 / (4 * (a - η * b)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * (a - η * b) * x - ε)]
  have hmain : β * n ≤ ε ^ 2 / (4 * (a - η * b)) := by
    have : β * n = a * x ^ 2 + b * y ^ 2 - c / (2 * √η) * n - (a - η * b) * x ^ 2 := by
      simp only [hβ, hn]
      ring
    linarith
  rw [le_div_iff₀ (by positivity)]
  have h1 : ε ^ 2 / (4 * (a - η * b)) * (4 * (a - η * b)) = ε ^ 2 := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_right hmain (by positivity : (0 : ℝ) ≤ 4 * (a - η * b))]

/-- **A strict weighted bound from a capacity condition** (Hou, Wang and Yang, Assumption 7 and
the estimate after (4.62)). Let `a x² + b y² - c x y ≤ ε x` with `c ≥ 0`. If

`b > c / (2 √η)`  and  `(a - η b) (b - c / (2 √η)) > ε² / (4 r²)`,

then `η x² + y² < r²`, by `weighted_energy_le_of_quadratic_constraint`. -/
theorem weighted_energy_lt_of_capacity {a b c η r ε x y : ℝ} (hη : 0 < η) (hr : 0 < r)
    (hc : 0 ≤ c) (hb : c / (2 * √η) < b)
    (hcap : ε ^ 2 / (4 * r ^ 2) < (a - η * b) * (b - c / (2 * √η)))
    (h : a * x ^ 2 + b * y ^ 2 - c * x * y ≤ ε * x) :
    η * x ^ 2 + y ^ 2 < r ^ 2 := by
  have hβpos : 0 < b - c / (2 * √η) := sub_pos.mpr hb
  have hα : 0 < a - η * b := by
    have h0 : 0 ≤ ε ^ 2 / (4 * r ^ 2) := by positivity
    exact pos_of_mul_pos_left (h0.trans_lt hcap) hβpos.le
  refine (weighted_energy_le_of_quadratic_constraint hη hc hb (sub_pos.mp hα) h).trans_lt ?_
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ (by positivity)] at hcap
  nlinarith

/-- **The support function of a weighted energy ball.** If `η x² + y² ≤ r²`, then
`p x + q y ≤ r √(p² / η + q²)` for all `p`, `q`, by the Cauchy–Schwarz inequality. -/
theorem mul_add_mul_le_of_weighted_energy_le {η r x y : ℝ} (hη : 0 < η) (hr : 0 ≤ r)
    (h : η * x ^ 2 + y ^ 2 ≤ r ^ 2) (p q : ℝ) : p * x + q * y ≤ r * √(p ^ 2 / η + q ^ 2) := by
  have hs : 0 ≤ p ^ 2 / η + q ^ 2 := by positivity
  refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (by positivity))
  rw [mul_pow, Real.sq_sqrt hs]
  have hcs : (p * x + q * y) ^ 2 ≤ (p ^ 2 / η + q ^ 2) * (η * x ^ 2 + y ^ 2) := by
    have hid : (p ^ 2 / η + q ^ 2) * (η * x ^ 2 + y ^ 2) - (p * x + q * y) ^ 2 =
        (p * y - η * q * x) ^ 2 / η := by
      field_simp
      ring
    have : 0 ≤ (p * y - η * q * x) ^ 2 / η := by positivity
    linarith
  calc
    _ ≤ (p ^ 2 / η + q ^ 2) * (η * x ^ 2 + y ^ 2) := hcs
    _ ≤ (p ^ 2 / η + q ^ 2) * r ^ 2 := mul_le_mul_of_nonneg_left h hs
    _ = r ^ 2 * (p ^ 2 / η + q ^ 2) := mul_comm _ _

/-- **A weighted energy ball from its support function.** If `x, y ≥ 0` and
`p x + q y ≤ r √(p² / η + q²)` for all `p, q ≥ 0`, then `η x² + y² ≤ r²`: take `p = η x` and
`q = y`. -/
theorem weighted_energy_le_of_forall_mul_add_mul_le {η r x y : ℝ} (hη : 0 < η) (hr : 0 ≤ r)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p * x + q * y ≤ r * √(p ^ 2 / η + q ^ 2)) :
    η * x ^ 2 + y ^ 2 ≤ r ^ 2 := by
  have hn0 : 0 ≤ η * x ^ 2 + y ^ 2 := by positivity
  set n := √(η * x ^ 2 + y ^ 2) with hn
  have hnsq : n ^ 2 = η * x ^ 2 + y ^ 2 := Real.sq_sqrt hn0
  have h1 := h (η * x) y (by positivity) hy
  have h2 : (η * x) ^ 2 / η + y ^ 2 = η * x ^ 2 + y ^ 2 := by
    field_simp
  rw [h2, ← hn] at h1
  have h3 : n * n ≤ r * n := by nlinarith
  have hnr : n ≤ r := by
    rcases (Real.sqrt_nonneg (η * x ^ 2 + y ^ 2)).eq_or_lt with h0 | hpos
    · rw [hn, ← h0]
      exact hr
    · exact le_of_mul_le_mul_right h3 hpos
  rw [← hnsq]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hnr 2

end Scalars

section Ball

variable {E H Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The weighted energy ball `{u | η ‖mass u‖² + ‖gradient u‖² ≤ r²}` of two bounded linear
maps. -/
def weightedEnergyBall (mass : E →L[ℝ] H) (gradient : E →L[ℝ] Z) (η r : ℝ) : Set E :=
  {u | η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤ r ^ 2}

/-- Membership in the weighted energy ball. -/
theorem mem_weightedEnergyBall {mass : E →L[ℝ] H} {gradient : E →L[ℝ] Z} {η r : ℝ} {u : E} :
    u ∈ weightedEnergyBall mass gradient η r ↔ η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤ r ^ 2 :=
  Iff.rfl

/-- The weighted energy ball contains the origin. -/
theorem zero_mem_weightedEnergyBall (mass : E →L[ℝ] H) (gradient : E →L[ℝ] Z) (η r : ℝ) :
    (0 : E) ∈ weightedEnergyBall mass gradient η r := by
  rw [mem_weightedEnergyBall]
  simpa only [map_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    mul_zero, add_zero] using sq_nonneg r

/-- The weighted energy ball is closed. -/
theorem isClosed_weightedEnergyBall (mass : E →L[ℝ] H) (gradient : E →L[ℝ] Z) (η r : ℝ) :
    IsClosed (weightedEnergyBall mass gradient η r) :=
  isClosed_le (by fun_prop) continuous_const

/-- The squared norm of the image of a segment point is at most the average of the squared
norms at the ends. -/
private theorem norm_sq_segment_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (u v : E) {t₁ t₂ : ℝ}
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (ht : t₁ + t₂ = 1) :
    ‖L (t₁ • u + t₂ • v)‖ ^ 2 ≤ t₁ * ‖L u‖ ^ 2 + t₂ * ‖L v‖ ^ 2 := by
  have hsq : (t₁ * ‖L u‖ + t₂ * ‖L v‖) ^ 2 ≤ t₁ * ‖L u‖ ^ 2 + t₂ * ‖L v‖ ^ 2 := by
    have h2 : t₂ = 1 - t₁ := by linarith
    subst h2
    nlinarith [mul_nonneg (mul_nonneg ht₁ ht₂) (sq_nonneg (‖L u‖ - ‖L v‖))]
  refine (pow_le_pow_left₀ (norm_nonneg _) ?_ 2).trans hsq
  rw [map_add, map_smul, map_smul]
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ht₁, Real.norm_of_nonneg ht₂]

/-- The weighted energy ball is convex: the weighted energy is convex along segments. -/
theorem convex_weightedEnergyBall (mass : E →L[ℝ] H) (gradient : E →L[ℝ] Z) {η : ℝ}
    (hη : 0 ≤ η) (r : ℝ) : Convex ℝ (weightedEnergyBall mass gradient η r) := by
  intro u hu v hv t₁ t₂ ht₁ ht₂ ht
  rw [mem_weightedEnergyBall] at hu hv ⊢
  have h₁ := mul_le_mul_of_nonneg_left (norm_sq_segment_le mass u v ht₁ ht₂ ht) hη
  have h₂ := norm_sq_segment_le gradient u v ht₁ ht₂ ht
  have h₃ := mul_le_mul_of_nonneg_left hu ht₁
  have h₄ := mul_le_mul_of_nonneg_left hv ht₂
  have h₅ : t₁ * r ^ 2 + t₂ * r ^ 2 = r ^ 2 := by rw [← add_mul, ht, one_mul]
  linarith

/-- If `‖u‖² = ‖mass u‖² + ‖gradient u‖²`, the weighted energy ball lies in the ball of radius
`r / √η + r`. -/
theorem norm_le_of_mem_weightedEnergyBall {mass : E →L[ℝ] H} {gradient : E →L[ℝ] Z} {η r : ℝ}
    (hη : 0 < η) (hr : 0 ≤ r) {u : E} (hnorm : ‖u‖ ^ 2 = ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2)
    (hu : u ∈ weightedEnergyBall mass gradient η r) : ‖u‖ ≤ r / √η + r := by
  rw [mem_weightedEnergyBall] at hu
  have hsη : 0 < √η := Real.sqrt_pos.mpr hη
  have hm : ‖mass u‖ ≤ r / √η := by
    rw [le_div_iff₀ hsη]
    refine abs_le_of_sq_le_sq' ?_ hr |>.2
    rw [mul_pow, Real.sq_sqrt hη.le]
    nlinarith [sq_nonneg ‖gradient u‖]
  have hg : ‖gradient u‖ ≤ r :=
    abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖mass u‖]) hr |>.2
  have hsum : ‖u‖ ≤ ‖mass u‖ + ‖gradient u‖ := by
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [hnorm]
    nlinarith [norm_nonneg (mass u), norm_nonneg (gradient u)]
  linarith

end Ball

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Transport validation in a weighted energy ball** (Hou, Wang and Yang, Section 4.3). Let the
form `B` have coercivity margins `a`, `b` in the value and gradient norms, the residual `ell`
size `ε` and the load `N` size `M ‖u‖²` on the ball, both in the value norm. For a weight
`η > 0` with `η b ≤ a` and a radius `r ≥ 0` with

`ε + (M / η) r² ≤ b √η r`,

there is a solution `u` of `B u + transport (R u) u + N u = ell` in the ball
`η ‖u‖² + ‖∇u‖² ≤ r²`. The ball is closed, convex and bounded, the a priori estimate
`weighted_energy_le_of_budget` makes it invariant, and
`exists_solution_of_transport_cancellation_on` gives the fixed point. -/
theorem exists_solution_of_weighted_energy_transport
    {H Z : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (mass : V →L[ℝ] H) (gradient : V →L[ℝ] Z)
    (hnorm : ∀ u, ‖u‖ ^ 2 = ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2)
    (B : V →L[ℝ] StrongDual ℝ V)
    (transport : A →L[ℝ] V →L[ℝ] StrongDual ℝ V) (R : V →L[ℝ] A)
    (hcancel : ∀ a u, transport a u u = 0)
    (e : V →L[ℝ] W) (he : Function.Injective e) (hcompact : IsCompactOperator e)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V)
    {a b η r ε M : ℝ} (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (hηb : η * b ≤ a) (hr : 0 ≤ r)
    (hM : 0 ≤ M)
    (hcoercive : ∀ u, a * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 ≤ B u u)
    (hell : ∀ v, |ell v| ≤ ε * ‖mass v‖)
    (hN : ∀ u, η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤ r ^ 2 →
      ∀ v, |N u v| ≤ M * ‖mass u‖ ^ 2 * ‖mass v‖)
    {k C : NNReal} (htransport : ∀ u v, ‖transport (R u) v‖ ≤ k * ‖e u‖ * ‖v‖)
    (hNcontinuous : ∀ u, η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤ r ^ 2 →
      ∀ v, η * ‖mass v‖ ^ 2 + ‖gradient v‖ ^ 2 ≤ r ^ 2 → ‖N u - N v‖ ≤ C * ‖e (u - v)‖)
    (hbudget : ε + M / η * r ^ 2 ≤ b * √η * r) :
    ∃ u, η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤ r ^ 2 ∧
      ∀ v, B u v + transport (R u) u v + N u v = ell v := by
  have hcoercive' (u : V) : min a b * ‖u‖ * ‖u‖ ≤ B u u := by
    calc
      min a b * ‖u‖ * ‖u‖ = min a b * (‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2) := by
        rw [← hnorm u]
        ring
      _ ≤ a * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 := by
        rw [mul_add]
        exact add_le_add
          (mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg _))
          (mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg _))
      _ ≤ B u u := hcoercive u
  have hinvariant (w : V) (hw : w ∈ weightedEnergyBall mass gradient η r) (u : V)
      (hu : B u u ≤ (ell - N w) u) : u ∈ weightedEnergyBall mass gradient η r := by
    have hw' : η * ‖mass w‖ ^ 2 + ‖gradient w‖ ^ 2 ≤ r ^ 2 := hw
    refine weighted_energy_le_of_budget (m := ‖mass w‖) hb hη hηb hr (norm_nonneg _) hM
      (by linarith [sq_nonneg ‖gradient w‖]) hbudget ?_
    calc
      _ ≤ (ell - N w) u := (hcoercive u).trans hu
      _ ≤ |ell u| + |N w u| := by
        change ell u - N w u ≤ _
        linarith only [le_abs_self (ell u), neg_abs_le (N w u)]
      _ ≤ ε * ‖mass u‖ + M * ‖mass w‖ ^ 2 * ‖mass u‖ := add_le_add (hell u) (hN w hw' u)
      _ = _ := by ring
  obtain ⟨u, hu, heq⟩ := exists_solution_of_transport_cancellation_on
    B transport R hcancel e he hcompact N ell ⟨0, zero_mem_weightedEnergyBall mass gradient η r⟩
    (isClosed_weightedEnergyBall mass gradient η r)
    (convex_weightedEnergyBall mass gradient hη.le r)
    (lt_min ha hb) (by positivity : 0 ≤ r / √η + r)
    (fun u hu ↦ norm_le_of_mem_weightedEnergyBall hη hr (hnorm u) hu) hcoercive' htransport
    (fun u hu v hv ↦ hNcontinuous u hu v hv) hinvariant
  exact ⟨u, hu, heq⟩

/-- Transport validation in a weighted energy ball of a closed subspace `S`. Every hypothesis
is required only on `S`, the solution lies in `S`, and the equation is tested by the vectors of
`S`. The argument runs in the Hilbert space `S` itself. -/
theorem exists_solution_of_weighted_energy_transport_on_submodule
    {H Z : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (S : Submodule ℝ V) (hS : IsClosed (S : Set V))
    (mass : V →L[ℝ] H) (gradient : V →L[ℝ] Z)
    (hnorm : ∀ u ∈ S, ‖u‖ ^ 2 = ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2)
    (B : V →L[ℝ] StrongDual ℝ V)
    (transport : A →L[ℝ] V →L[ℝ] StrongDual ℝ V) (R : V →L[ℝ] A)
    (hcancel : ∀ u ∈ S, ∀ v ∈ S, transport (R u) v v = 0)
    (e : V →L[ℝ] W) (he : Set.InjOn e S) (hcompact : IsCompactOperator e)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V)
    {a b η r ε M : ℝ} (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (hηb : η * b ≤ a) (hr : 0 ≤ r)
    (hM : 0 ≤ M)
    (hcoercive : ∀ u ∈ S, a * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 ≤ B u u)
    (hell : ∀ v ∈ S, |ell v| ≤ ε * ‖mass v‖)
    (hN : ∀ u ∈ S, η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤ r ^ 2 →
      ∀ v ∈ S, |N u v| ≤ M * ‖mass u‖ ^ 2 * ‖mass v‖)
    {k C : NNReal}
    (htransport : ∀ u ∈ S, ∀ v ∈ S, ‖transport (R u) v‖ ≤ k * ‖e u‖ * ‖v‖)
    (hNcontinuous : ∀ u ∈ S, η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤ r ^ 2 →
      ∀ v ∈ S, η * ‖mass v‖ ^ 2 + ‖gradient v‖ ^ 2 ≤ r ^ 2 → ‖N u - N v‖ ≤ C * ‖e (u - v)‖)
    (hbudget : ε + M / η * r ^ 2 ≤ b * √η * r) :
    ∃ u ∈ S, η * ‖mass u‖ ^ 2 + ‖gradient u‖ ^ 2 ≤ r ^ 2 ∧
      ∀ v ∈ S, B u v + transport (R u) u v + N u v = ell v := by
  have : CompleteSpace S := hS.completeSpace_coe
  -- The transport form with the reconstruction built in, so that only `S` enters.
  obtain ⟨u, hu, heq⟩ := exists_solution_of_weighted_energy_transport
    (mass.comp S.subtypeL) (gradient.comp S.subtypeL) (fun u ↦ hnorm u u.2)
    (PDE.Analysis.Evolution.restrictForm S B)
    (ContinuousTrilinearForm.restrict transport (R.comp S.subtypeL) S.subtypeL S.subtypeL)
    (ContinuousLinearMap.id ℝ S) (fun u v ↦ hcancel u u.2 v v.2) (e.comp S.subtypeL)
    (fun u v huv ↦ Subtype.ext (he u.2 v.2 huv)) (hcompact.comp_clm S.subtypeL)
    (fun u ↦ PDE.Analysis.Evolution.restrictFunctional S (N u))
    (PDE.Analysis.Evolution.restrictFunctional S ell) ha hb hη hηb hr hM
    (fun u ↦ by
      rw [PDE.Analysis.Evolution.restrictForm_apply]
      exact hcoercive u u.2)
    (fun v ↦ hell v v.2) (fun u hu v ↦ hN u u.2 hu v v.2)
    (fun u v ↦ (PDE.Analysis.Evolution.norm_restrictFunctional_le S _).trans
      (htransport u u.2 v v.2))
    (fun u hu v hv ↦
      (PDE.Analysis.Evolution.norm_restrictFunctional_le S (N u - N v)).trans
        (hNcontinuous u u.2 hu v v.2 hv))
    hbudget
  exact ⟨u, u.2, hu, fun v hv ↦ heq ⟨v, hv⟩⟩

omit [CompleteSpace V] in
/-- **The refined bound at a solution** (Hou, Wang and Yang, (4.42) and (4.43)). Let `u` solve
`B u + transport (R u) u + N u = ell` against itself, with transport cancelling. If the load at
`u` tested with `u` is at most `c ‖u‖ ‖∇u‖`, then for all `p`, `q`

`p ‖u‖ + q ‖∇u‖ ≤ 2 ε / (4 a b - c²) (b p + c q / 2 + √(b (b p² + c p q + a q²)))`.

Testing gives `a ‖u‖² + b ‖∇u‖² - c ‖u‖ ‖∇u‖ ≤ ε ‖u‖`, and `add_le_of_quadratic_constraint`
does the rest. -/
theorem add_le_of_isSolution_of_split_energy
    {H Z : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (mass : V →L[ℝ] H) (gradient : V →L[ℝ] Z) (B : V →L[ℝ] StrongDual ℝ V)
    (ell load : StrongDual ℝ V) {a b c ε : ℝ} (hb : 0 < b) (hD : c ^ 2 < 4 * a * b)
    (hε : 0 ≤ ε) {u : V}
    (hcoercive : a * ‖mass u‖ ^ 2 + b * ‖gradient u‖ ^ 2 ≤ B u u)
    (hell : |ell u| ≤ ε * ‖mass u‖)
    (hload : |load u| ≤ c * ‖mass u‖ * ‖gradient u‖)
    (heq : B u u + load u = ell u) (p q : ℝ) :
    p * ‖mass u‖ + q * ‖gradient u‖ ≤ 2 * ε / (4 * a * b - c ^ 2) *
      (b * p + c * q / 2 + √(b * (b * p ^ 2 + c * p * q + a * q ^ 2))) := by
  refine add_le_of_quadratic_constraint hb hD hε ?_
  linarith [le_abs_self (ell u), neg_abs_le (load u)]

end PDE.Analysis.Variational
