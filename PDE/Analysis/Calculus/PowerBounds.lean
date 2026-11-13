/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Holder.BoundedHolder
public import PDE.Spaces.Holder.Homogeneous
public import PDE.FDeriv.PartialDeriv
public import PDE.FDeriv.PointBounds
import PDE.FDeriv.PartialDeriv.Energy
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Two-scale power bounds of a function and its derivative

`PDE.Analysis.IsPowerBoundOn s f p q C` states that at every point `x` of `s`, `f` has the point
bounds `PDE.HasPointBounds` with `|f(x)| ≤ C m(x)^p M(x)^q` and `‖Df(x)‖ ≤ C m(x)^{p - 1} M(x)^q`,
where `m(x) = min(‖x‖, 1)` and `M(x) = max(‖x‖, 1)`: near the origin `f` vanishes like `‖x‖^p` (and
its derivative like `‖x‖^{p - 1}`), far from it both grow at most like `‖x‖^q`. The class is
closed under products (the exponents add) and sums with equal exponents, and on a bounded set a
power of `M` can be traded for a constant.

On a convex set inside a ball of radius `ρ ≥ 1` avoiding the origin the class gives bounded
Hölder functions: with `p = 1/2` through `HolderSpace.norm_sub_le_of_rpow_bounds`, and with
`p = 1` through the bounded derivative.

## Main definitions

* `IsPowerBoundOn`: the point bounds `|f| ≤ C m^p M^q` and `‖Df‖ ≤ C m^{p - 1} M^q` at every
  point of `s`.

## Main results

* `IsPowerBoundOn.mul`: a product of power-bounded functions is power-bounded; the exponents add.
* `IsPowerBoundOn.pow`: `f^n` has the exponents `(n p, n q)`.
* `IsPowerBoundOn.trade`: on the ball of radius `ρ ≥ 1` the far exponent `q` can be lowered to
  `q - 1` at the cost of a factor `ρ`.
* `IsPowerBoundOn.of_near_far`: separate bounds for `‖x‖ ≤ 1` and `‖x‖ ≥ 1` give the two-scale
  bounds.
* `IsPowerBoundOn.isBoundedHolderOn`: with `p = 1/2`, `f` is bounded and `1/2`-Hölder on a convex
  set inside the ball of radius `ρ ≥ 1` avoiding the origin.
* `IsPowerBoundOn.isBoundedHolderOn_of_one`: with `p = 1`, `f` is bounded and `α`-Hölder for
  `0 ≤ α ≤ 1` on such a set.
* `IsPowerBoundOn.partialDeriv_mul`: the product rule for the bounds of a coordinate derivative.
* `exists_isPowerBoundOn_of_hasCompactSupport`: a compactly supported `C¹` function has the
  exponents `(0, 0)` on every set avoiding the origin.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Two-scale power bounds**: at every point `x` of `s`, `f` is differentiable with
`|f(x)| ≤ C min(‖x‖, 1)^p max(‖x‖, 1)^q` and `‖Df(x)‖ ≤ C min(‖x‖, 1)^{p - 1} max(‖x‖, 1)^q`. -/
def IsPowerBoundOn (s : Set E) (f : E → ℝ) (p q C : ℝ) : Prop :=
  ∀ x ∈ s, HasPointBounds f x (C * min ‖x‖ 1 ^ p * max ‖x‖ 1 ^ q)
    (C * min ‖x‖ 1 ^ (p - 1) * max ‖x‖ 1 ^ q)

namespace IsPowerBoundOn

variable {s : Set E} {f g : E → ℝ} {p q C p' q' C' : ℝ}

omit [NormedSpace ℝ E] in
/-- For `x ≠ 0`, `min ‖x‖ 1 > 0`. -/
private theorem min_pos {x : E} (hx : x ≠ 0) : 0 < min ‖x‖ 1 :=
  lt_min (norm_pos_iff.2 hx) one_pos

omit [NormedSpace ℝ E] in
/-- `max ‖x‖ 1 ≥ 1`. -/
private theorem one_le_max (x : E) : 1 ≤ max ‖x‖ 1 := le_max_right _ _

omit [NormedSpace ℝ E] in
/-- `max ‖x‖ 1 > 0`. -/
private theorem max_pos (x : E) : 0 < max ‖x‖ 1 := one_pos.trans_le (one_le_max x)

/-- The constant of a power bound on a set avoiding the origin is nonnegative, as soon as the set
contains a point. -/
theorem nonneg (h : IsPowerBoundOn s f p q C) (hs : ∀ x ∈ s, x ≠ 0) {x : E} (hx : x ∈ s) :
    0 ≤ C := by
  have h1 := (h x hx).value_nonneg
  have hm := Real.rpow_pos_of_pos (min_pos (hs x hx)) p
  have hM := Real.rpow_pos_of_pos (max_pos x) q
  by_contra hC
  push Not at hC
  have : C * min ‖x‖ 1 ^ p * max ‖x‖ 1 ^ q < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hC hm) hM
  linarith

/-- Weaker exponents and a larger constant: `p' ≤ p`, `q ≤ q'`, `C ≤ C'`. -/
theorem mono (h : IsPowerBoundOn s f p q C) (hs : ∀ x ∈ s, x ≠ 0) (hp : p' ≤ p) (hq : q ≤ q')
    (hC : C ≤ C') : IsPowerBoundOn s f p' q' C' := by
  have key : ∀ x ∈ s, ∀ a a' : ℝ, a' ≤ a →
      C * min ‖x‖ 1 ^ a * max ‖x‖ 1 ^ q ≤ C' * min ‖x‖ 1 ^ a' * max ‖x‖ 1 ^ q' := by
    intro x hx a a' ha
    have hC0 := h.nonneg hs hx
    have hm := min_pos (hs x hx)
    have h1 : min ‖x‖ 1 ^ a ≤ min ‖x‖ 1 ^ a' :=
      Real.rpow_le_rpow_of_exponent_ge hm (min_le_right _ _) ha
    have h2 : max ‖x‖ 1 ^ q ≤ max ‖x‖ 1 ^ q' :=
      Real.rpow_le_rpow_of_exponent_le (one_le_max x) hq
    have e1 := Real.rpow_nonneg hm.le a
    have e2 := Real.rpow_nonneg (max_pos x).le q
    calc C * min ‖x‖ 1 ^ a * max ‖x‖ 1 ^ q ≤ C * min ‖x‖ 1 ^ a' * max ‖x‖ 1 ^ q' := by gcongr
      _ ≤ C' * min ‖x‖ 1 ^ a' * max ‖x‖ 1 ^ q' := by
          have := Real.rpow_nonneg hm.le a'
          have := Real.rpow_nonneg (max_pos x).le q'
          gcongr
  exact fun x hx ↦ (h x hx).mono (key x hx p p' hp) (key x hx (p - 1) (p' - 1) (by linarith))

/-- A power bound on `s` holds on every subset `t ⊆ s`. -/
theorem mono_set {t : Set E} (h : IsPowerBoundOn s f p q C) (hts : t ⊆ s) :
    IsPowerBoundOn t f p q C :=
  fun x hx ↦ h x (hts hx)

/-- Rewriting the function, the exponents and the constant. -/
theorem of_eq {f' : E → ℝ} {p'' q'' C'' : ℝ} (h : IsPowerBoundOn s f p q C) (hf : ∀ x, f x = f' x)
    (hp : p = p'') (hq : q = q'') (hC : C = C'') : IsPowerBoundOn s f' p'' q'' C'' := by
  obtain rfl : f = f' := funext hf
  subst hp hq hC
  exact h

/-- Every function is bounded on the empty set. -/
theorem of_empty : IsPowerBoundOn (∅ : Set E) f p q C :=
  fun _ h ↦ h.elim

/-- Local congruence. -/
theorem congr (h : IsPowerBoundOn s f p q C) (hfg : ∀ x ∈ s, f =ᶠ[nhds x] g) :
    IsPowerBoundOn s g p q C :=
  fun x hx ↦ (h x hx).congr (hfg x hx)

/-- A sum of functions with the exponents `(p, q)` has these exponents, with the sum of the
constants. -/
theorem add (hf : IsPowerBoundOn s f p q C) (hg : IsPowerBoundOn s g p q C') :
    IsPowerBoundOn s (fun x ↦ f x + g x) p q (C + C') :=
  fun x hx ↦ ((hf x hx).add (hg x hx)).mono (le_of_eq (by ring)) (le_of_eq (by ring))

/-- The negation of a function keeps its power bound. -/
theorem neg (hf : IsPowerBoundOn s f p q C) : IsPowerBoundOn s (fun x ↦ -f x) p q C :=
  fun x hx ↦ (hf x hx).neg

/-- A difference of functions with the exponents `(p, q)` has these exponents, with the sum of the
constants. -/
theorem sub (hf : IsPowerBoundOn s f p q C) (hg : IsPowerBoundOn s g p q C') :
    IsPowerBoundOn s (fun x ↦ f x - g x) p q (C + C') := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- The multiple `k f` keeps the exponents of `f`, with the constant `|k| C`. -/
theorem const_mul (hf : IsPowerBoundOn s f p q C) (k : ℝ) :
    IsPowerBoundOn s (fun x ↦ k * f x) p q (|k| * C) :=
  fun x hx ↦ ((hf x hx).const_mul k).mono (le_of_eq (by ring)) (le_of_eq (by ring))

/-- **Products**: the exponents add and the constant is `2 C C'`. -/
theorem mul (hf : IsPowerBoundOn s f p q C) (hg : IsPowerBoundOn s g p' q' C')
    (hs : ∀ x ∈ s, x ≠ 0) :
    IsPowerBoundOn s (fun x ↦ f x * g x) (p + p') (q + q') (2 * C * C') := by
  intro x hx
  have hC := hf.nonneg hs hx
  have hC' := hg.nonneg hs hx
  have hm := min_pos (hs x hx)
  have hM := max_pos x
  refine ((hf x hx).mul (hg x hx)).mono ?_ (le_of_eq ?_)
  · have e : min ‖x‖ 1 ^ (p + p') * max ‖x‖ 1 ^ (q + q') =
        (min ‖x‖ 1 ^ p * max ‖x‖ 1 ^ q) * (min ‖x‖ 1 ^ p' * max ‖x‖ 1 ^ q') := by
      rw [Real.rpow_add hm, Real.rpow_add hM]; ring
    have : 0 ≤ C * C' * (min ‖x‖ 1 ^ (p + p') * max ‖x‖ 1 ^ (q + q')) := by positivity
    calc (C * min ‖x‖ 1 ^ p * max ‖x‖ 1 ^ q) * (C' * min ‖x‖ 1 ^ p' * max ‖x‖ 1 ^ q') =
          C * C' * (min ‖x‖ 1 ^ (p + p') * max ‖x‖ 1 ^ (q + q')) := by rw [e]; ring
      _ ≤ 2 * C * C' * min ‖x‖ 1 ^ (p + p') * max ‖x‖ 1 ^ (q + q') := by nlinarith
  · have e1 : min ‖x‖ 1 ^ (p + p' - 1) * max ‖x‖ 1 ^ (q + q') =
        (min ‖x‖ 1 ^ p * max ‖x‖ 1 ^ q) * (min ‖x‖ 1 ^ (p' - 1) * max ‖x‖ 1 ^ q') := by
      rw [show p + p' - 1 = p + (p' - 1) by ring, Real.rpow_add hm, Real.rpow_add hM]; ring
    have e2 : min ‖x‖ 1 ^ (p + p' - 1) * max ‖x‖ 1 ^ (q + q') =
        (min ‖x‖ 1 ^ p' * max ‖x‖ 1 ^ q') * (min ‖x‖ 1 ^ (p - 1) * max ‖x‖ 1 ^ q) := by
      rw [show p + p' - 1 = p' + (p - 1) by ring, Real.rpow_add hm, Real.rpow_add hM]; ring
    have k1 : (C * min ‖x‖ 1 ^ p * max ‖x‖ 1 ^ q) *
        (C' * min ‖x‖ 1 ^ (p' - 1) * max ‖x‖ 1 ^ q') =
        C * C' * (min ‖x‖ 1 ^ (p + p' - 1) * max ‖x‖ 1 ^ (q + q')) := by
      rw [e1]; ring
    have k2 : (C' * min ‖x‖ 1 ^ p' * max ‖x‖ 1 ^ q') *
        (C * min ‖x‖ 1 ^ (p - 1) * max ‖x‖ 1 ^ q) =
        C * C' * (min ‖x‖ 1 ^ (p + p' - 1) * max ‖x‖ 1 ^ (q + q')) := by
      rw [e2]; ring
    rw [k1, k2]; ring

/-- **Trading growth for a constant** on a bounded set: `max(‖x‖, 1)^q ≤ ρ max(‖x‖, 1)^{q - 1}`
for `‖x‖ ≤ ρ`, `1 ≤ ρ`. -/
theorem trade (h : IsPowerBoundOn s f p q C) (hs : ∀ x ∈ s, x ≠ 0) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (hsρ : ∀ x ∈ s, ‖x‖ ≤ ρ) : IsPowerBoundOn s f p (q - 1) (ρ * C) := by
  have key : ∀ x ∈ s, ∀ a : ℝ, C * min ‖x‖ 1 ^ a * max ‖x‖ 1 ^ q ≤
      ρ * C * min ‖x‖ 1 ^ a * max ‖x‖ 1 ^ (q - 1) := by
    intro x hx a
    have hC := h.nonneg hs hx
    have hM := max_pos x
    have hMρ : max ‖x‖ 1 ≤ ρ := max_le (hsρ x hx) hρ
    have e : max ‖x‖ 1 ^ q = max ‖x‖ 1 ^ (q - 1) * max ‖x‖ 1 := by
      rw [← Real.rpow_add_one hM.ne', sub_add_cancel]
    have hm := Real.rpow_nonneg (min_pos (hs x hx)).le a
    have hq := Real.rpow_nonneg hM.le (q - 1)
    rw [e]
    calc C * min ‖x‖ 1 ^ a * (max ‖x‖ 1 ^ (q - 1) * max ‖x‖ 1) ≤
          C * min ‖x‖ 1 ^ a * (max ‖x‖ 1 ^ (q - 1) * ρ) := by gcongr
      _ = ρ * C * min ‖x‖ 1 ^ a * max ‖x‖ 1 ^ (q - 1) := by ring
  exact fun x hx ↦ (h x hx).mono (key x hx p) (key x hx (p - 1))

/-- **Near and far bounds**: `|f(x)| ≤ C ‖x‖^p`, `‖Df(x)‖ ≤ C ‖x‖^{p - 1}` for `‖x‖ ≤ 1` and
`|f(x)| ≤ C ‖x‖^q`, `‖Df(x)‖ ≤ C ‖x‖^q` for `‖x‖ ≥ 1` give the two-scale bounds. -/
theorem of_near_far (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hnear : ∀ x ∈ s, ‖x‖ ≤ 1 → |f x| ≤ C * ‖x‖ ^ p ∧ ‖fderiv ℝ f x‖ ≤ C * ‖x‖ ^ (p - 1))
    (hfar : ∀ x ∈ s, 1 ≤ ‖x‖ → |f x| ≤ C * ‖x‖ ^ q ∧ ‖fderiv ℝ f x‖ ≤ C * ‖x‖ ^ q) :
    IsPowerBoundOn s f p q C := by
  have hn : ∀ x : E, ‖x‖ ≤ 1 → min ‖x‖ 1 = ‖x‖ ∧ max ‖x‖ 1 = 1 := fun x h ↦
    ⟨min_eq_left h, max_eq_right h⟩
  have hf : ∀ x : E, 1 ≤ ‖x‖ → min ‖x‖ 1 = 1 ∧ max ‖x‖ 1 = ‖x‖ := fun x h ↦
    ⟨min_eq_right h, max_eq_left h⟩
  intro x hx
  refine ⟨hd x hx, ?_, ?_⟩ <;> rcases le_total ‖x‖ 1 with h | h
  · rw [(hn x h).1, (hn x h).2, Real.one_rpow, mul_one]; exact (hnear x hx h).1
  · rw [(hf x h).1, (hf x h).2, Real.one_rpow, mul_one]; exact (hfar x hx h).1
  · rw [(hn x h).1, (hn x h).2, Real.one_rpow, mul_one]; exact (hnear x hx h).2
  · rw [(hf x h).1, (hf x h).2, Real.one_rpow, mul_one]; exact (hfar x hx h).2

/-- **The vanishing consumer**: with `p = 1/2` and `0 ≤ q`, on a convex set inside the ball of
radius `ρ ≥ 1` avoiding the origin, `f` is bounded and `1/2`-Hölder with the constant
`6 C ρ^{q + 1/2}`: there `|f(x)| ≤ C ρ^q ‖x‖^{1/2}` and `‖Df(x)‖ ≤ C ρ^{q + 1/2} ‖x‖^{-1/2}`,
and `HolderSpace.norm_sub_le_of_rpow_bounds` applies. -/
theorem isBoundedHolderOn (h : IsPowerBoundOn s f (1 / 2) q C) (hconv : Convex ℝ s)
    (hs : ∀ x ∈ s, x ≠ 0) {ρ : ℝ} (hρ : 1 ≤ ρ) (hsρ : ∀ x ∈ s, ‖x‖ ≤ ρ) (hq : 0 ≤ q) :
    HolderSpace.IsBoundedHolderOn (1 / 2) s f (6 * (C * ρ ^ (q + 1 / 2))) := by
  rcases s.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · subst he; exact ⟨fun _ h ↦ h.elim, fun _ h ↦ h.elim⟩
  have hC := h.nonneg hs hx₀
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hM : ∀ x ∈ s, max ‖x‖ 1 ^ q ≤ ρ ^ q := fun x hx ↦
    Real.rpow_le_rpow (by positivity) (max_le (hsρ x hx) hρ) hq
  have hρq : ρ ^ q ≤ ρ ^ (q + 1 / 2) := Real.rpow_le_rpow_of_exponent_le hρ (by linarith)
  have hval : ∀ x ∈ s, |f x| ≤ C * ρ ^ q * ‖x‖ ^ (1 / 2 : ℝ) ∧ |f x| ≤ C * ρ ^ q := by
    intro x hx
    have hm := Real.rpow_nonneg (min_pos (hs x hx)).le (1 / 2 : ℝ)
    have h1 : |f x| ≤ C * ρ ^ q * min ‖x‖ 1 ^ (1 / 2 : ℝ) :=
      calc |f x| ≤ C * min ‖x‖ 1 ^ (1 / 2 : ℝ) * max ‖x‖ 1 ^ q := (h x hx).abs_le
        _ ≤ C * min ‖x‖ 1 ^ (1 / 2 : ℝ) * ρ ^ q :=
            mul_le_mul_of_nonneg_left (hM x hx) (mul_nonneg hC hm)
        _ = C * ρ ^ q * min ‖x‖ 1 ^ (1 / 2 : ℝ) := by ring
    have hmx : min ‖x‖ 1 ^ (1 / 2 : ℝ) ≤ ‖x‖ ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (min_pos (hs x hx)).le (min_le_left _ _) (by norm_num)
    have hm1 : min ‖x‖ 1 ^ (1 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one (min_pos (hs x hx)).le (min_le_right _ _) (by norm_num)
    have hCq : 0 ≤ C * ρ ^ q := mul_nonneg hC (Real.rpow_nonneg hρ0.le _)
    exact ⟨h1.trans (mul_le_mul_of_nonneg_left hmx hCq),
      h1.trans ((mul_le_mul_of_nonneg_left hm1 hCq).trans_eq (mul_one _))⟩
  have hder : ∀ x ∈ s, x ≠ 0 →
      ‖fderiv ℝ f x‖ ≤ C * ρ ^ (q + 1 / 2) * ‖x‖ ^ (1 / 2 - 1 : ℝ) := by
    intro x hx _
    have hx0 : 0 < ‖x‖ := norm_pos_iff.2 (hs x hx)
    have hm := min_pos (hs x hx)
    have key : min ‖x‖ 1 ^ (1 / 2 - 1 : ℝ) * max ‖x‖ 1 ^ q ≤
        ρ ^ (q + 1 / 2) * ‖x‖ ^ (1 / 2 - 1 : ℝ) := by
      rcases le_total ‖x‖ 1 with h1 | h1
      · rw [min_eq_left h1, max_eq_right h1, Real.one_rpow, mul_one]
        have : 1 ≤ ρ ^ (q + 1 / 2) := Real.one_le_rpow hρ (by linarith)
        have := Real.rpow_nonneg hx0.le (1 / 2 - 1 : ℝ)
        nlinarith
      · rw [min_eq_right h1, max_eq_left h1, Real.one_rpow, one_mul]
        have e : ρ ^ (q + 1 / 2) * ‖x‖ ^ (1 / 2 - 1 : ℝ) =
            ρ ^ q * (ρ / ‖x‖) ^ (1 / 2 : ℝ) := by
          rw [Real.rpow_add hρ0, Real.div_rpow hρ0.le hx0.le,
            show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hx0.le]
          field_simp
        rw [e]
        have h2 : ‖x‖ ^ q ≤ ρ ^ q := Real.rpow_le_rpow hx0.le (hsρ x hx) hq
        have h3 : 1 ≤ (ρ / ‖x‖) ^ (1 / 2 : ℝ) :=
          Real.one_le_rpow ((one_le_div hx0).2 (hsρ x hx)) (by norm_num)
        have := Real.rpow_nonneg hρ0.le q
        nlinarith
    calc ‖fderiv ℝ f x‖ ≤ C * min ‖x‖ 1 ^ (1 / 2 - 1 : ℝ) * max ‖x‖ 1 ^ q :=
          (h x hx).norm_fderiv_le
      _ = C * (min ‖x‖ 1 ^ (1 / 2 - 1 : ℝ) * max ‖x‖ 1 ^ q) := by ring
      _ ≤ C * (ρ ^ (q + 1 / 2) * ‖x‖ ^ (1 / 2 - 1 : ℝ)) := mul_le_mul_of_nonneg_left key hC
      _ = C * ρ ^ (q + 1 / 2) * ‖x‖ ^ (1 / 2 - 1 : ℝ) := by ring
  have hA : 0 ≤ C * ρ ^ q := mul_nonneg hC (Real.rpow_nonneg hρ0.le _)
  have hK : 0 ≤ C * ρ ^ (q + 1 / 2) := mul_nonneg hC (Real.rpow_nonneg hρ0.le _)
  have h3 : (3 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]; norm_num
  have hCq : C * ρ ^ q ≤ C * ρ ^ (q + 1 / 2) := mul_le_mul_of_nonneg_left hρq hC
  refine ⟨fun x hx ↦ (hval x hx).2.trans (by nlinarith), fun x hx z hz ↦ ?_⟩
  have hH := HolderSpace.norm_sub_le_of_rpow_bounds hconv (by norm_num) (by norm_num)
    (fun y hy ↦ (h y hy).differentiableAt)
    (fun y hy ↦ by rw [Real.norm_eq_abs]; exact (hval y hy).1) hder hx hz
  rw [Real.norm_eq_abs] at hH
  refine hH.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _))
  have : 0 ≤ (3 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  nlinarith

/-- **The bounded-derivative consumer**: with `p = 1` and `0 ≤ q`, on a convex set inside the
ball of radius `ρ ≥ 1` avoiding the origin, `f` is bounded and `α`-Hölder for `0 ≤ α ≤ 1` with
the constant `2 C ρ^q`. -/
theorem isBoundedHolderOn_of_one (h : IsPowerBoundOn s f 1 q C) (hconv : Convex ℝ s)
    (hs : ∀ x ∈ s, x ≠ 0) {ρ : ℝ} (hρ : 1 ≤ ρ) (hsρ : ∀ x ∈ s, ‖x‖ ≤ ρ) (hq : 0 ≤ q)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    HolderSpace.IsBoundedHolderOn α s f (2 * (C * ρ ^ q)) := by
  rcases s.eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
  · subst he; exact ⟨fun _ h ↦ h.elim, fun _ h ↦ h.elim⟩
  have hA : 0 ≤ C * ρ ^ q :=
    mul_nonneg (h.nonneg hs hx₀) (Real.rpow_nonneg (zero_le_one.trans hρ) _)
  have hM : ∀ x ∈ s, max ‖x‖ 1 ^ q ≤ ρ ^ q := fun x hx ↦
    Real.rpow_le_rpow (by positivity) (max_le (hsρ x hx) hρ) hq
  refine HolderSpace.IsBoundedHolderOn.of_norm_fderiv_le hconv hα0 hα1 hA
    (fun x hx ↦ (h x hx).differentiableAt) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · have hm1 : min ‖x‖ 1 ^ (1 : ℝ) ≤ 1 := by
      rw [Real.rpow_one]; exact min_le_right _ _
    have hm0 := Real.rpow_nonneg (min_pos (hs x hx)).le (1 : ℝ)
    have hC := h.nonneg hs hx
    calc |f x| ≤ C * min ‖x‖ 1 ^ (1 : ℝ) * max ‖x‖ 1 ^ q := (h x hx).abs_le
      _ ≤ C * 1 * ρ ^ q := mul_le_mul (mul_le_mul_of_nonneg_left hm1 hC) (hM x hx)
          (Real.rpow_nonneg (max_pos x).le _) (by positivity)
      _ = C * ρ ^ q := by ring
  · have hC := h.nonneg hs hx
    calc ‖fderiv ℝ f x‖ ≤ C * min ‖x‖ 1 ^ (1 - 1 : ℝ) * max ‖x‖ 1 ^ q := (h x hx).norm_fderiv_le
      _ = C * max ‖x‖ 1 ^ q := by rw [sub_self, Real.rpow_zero, mul_one]
      _ ≤ C * ρ ^ q := mul_le_mul_of_nonneg_left (hM x hx) hC

/-! ### Basic members -/

/-- The zero function has every pair of exponents. -/
theorem zero (hs : ∀ x ∈ s, x ≠ 0) (hC : 0 ≤ C) : IsPowerBoundOn s (fun _ ↦ (0 : ℝ)) p q C := by
  intro x hx
  have := Real.rpow_nonneg (min_pos (hs x hx)).le p
  have := Real.rpow_nonneg (min_pos (hs x hx)).le (p - 1)
  have := Real.rpow_nonneg (max_pos x).le q
  exact (HasPointBounds.const 0).mono (by rw [abs_zero]; positivity) (by positivity)

/-- A constant has the exponents `(0, 0)` and the constant `|k|`. -/
theorem const (k : ℝ) : IsPowerBoundOn s (fun _ ↦ k) 0 0 |k| := by
  intro x _
  have h1 : (0 : ℝ) ≤ min ‖x‖ 1 ^ ((0 : ℝ) - 1) :=
    Real.rpow_nonneg (le_min (norm_nonneg _) zero_le_one) _
  have h2 : (0 : ℝ) ≤ max ‖x‖ 1 ^ (0 : ℝ) := Real.rpow_nonneg (by positivity) _
  exact (HasPointBounds.const k).mono (by simp) (by positivity)

/-- A continuous linear functional of norm at most `1` has the exponents `(1, 1)`: `|ℓ(x)| ≤ ‖x‖ =
min(‖x‖, 1) max(‖x‖, 1)`. -/
theorem clm (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) : IsPowerBoundOn s (fun x ↦ ℓ x) 1 1 1 := by
  intro x _
  refine ⟨ℓ.differentiableAt, ?_, ?_⟩
  · calc |ℓ x| = ‖ℓ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ℓ‖ * ‖x‖ := ℓ.le_opNorm x
      _ ≤ 1 * ‖x‖ := by gcongr
      _ = 1 * min ‖x‖ 1 ^ (1 : ℝ) * max ‖x‖ 1 ^ (1 : ℝ) := by
          rw [Real.rpow_one, Real.rpow_one, mul_assoc, min_mul_max, mul_one]
  · rw [ℓ.fderiv, sub_self, Real.rpow_zero, Real.rpow_one, one_mul, one_mul]
    exact hℓ.trans (le_max_right _ _)

/-- **Powers**: `f^n` has the exponents `(n p, n q)`. -/
theorem pow (h : IsPowerBoundOn s f p q C) (hs : ∀ x ∈ s, x ≠ 0) (n : ℕ) :
    ∃ K, IsPowerBoundOn s (fun x ↦ f x ^ n) (n * p) (n * q) K := by
  induction n with
  | zero => exact ⟨|1|, by simpa using const (s := s) (1 : ℝ)⟩
  | succ n ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨2 * K * C, ?_⟩
    have h' := hK.mul h hs
    simp only [← pow_succ] at h'
    convert h' using 2 <;> push_cast <;> ring

/-- **Compact support improves the far exponent**: if `f` vanishes near every point of `s` with
`‖x‖ ≥ R₀ ≥ 1`, the far exponent `q` can be lowered to any `q' ≤ q` at the cost `R₀^{q - q'}`. -/
theorem of_eventuallyEq_zero (h : IsPowerBoundOn s f p q C) (hs : ∀ x ∈ s, x ≠ 0) {R₀ : ℝ}
    (hR₀ : 1 ≤ R₀) (hz : ∀ x ∈ s, R₀ ≤ ‖x‖ → f =ᶠ[nhds x] fun _ ↦ 0) {q' : ℝ} (hq : q' ≤ q) :
    IsPowerBoundOn s f p q' (R₀ ^ (q - q') * C) := by
  have key : ∀ x ∈ s, ‖x‖ < R₀ → ∀ a : ℝ, C * min ‖x‖ 1 ^ a * max ‖x‖ 1 ^ q ≤
      R₀ ^ (q - q') * C * min ‖x‖ 1 ^ a * max ‖x‖ 1 ^ q' := by
    intro x hx hxR a
    have hC := h.nonneg hs hx
    have hM := max_pos x
    have hMR : max ‖x‖ 1 ≤ R₀ := max_le hxR.le hR₀
    have e : max ‖x‖ 1 ^ q = max ‖x‖ 1 ^ q' * max ‖x‖ 1 ^ (q - q') := by
      rw [← Real.rpow_add hM]; ring_nf
    have h1 : max ‖x‖ 1 ^ (q - q') ≤ R₀ ^ (q - q') :=
      Real.rpow_le_rpow hM.le hMR (by linarith)
    have hm := Real.rpow_nonneg (min_pos (hs x hx)).le a
    have hq' := Real.rpow_nonneg hM.le q'
    rw [e]
    calc C * min ‖x‖ 1 ^ a * (max ‖x‖ 1 ^ q' * max ‖x‖ 1 ^ (q - q')) ≤
          C * min ‖x‖ 1 ^ a * (max ‖x‖ 1 ^ q' * R₀ ^ (q - q')) := by gcongr
      _ = R₀ ^ (q - q') * C * min ‖x‖ 1 ^ a * max ‖x‖ 1 ^ q' := by ring
  have hpos : ∀ x ∈ s, ∀ a : ℝ, 0 ≤ R₀ ^ (q - q') * C * min ‖x‖ 1 ^ a * max ‖x‖ 1 ^ q' := by
    intro x hx a
    have := h.nonneg hs hx
    have := Real.rpow_nonneg (zero_le_one.trans hR₀) (q - q')
    have := Real.rpow_nonneg (min_pos (hs x hx)).le a
    have := Real.rpow_nonneg (max_pos x).le q'
    positivity
  intro x hx
  by_cases hxR : R₀ ≤ ‖x‖
  · exact (HasPointBounds.of_eventuallyEq_zero (hz x hx hxR)).mono (hpos x hx p)
      (hpos x hx (p - 1))
  · exact (h x hx).mono (key x hx (not_le.1 hxR) p) (key x hx (not_le.1 hxR) (p - 1))

end IsPowerBoundOn

/-! ### Coordinate derivatives of products and sums -/

section Euclidean

variable {n : ℕ} {s U : Set (ℝ^n)} {f g : ℝ^n → ℝ}

/-- **The product rule for the bounds of a coordinate derivative**: on an open set `U ⊇ s` where
`f` and `g` are differentiable, bounds of `∂ₖf`, `g`, `f`, `∂ₖg` give a bound of `∂ₖ(f g)`. -/
theorem IsPowerBoundOn.partialDeriv_mul (hU : IsOpen U) (hsU : s ⊆ U) (hs : ∀ x ∈ s, x ≠ 0)
    (hf : ∀ y ∈ U, DifferentiableAt ℝ f y) (hg : ∀ y ∈ U, DifferentiableAt ℝ g y) (k : Fin n)
    {p₁ q₁ C₁ p₂ q₂ C₂ p₃ q₃ C₃ p₄ q₄ C₄ p q : ℝ}
    (h₁ : IsPowerBoundOn s (∂[k] f) p₁ q₁ C₁) (h₂ : IsPowerBoundOn s g p₂ q₂ C₂)
    (h₃ : IsPowerBoundOn s f p₃ q₃ C₃) (h₄ : IsPowerBoundOn s (∂[k] g) p₄ q₄ C₄)
    (hp₁ : p ≤ p₁ + p₂) (hp₂ : p ≤ p₃ + p₄) (hq₁ : q₁ + q₂ ≤ q) (hq₂ : q₃ + q₄ ≤ q) :
    IsPowerBoundOn s (∂[k] (fun y ↦ f y * g y)) p q (2 * C₁ * C₂ + 2 * C₃ * C₄) := by
  refine (((h₁.mul h₂ hs).mono hs hp₁ hq₁ le_rfl).add
    ((h₃.mul h₄ hs).mono hs hp₂ hq₂ le_rfl)).congr fun x hx ↦ ?_
  filter_upwards [hU.mem_nhds (hsU hx)] with y hy
  exact (PDE.partialDeriv_mul (hf y hy) (hg y hy)).symm

/-- **The sum rule for the bounds of a coordinate derivative**. -/
theorem IsPowerBoundOn.partialDeriv_add (hU : IsOpen U) (hsU : s ⊆ U)
    (hf : ∀ y ∈ U, DifferentiableAt ℝ f y) (hg : ∀ y ∈ U, DifferentiableAt ℝ g y) (k : Fin n)
    {p q C₁ C₂ : ℝ} (h₁ : IsPowerBoundOn s (∂[k] f) p q C₁)
    (h₂ : IsPowerBoundOn s (∂[k] g) p q C₂) :
    IsPowerBoundOn s (∂[k] (fun y ↦ f y + g y)) p q (C₁ + C₂) := by
  refine (h₁.add h₂).congr fun x hx ↦ ?_
  filter_upwards [hU.mem_nhds (hsU hx)] with y hy
  exact (PDE.partialDeriv_add (hf y hy) (hg y hy)).symm

/-- **A constant factor** passes through the bounds of a coordinate derivative. -/
theorem IsPowerBoundOn.partialDeriv_const_mul (k : Fin n) (a : ℝ) {p q C : ℝ}
    (h : IsPowerBoundOn s (∂[k] f) p q C) :
    IsPowerBoundOn s (∂[k] (fun y ↦ a * f y)) p q (|a| * C) :=
  (h.const_mul a).of_eq (fun y ↦ by
    rw [show (fun y ↦ a * f y) = fun y ↦ a • f y from rfl, partialDeriv_const_smul,
      smul_eq_mul]) rfl rfl rfl

end Euclidean

/-! ### Coordinates on the plane -/

section Plane

/-- The derivative of a function on the plane is bounded by twice a bound of its two partial
derivatives. -/
theorem norm_fderiv_le_two_mul {f : ℝ^2 → ℝ} {x : ℝ^2} {B : ℝ}
    (h : ∀ k : Fin 2, |(∂[k] f) x| ≤ B) : ‖fderiv ℝ f x‖ ≤ 2 * B := by
  refine (norm_fderiv_le_sum_norm_partialDeriv f x).trans ?_
  rw [Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs]
  linarith [h 0, h 1]

/-- A coordinate has the exponents `(1, 1)`. -/
theorem isPowerBoundOn_coord (s : Set (ℝ^2)) (j : Fin 2) :
    IsPowerBoundOn s (fun x ↦ x j) 1 1 1 := by
  have h := IsPowerBoundOn.clm (s := s) (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ) (by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    simpa using PiLp.norm_apply_le x j)
  simpa using h

/-- The power rule for a coordinate derivative: `∂ₖ (f^n) = n f^{n-1} ∂ₖ f`. -/
theorem partialDeriv_fun_pow (n : ℕ) {f : ℝ^2 → ℝ} {y : ℝ^2} (hf : DifferentiableAt ℝ f y)
    (k : Fin 2) : (∂[k] (fun y ↦ f y ^ n)) y = n * f y ^ (n - 1) * (∂[k] f) y := by
  change fderiv ℝ (fun y ↦ f y ^ n) y (EuclideanSpace.single k 1) =
    n * f y ^ (n - 1) * fderiv ℝ f y (EuclideanSpace.single k 1)
  rw [fderiv_fun_pow n hf]
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]

/-- `∂ₖ (x_j^n) = [k = j] n x_j^{n-1}`. -/
theorem partialDeriv_coord_pow (n : ℕ) (j k : Fin 2) (y : ℝ^2) :
    (∂[k] (fun y : ℝ^2 ↦ y j ^ n)) y = if k = j then n * y j ^ (n - 1) else 0 := by
  have hd : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y j) y :=
    (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ).differentiableAt
  rw [partialDeriv_fun_pow n hd, partialDeriv_coord]
  split_ifs <;> simp

/-- The product rule as an equality of functions, for functions differentiable everywhere. -/
theorem partialDeriv_mul_eq {f g : ℝ^2 → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (k : Fin 2) :
    ∂[k] (fun y ↦ f y * g y) = fun y ↦ (∂[k] f) y * g y + f y * (∂[k] g) y :=
  funext fun y ↦ partialDeriv_mul (hf y) (hg y)

end Plane

/-- **Compactly supported `C¹` functions** have the exponents `(0, 0)` on every set avoiding the
origin, with one constant. -/
theorem exists_isPowerBoundOn_of_hasCompactSupport {f : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∃ K, 0 ≤ K ∧ ∀ s : Set E, (∀ x ∈ s, x ≠ 0) → IsPowerBoundOn s f 0 0 K := by
  obtain ⟨A, hA⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨B, hB⟩ := (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hc.fderiv (𝕜 := ℝ))
  refine ⟨max A 0 + max B 0, by positivity, fun s hs x hx ↦
    ⟨(hf.differentiable one_ne_zero) x, ?_, ?_⟩⟩
  · rw [Real.rpow_zero, Real.rpow_zero, mul_one, mul_one, ← Real.norm_eq_abs]
    exact (hA x).trans ((le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _)))
  · have hm : 1 ≤ min ‖x‖ 1 ^ ((0 : ℝ) - 1) := by
      rw [zero_sub, Real.rpow_neg_one]
      exact one_le_inv₀ (lt_min (norm_pos_iff.2 (hs x hx)) one_pos) |>.2 (min_le_right _ _)
    rw [Real.rpow_zero, mul_one]
    have hK : B ≤ max A 0 + max B 0 :=
      (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
    have h0 : 0 ≤ max A 0 + max B 0 := by positivity
    nlinarith [hB x]

end PDE.Analysis
