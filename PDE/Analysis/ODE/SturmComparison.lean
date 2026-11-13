/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Sturm comparison for planar systems in a clock

The planar system `w' = ρ p`, `p' = ρ κ w` is, where `ρ > 0`, the equation `w_θθ = κ w` in a
clock `θ` with `θ' = ρ`. A flux equation `(D V')' = c V` with `D > 0` takes this form after the
Liouville substitution `w = D^{1/4} V`, `ρ = D^{-1/2}`, with `κ = c + (D^{1/4})_θθ / D^{1/4}`. These
two reductions are motivation and are not formalized here.

The coefficients `ρ` and `κ` are arbitrary functions, and a clock is any function `θ` with
`θ' = ρ` on `[a, b]`; no formula for them is assumed. Each result states its own hypotheses, which
are of three kinds: an ordering (`κ₁ ≤ κ₂`, or `lo² ≤ κ ≤ hi²`), signs (`ρ ≥ 0`, `κ ≥ 0`, and
`w > 0`, `p ≥ 0` at the left endpoint `a`), and a clock. Below `Δθ = θ t - θ a`, which is
nonnegative when `ρ ≥ 0`.

The Wronskian `w₁ p₂ - p₁ w₂` of solutions for `κ₁` and `κ₂` has derivative `ρ (κ₂ - κ₁) w₁ w₂`, and
`w₂/w₁` has derivative `ρ (w₁ p₂ - p₁ w₂) / w₁²` where `w₁ ≠ 0`. Comparison with the solutions
`cosh (c (θ - θ₀))` and `sinh (c (θ - θ₀))` of the constant system gives, for `ρ ≥ 0`, a clock,
`lo² ≤ κ ≤ hi²` and data `w a > 0`, `p a ≥ 0`, at every `t ∈ [a, b]`:

* growth, `w a * cosh (lo Δθ) ≤ w t`;
* for `hi > 0`, the upper bound `w t ≤ w a * cosh (hi Δθ) + p a / hi * sinh (hi Δθ)`;
* the lower direction bound `lo * sinh (lo Δθ) * w t ≤ cosh (lo Δθ) * p t`, which is
  `lo tanh (lo Δθ) ≤ p t / w t` because `cosh > 0` and `w t > 0`;
* for `hi ≥ 0`, the upper direction bound `sinh (hi Δθ) * p t ≤ hi * cosh (hi Δθ) * w t`. Where
  `hi > 0` and `θ t > θ a` it is `p t / w t ≤ hi coth (hi Δθ)`. Where `hi = 0` or `θ t = θ a` its
  left side is zero and it gives no bound on `p t / w t`. The size of `p a` does not enter.

All statements are for functions differentiable at every point of a compact interval `[a, b]`.

## Main definitions

* `Sturm.Solves`: `(w, p)` solves `w' = ρ p`, `p' = ρ κ w` on `[a, b]`.

## Main results

* `Sturm.Solves.wronskian_monotoneOn`: for `ρ ≥ 0`, `κ₁ ≤ κ₂` and `w₁, w₂ ≥ 0`, the Wronskian
  is nondecreasing.
* `Sturm.Solves.pos`: for `ρ, κ ≥ 0`, a solution with `w a > 0`, `p a ≥ 0` has `w > 0`, `p ≥ 0`
  on `[a, b]`.
* `Sturm.Solves.div_monotoneOn`: Sturm comparison. For `ρ ≥ 0`, `κ₁ ≤ κ₂`, `w₁ > 0`, `w₂ ≥ 0` and
  a nonnegative Wronskian at `a`, `w₂/w₁` is nondecreasing.
* `Sturm.Solves.cosh_le`, `Sturm.Solves.le_cosh_add_sinh`: the lower and the upper growth bound.
* `Sturm.Solves.tanh_le`, `Sturm.Solves.le_coth`: the lower and the upper direction bound, both
  written without division.
* `Sturm.Solves.energy_le`: for `ρ ≥ 0`, a clock, `lo² ≤ κ ≤ hi²` and `hi > 0`, the squared norm
  `w² + (p/hi)²` of any solution is at most `exp (2 hi Δθ)` times its value at `a`.
* `Sturm.Solves.div_add_tanh_le`: under the same hypotheses, two solutions of one system with
  `w₁ a > 0`, `p₁ a = 0`, `p₂ a ≥ 0` satisfy
  `w₂ a / w₁ a + (p₂ a / w₁ a) * tanh (hi Δθ) / hi ≤ w₂ t / w₁ t`.
* `Sturm.Solves.relative_energy_le`: under the same hypotheses, any solution grows at most like
  a reference solution with `w a > 0`, `p a ≥ 0`, with the loss `4 exp (2 (hi - lo) Δθ)` in the
  squared norm.
-/

@[expose] public section

namespace PDE.Analysis.ODE.Sturm

open Set Real

/-- A function with a nonnegative derivative at every point of `[a, b]` is nondecreasing there. -/
private theorem monotoneOn_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t) (hf' : ∀ t ∈ Icc a b, 0 ≤ f' t) :
    MonotoneOn f (Icc a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) (HasDerivAt.continuousOn hf)
    (fun t ht ↦ (hf t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht ↦ hf' t (interior_subset ht))

/-- `Solves ρ κ w p a b`: the pair `(w, p)` solves the planar system `w' = ρ p`, `p' = ρ κ w` at
every point of `[a, b]`. No sign of `ρ` or `κ` is part of the predicate. -/
structure Solves (ρ κ w p : ℝ → ℝ) (a b : ℝ) : Prop where
  /-- The first equation, `w' = ρ p`. -/
  fst : ∀ t ∈ Icc a b, HasDerivAt w (ρ t * p t) t
  /-- The second equation, `p' = ρ κ w`. -/
  snd : ∀ t ∈ Icc a b, HasDerivAt p (ρ t * κ t * w t) t

variable {ρ κ κ₁ κ₂ w p w₁ p₁ w₂ p₂ θ : ℝ → ℝ} {a b lo hi : ℝ}

/-- If `θ' = ρ` on `[a, b]`, then `w = cosh (c (θ - θ₀))`, `p = c sinh (c (θ - θ₀))` solve the
system with the constant coefficient `κ = c²` on `[a, b]`, for all real `c` and `θ₀`. -/
theorem solves_cosh (hθ : ∀ t ∈ Icc a b, HasDerivAt θ (ρ t) t) (c θ₀ : ℝ) :
    Solves ρ (fun _ ↦ c ^ 2) (fun t ↦ cosh (c * (θ t - θ₀)))
      (fun t ↦ c * sinh (c * (θ t - θ₀))) a b :=
  ⟨fun t ht ↦ (((hθ t ht).sub_const θ₀).const_mul c).cosh.congr_deriv (by ring),
    fun t ht ↦ ((((hθ t ht).sub_const θ₀).const_mul c).sinh.const_mul c).congr_deriv (by ring)⟩

/-- If `θ' = ρ` on `[a, b]`, then `w = sinh (c (θ - θ₀))`, `p = c cosh (c (θ - θ₀))` solve the
system with the constant coefficient `κ = c²` on `[a, b]`, for all real `c` and `θ₀`. -/
theorem solves_sinh (hθ : ∀ t ∈ Icc a b, HasDerivAt θ (ρ t) t) (c θ₀ : ℝ) :
    Solves ρ (fun _ ↦ c ^ 2) (fun t ↦ sinh (c * (θ t - θ₀)))
      (fun t ↦ c * cosh (c * (θ t - θ₀))) a b :=
  ⟨fun t ht ↦ (((hθ t ht).sub_const θ₀).const_mul c).sinh.congr_deriv (by ring),
    fun t ht ↦ ((((hθ t ht).sub_const θ₀).const_mul c).cosh.const_mul c).congr_deriv (by ring)⟩

namespace Solves

/-- The sum of two solutions of one system is a solution. -/
theorem add (h₁ : Solves ρ κ w₁ p₁ a b) (h₂ : Solves ρ κ w₂ p₂ a b) :
    Solves ρ κ (fun t ↦ w₁ t + w₂ t) (fun t ↦ p₁ t + p₂ t) a b :=
  ⟨fun t ht ↦ ((h₁.fst t ht).add (h₂.fst t ht)).congr_deriv (by ring),
    fun t ht ↦ ((h₁.snd t ht).add (h₂.snd t ht)).congr_deriv (by ring)⟩

/-- The difference of two solutions of one system is a solution. -/
theorem sub (h₁ : Solves ρ κ w₁ p₁ a b) (h₂ : Solves ρ κ w₂ p₂ a b) :
    Solves ρ κ (fun t ↦ w₁ t - w₂ t) (fun t ↦ p₁ t - p₂ t) a b :=
  ⟨fun t ht ↦ ((h₁.fst t ht).sub (h₂.fst t ht)).congr_deriv (by ring),
    fun t ht ↦ ((h₁.snd t ht).sub (h₂.snd t ht)).congr_deriv (by ring)⟩

/-- A constant multiple of a solution is a solution. -/
theorem const_mul (h : Solves ρ κ w p a b) (c : ℝ) :
    Solves ρ κ (fun t ↦ c * w t) (fun t ↦ c * p t) a b :=
  ⟨fun t ht ↦ ((h.fst t ht).const_mul c).congr_deriv (by ring),
    fun t ht ↦ ((h.snd t ht).const_mul c).congr_deriv (by ring)⟩

/-- If `ρ ≥ 0`, `κ₁ ≤ κ₂` and `w₁, w₂ ≥ 0` on `[a, b]`, the Wronskian `w₁ p₂ - p₁ w₂` of a solution
for `κ₁` and a solution for `κ₂` is nondecreasing on `[a, b]`: its derivative is
`ρ (κ₂ - κ₁) w₁ w₂`. -/
theorem wronskian_monotoneOn (h₁ : Solves ρ κ₁ w₁ p₁ a b) (h₂ : Solves ρ κ₂ w₂ p₂ a b)
    (hρ : ∀ t ∈ Icc a b, 0 ≤ ρ t) (hκ : ∀ t ∈ Icc a b, κ₁ t ≤ κ₂ t)
    (hw₁ : ∀ t ∈ Icc a b, 0 ≤ w₁ t) (hw₂ : ∀ t ∈ Icc a b, 0 ≤ w₂ t) :
    MonotoneOn (fun t ↦ w₁ t * p₂ t - p₁ t * w₂ t) (Icc a b) :=
  monotoneOn_of_hasDerivAt_nonneg (f' := fun t ↦ ρ t * (κ₂ t - κ₁ t) * (w₁ t * w₂ t))
    (fun t ht ↦ (((h₁.fst t ht).mul (h₂.snd t ht)).sub
      ((h₁.snd t ht).mul (h₂.fst t ht))).congr_deriv (by ring))
    (fun t ht ↦ mul_nonneg (mul_nonneg (hρ t ht) (sub_nonneg.mpr (hκ t ht)))
      (mul_nonneg (hw₁ t ht) (hw₂ t ht)))

/-- The Wronskian of two solutions of one system equals its value at `a` on all of `[a, b]`. No
sign of `ρ`, `κ` or the solutions is assumed. -/
theorem wronskian_eq (h₁ : Solves ρ κ w₁ p₁ a b) (h₂ : Solves ρ κ w₂ p₂ a b) :
    ∀ t ∈ Icc a b, w₁ t * p₂ t - p₁ t * w₂ t = w₁ a * p₂ a - p₁ a * w₂ a := by
  have hd : ∀ t ∈ Icc a b, HasDerivAt (fun s ↦ w₁ s * p₂ s - p₁ s * w₂ s) 0 t := fun t ht ↦
    (((h₁.fst t ht).mul (h₂.snd t ht)).sub ((h₁.snd t ht).mul (h₂.fst t ht))).congr_deriv
      (by ring)
  exact constant_of_has_deriv_right_zero (HasDerivAt.continuousOn hd)
    (fun t ht ↦ (hd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)

/-- At a point `t ∈ [a, b]` with `w₁ t ≠ 0`, the quotient `w₂/w₁` of the first components of two
solutions, for any `κ₁` and `κ₂`, has derivative `ρ (w₁ p₂ - p₁ w₂) / w₁²`. -/
theorem hasDerivAt_div (h₁ : Solves ρ κ₁ w₁ p₁ a b) (h₂ : Solves ρ κ₂ w₂ p₂ a b) {t : ℝ}
    (ht : t ∈ Icc a b) (hw : w₁ t ≠ 0) :
    HasDerivAt (fun s ↦ w₂ s / w₁ s) (ρ t * (w₁ t * p₂ t - p₁ t * w₂ t) / w₁ t ^ 2) t :=
  ((h₂.fst t ht).div (h₁.fst t ht) hw).congr_deriv (by ring)

/-- If `ρ ≥ 0` and `κ ≥ 0` on `[a, b]`, a solution with `w a > 0` and `p a ≥ 0` has `w > 0` and
`p ≥ 0` on all of `[a, b]`. The products `w p` and `w²` are nondecreasing, so `w` cannot vanish. -/
theorem pos (h : Solves ρ κ w p a b) (hρ : ∀ t ∈ Icc a b, 0 ≤ ρ t)
    (hκ : ∀ t ∈ Icc a b, 0 ≤ κ t) (hw : 0 < w a) (hp : 0 ≤ p a) :
    ∀ t ∈ Icc a b, 0 < w t ∧ 0 ≤ p t := by
  have hprod : MonotoneOn (fun t ↦ w t * p t) (Icc a b) :=
    monotoneOn_of_hasDerivAt_nonneg (f' := fun t ↦ ρ t * (p t ^ 2 + κ t * w t ^ 2))
      (fun t ht ↦ ((h.fst t ht).mul (h.snd t ht)).congr_deriv (by ring))
      (fun t ht ↦ mul_nonneg (hρ t ht)
        (add_nonneg (sq_nonneg _) (mul_nonneg (hκ t ht) (sq_nonneg _))))
  have hwp : ∀ t ∈ Icc a b, 0 ≤ w t * p t := fun t ht ↦
    (mul_nonneg hw.le hp).trans (hprod ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1)
  have hsq : MonotoneOn (fun t ↦ w t * w t) (Icc a b) :=
    monotoneOn_of_hasDerivAt_nonneg (f' := fun t ↦ 2 * ρ t * (w t * p t))
      (fun t ht ↦ ((h.fst t ht).mul (h.fst t ht)).congr_deriv (by ring))
      (fun t ht ↦ mul_nonneg (mul_nonneg zero_le_two (hρ t ht)) (hwp t ht))
  have hpos : ∀ t ∈ Icc a b, 0 < w t := by
    intro t ht
    by_contra hneg
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' ht.1
      ((HasDerivAt.continuousOn h.fst).mono (Icc_subset_Icc le_rfl ht.2))
      (show (0 : ℝ) ∈ Icc (w t) (w a) from ⟨not_lt.mp hneg, hw.le⟩)
    have hmono : w a * w a ≤ w c * w c :=
      hsq ⟨le_rfl, ht.1.trans ht.2⟩ ⟨hc.1, hc.2.trans ht.2⟩ hc.1
    rw [hc0] at hmono
    nlinarith
  exact fun t ht ↦ ⟨hpos t ht, nonneg_of_mul_nonneg_right (hwp t ht) (hpos t ht)⟩

/-- If `ρ ≥ 0` and `κ ≥ 0` on `[a, b]`, both components of a solution with `w a > 0` and
`p a ≥ 0` are nondecreasing on `[a, b]`. -/
theorem monotoneOn (h : Solves ρ κ w p a b) (hρ : ∀ t ∈ Icc a b, 0 ≤ ρ t)
    (hκ : ∀ t ∈ Icc a b, 0 ≤ κ t) (hw : 0 < w a) (hp : 0 ≤ p a) :
    MonotoneOn w (Icc a b) ∧ MonotoneOn p (Icc a b) :=
  have hpos := h.pos hρ hκ hw hp
  ⟨monotoneOn_of_hasDerivAt_nonneg h.fst fun t ht ↦ mul_nonneg (hρ t ht) (hpos t ht).2,
    monotoneOn_of_hasDerivAt_nonneg h.snd fun t ht ↦
      mul_nonneg (mul_nonneg (hρ t ht) (hκ t ht)) (hpos t ht).1.le⟩

/-- **Sturm comparison.** Let `ρ ≥ 0` and `κ₁ ≤ κ₂` on `[a, b]`, and let `(w₁, p₁)` and `(w₂, p₂)`
solve the systems for `κ₁` and `κ₂`, with `w₁ > 0` and `w₂ ≥ 0` on `[a, b]`. If the Wronskian
`w₁ p₂ - p₁ w₂` is nonnegative at `a`, then `w₂/w₁` is nondecreasing on `[a, b]`. -/
theorem div_monotoneOn (h₁ : Solves ρ κ₁ w₁ p₁ a b) (h₂ : Solves ρ κ₂ w₂ p₂ a b)
    (hρ : ∀ t ∈ Icc a b, 0 ≤ ρ t) (hκ : ∀ t ∈ Icc a b, κ₁ t ≤ κ₂ t)
    (hw₁ : ∀ t ∈ Icc a b, 0 < w₁ t) (hw₂ : ∀ t ∈ Icc a b, 0 ≤ w₂ t)
    (hW : 0 ≤ w₁ a * p₂ a - p₁ a * w₂ a) :
    MonotoneOn (fun t ↦ w₂ t / w₁ t) (Icc a b) := by
  have hmono := h₁.wronskian_monotoneOn h₂ hρ hκ (fun t ht ↦ (hw₁ t ht).le) hw₂
  exact monotoneOn_of_hasDerivAt_nonneg (fun t ht ↦ h₁.hasDerivAt_div h₂ ht (hw₁ t ht).ne')
    (fun t ht ↦ div_nonneg (mul_nonneg (hρ t ht)
      (hW.trans (hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1))) (sq_nonneg _))

section Clock

variable (h : Solves ρ κ w p a b) (hθ : ∀ t ∈ Icc a b, HasDerivAt θ (ρ t) t)
  (hρ : ∀ t ∈ Icc a b, 0 ≤ ρ t) (hκ : ∀ t ∈ Icc a b, lo ^ 2 ≤ κ t ∧ κ t ≤ hi ^ 2)

include hθ hρ in
/-- A clock with `θ' = ρ ≥ 0` on `[a, b]` does not run backwards: `θ a ≤ θ t` for `t ∈ [a, b]`. -/
private theorem clock_le {t : ℝ} (ht : t ∈ Icc a b) : θ a ≤ θ t :=
  monotoneOn_of_hasDerivAt_nonneg hθ hρ ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

include h hθ hρ hκ

/-- Lower direction bound. Let `ρ ≥ 0`, `θ' = ρ` and `lo² ≤ κ ≤ hi²` on `[a, b]`, and let
`w a > 0`, `p a ≥ 0`. Then `lo * sinh (lo Δθ) * w t ≤ cosh (lo Δθ) * p t` for every `t ∈ [a, b]`,
with `Δθ = θ t - θ a`. Since `cosh > 0` and `w t > 0` (`Solves.pos`), this is
`lo tanh (lo Δθ) ≤ p t / w t`. Only the lower bound `lo² ≤ κ` is used. -/
theorem tanh_le (hw : 0 < w a) (hp : 0 ≤ p a) : ∀ t ∈ Icc a b,
    lo * sinh (lo * (θ t - θ a)) * w t ≤ cosh (lo * (θ t - θ a)) * p t := by
  have hκ0 : ∀ t ∈ Icc a b, 0 ≤ κ t := fun t ht ↦ (sq_nonneg lo).trans (hκ t ht).1
  have hmono := (solves_cosh hθ lo (θ a)).wronskian_monotoneOn h hρ (fun t ht ↦ (hκ t ht).1)
    (fun t _ ↦ (cosh_pos _).le) (fun t ht ↦ (h.pos hρ hκ0 hw hp t ht).1.le)
  intro t ht
  have hW := hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  simp only [sub_self, mul_zero, cosh_zero, sinh_zero, one_mul, zero_mul, sub_zero] at hW
  linarith

/-- Upper direction bound. Let `ρ ≥ 0`, `θ' = ρ` and `lo² ≤ κ ≤ hi²` on `[a, b]`, with `hi ≥ 0`,
and let `w a > 0`, `p a ≥ 0`. Then `sinh (hi Δθ) * p t ≤ hi * cosh (hi Δθ) * w t` for every
`t ∈ [a, b]`, with `Δθ = θ t - θ a ≥ 0`. Where `hi > 0` and `θ t > θ a`, both `sinh (hi Δθ)` and
`w t` are positive and this is `p t / w t ≤ hi coth (hi Δθ)`. Where `hi = 0` or `θ t = θ a`, the
left side is zero and the inequality gives no bound on `p t / w t`. The value `p a` enters only
through its sign. -/
theorem le_coth (hhi : 0 ≤ hi) (hw : 0 < w a) (hp : 0 ≤ p a) : ∀ t ∈ Icc a b,
    sinh (hi * (θ t - θ a)) * p t ≤ hi * cosh (hi * (θ t - θ a)) * w t := by
  have hκ0 : ∀ t ∈ Icc a b, 0 ≤ κ t := fun t ht ↦ (sq_nonneg lo).trans (hκ t ht).1
  have hmono := h.wronskian_monotoneOn (solves_sinh hθ hi (θ a)) hρ (fun t ht ↦ (hκ t ht).2)
    (fun t ht ↦ (h.pos hρ hκ0 hw hp t ht).1.le)
    (fun t ht ↦ sinh_nonneg_iff.mpr (mul_nonneg hhi (sub_nonneg.mpr (clock_le hθ hρ ht))))
  intro t ht
  have hW := hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  simp only [sub_self, mul_zero, cosh_zero, sinh_zero, mul_one, sub_zero] at hW
  nlinarith [mul_nonneg hhi hw.le]

/-- Growth. Let `ρ ≥ 0`, `θ' = ρ` and `lo² ≤ κ ≤ hi²` on `[a, b]`, and let `w a > 0`, `p a ≥ 0`.
Then `w a * cosh (lo Δθ) ≤ w t` for every `t ∈ [a, b]`, with `Δθ = θ t - θ a`. Only the lower
bound `lo² ≤ κ` is used. -/
theorem cosh_le (hw : 0 < w a) (hp : 0 ≤ p a) : ∀ t ∈ Icc a b,
    w a * cosh (lo * (θ t - θ a)) ≤ w t := by
  have hκ0 : ∀ t ∈ Icc a b, 0 ≤ κ t := fun t ht ↦ (sq_nonneg lo).trans (hκ t ht).1
  have hmono := (solves_cosh hθ lo (θ a)).div_monotoneOn h hρ (fun t ht ↦ (hκ t ht).1)
    (fun t _ ↦ cosh_pos _) (fun t ht ↦ (h.pos hρ hκ0 hw hp t ht).1.le)
    (by simpa using hp)
  intro t ht
  have hW := hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  simp only [sub_self, mul_zero, cosh_zero, div_one] at hW
  exact (le_div_iff₀ (cosh_pos _)).mp hW

/-- Upper bound. Let `ρ ≥ 0`, `θ' = ρ` and `lo² ≤ κ ≤ hi²` on `[a, b]`, with `hi > 0`, and let
`w a > 0`, `p a ≥ 0`. Then `w t ≤ w a * cosh (hi Δθ) + p a / hi * sinh (hi Δθ)` for every
`t ∈ [a, b]`, with `Δθ = θ t - θ a`. -/
theorem le_cosh_add_sinh (hhi : 0 < hi) (hw : 0 < w a) (hp : 0 ≤ p a) : ∀ t ∈ Icc a b,
    w t ≤ w a * cosh (hi * (θ t - θ a)) + p a / hi * sinh (hi * (θ t - θ a)) := by
  have hκ0 : ∀ t ∈ Icc a b, 0 ≤ κ t := fun t ht ↦ (sq_nonneg lo).trans (hκ t ht).1
  have hpos := h.pos hρ hκ0 hw hp
  have hmodel := ((solves_cosh hθ hi (θ a)).const_mul (w a)).add
    ((solves_sinh hθ hi (θ a)).const_mul (p a / hi))
  have hmono := h.div_monotoneOn hmodel hρ (fun t ht ↦ (hκ t ht).2) (fun t ht ↦ (hpos t ht).1)
    (fun t ht ↦ add_nonneg (mul_nonneg hw.le (cosh_pos _).le)
      (mul_nonneg (div_nonneg hp hhi.le)
        (sinh_nonneg_iff.mpr (mul_nonneg hhi.le (sub_nonneg.mpr (clock_le hθ hρ ht))))))
    (by simp only [sub_self, mul_zero, cosh_zero, sinh_zero, mul_one, add_zero, zero_add]
        rw [div_mul_cancel₀ _ hhi.ne']
        linarith)
  intro t ht
  have hW := hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  simp only [sub_self, mul_zero, cosh_zero, sinh_zero, mul_one, add_zero] at hW
  rw [div_self hw.ne'] at hW
  exact (one_le_div (hpos t ht).1).mp hW

/-- Let `ρ ≥ 0`, `θ' = ρ` and `lo² ≤ κ ≤ hi²` on `[a, b]`, with `hi > 0`. For every solution, with
no sign condition on its data, and every `t ∈ [a, b]`, with `Δθ = θ t - θ a`,
`w t ^ 2 + (p t / hi) ^ 2 ≤ exp (2 hi Δθ) * (w a ^ 2 + (p a / hi) ^ 2)`. -/
theorem energy_le (hhi : 0 < hi) : ∀ t ∈ Icc a b,
    w t ^ 2 + (p t / hi) ^ 2 ≤ exp (2 * hi * (θ t - θ a)) * (w a ^ 2 + (p a / hi) ^ 2) := by
  have hanti : AntitoneOn
      (fun t ↦ exp (-2 * hi * θ t) * (w t * w t + p t / hi * (p t / hi))) (Icc a b) := by
    have hd : ∀ t ∈ Icc a b, HasDerivAt
        (fun s ↦ exp (-2 * hi * θ s) * (w s * w s + p s / hi * (p s / hi)))
        (exp (-2 * hi * θ t) * (2 * ρ t *
          (w t * p t + p t / hi * (κ t / hi * w t) - hi * (w t * w t + p t / hi * (p t / hi)))))
        t := fun t ht ↦
      ((((hθ t ht).const_mul (-2 * hi)).exp).mul (((h.fst t ht).mul (h.fst t ht)).add
        (((h.snd t ht).div_const hi).mul ((h.snd t ht).div_const hi)))).congr_deriv
          (by simp only [Pi.add_apply, Pi.mul_apply]; ring)
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) (HasDerivAt.continuousOn hd)
      (fun t ht ↦ (hd t (interior_subset ht)).hasDerivWithinAt) (fun t ht ↦ ?_)
    have hti := interior_subset ht
    have hk0 : 0 ≤ κ t / hi := div_nonneg ((sq_nonneg lo).trans (hκ t hti).1) hhi.le
    have hk : κ t / hi ≤ hi := (div_le_iff₀ hhi).mpr (by nlinarith [(hκ t hti).2])
    have hkey : w t * p t + p t / hi * (κ t / hi * w t) ≤
        hi * (w t * w t + p t / hi * (p t / hi)) := by
      have hp : p t = hi * (p t / hi) := by field_simp
      generalize p t / hi = v at hp ⊢
      rw [hp]
      obtain hwv | hwv := le_total 0 (w t * v)
      · nlinarith [sq_nonneg (w t - v), mul_le_mul_of_nonneg_left hk hwv]
      · nlinarith [sq_nonneg (w t + v), mul_nonpos_of_nonpos_of_nonneg hwv hk0,
          mul_nonneg hhi.le (mul_self_nonneg (w t + v))]
    exact mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg zero_le_two (hρ t hti)) (by linarith))
  intro t ht
  have hG := hanti ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  have hsplit : exp (2 * hi * (θ t - θ a)) = exp (2 * hi * θ t) * exp (-2 * hi * θ a) := by
    rw [← exp_add]
    ring_nf
  have hcancel : exp (2 * hi * θ t) * exp (-2 * hi * θ t) = 1 := by
    rw [← exp_add]
    ring_nf
    exact exp_zero
  have hscaled := mul_le_mul_of_nonneg_left hG (exp_pos (2 * hi * θ t)).le
  rw [hsplit]
  calc w t ^ 2 + (p t / hi) ^ 2
      = exp (2 * hi * θ t) * exp (-2 * hi * θ t) * (w t * w t + p t / hi * (p t / hi)) := by
        rw [hcancel]
        ring
    _ ≤ exp (2 * hi * θ t) * exp (-2 * hi * θ a) * (w a ^ 2 + (p a / hi) ^ 2) := by
        nlinarith [hscaled]

end Clock

/-- **Relative propagator.** Let `ρ ≥ 0`, `θ' = ρ` and `lo² ≤ κ ≤ hi²` on `[a, b]`, with `hi > 0`.
Let `(w, p)` be a reference solution with `w a > 0`, `p a ≥ 0`, and let `(y, q)` be any solution
of the same system. Then for every `t ∈ [a, b]`, with `Δθ = θ t - θ a`, the squared norm
`y t ^ 2 + (q t / hi) ^ 2` is at most
`4 exp (2 (hi - lo) Δθ) * (w t / w a) ^ 2 * (y a ^ 2 + (q a / hi) ^ 2)`. -/
theorem relative_energy_le {y q : ℝ → ℝ} (h : Solves ρ κ w p a b) (hy : Solves ρ κ y q a b)
    (hθ : ∀ t ∈ Icc a b, HasDerivAt θ (ρ t) t) (hρ : ∀ t ∈ Icc a b, 0 ≤ ρ t)
    (hκ : ∀ t ∈ Icc a b, lo ^ 2 ≤ κ t ∧ κ t ≤ hi ^ 2) (hhi : 0 < hi)
    (hw : 0 < w a) (hp : 0 ≤ p a) : ∀ t ∈ Icc a b,
    y t ^ 2 + (q t / hi) ^ 2 ≤ 4 * exp (2 * (hi - lo) * (θ t - θ a)) * (w t / w a) ^ 2 *
      (y a ^ 2 + (q a / hi) ^ 2) := by
  intro t ht
  have hE := hy.energy_le hθ hρ hκ hhi t ht
  have hgrow := h.cosh_le hθ hρ hκ hw hp t ht
  have hratio : exp (lo * (θ t - θ a)) ≤ 2 * (w t / w a) := by
    have hc : cosh (lo * (θ t - θ a)) ≤ w t / w a := (le_div_iff₀' hw).mpr hgrow
    rw [cosh_eq] at hc
    linarith [exp_pos (-(lo * (θ t - θ a)))]
  have hsq : exp (2 * lo * (θ t - θ a)) ≤ 4 * (w t / w a) ^ 2 := by
    have he : exp (2 * lo * (θ t - θ a)) = exp (lo * (θ t - θ a)) ^ 2 := by
      rw [sq, ← exp_add]
      ring_nf
    rw [he]
    nlinarith [exp_pos (lo * (θ t - θ a))]
  have hsplit : exp (2 * hi * (θ t - θ a)) =
      exp (2 * (hi - lo) * (θ t - θ a)) * exp (2 * lo * (θ t - θ a)) := by
    rw [← exp_add]
    ring_nf
  rw [hsplit] at hE
  have hE0 : 0 ≤ y a ^ 2 + (q a / hi) ^ 2 := by positivity
  have hstep := mul_le_mul_of_nonneg_left hsq (exp_pos (2 * (hi - lo) * (θ t - θ a))).le
  calc y t ^ 2 + (q t / hi) ^ 2
      ≤ exp (2 * (hi - lo) * (θ t - θ a)) * exp (2 * lo * (θ t - θ a)) *
          (y a ^ 2 + (q a / hi) ^ 2) := hE
    _ ≤ exp (2 * (hi - lo) * (θ t - θ a)) * (4 * (w t / w a) ^ 2) *
          (y a ^ 2 + (q a / hi) ^ 2) := mul_le_mul_of_nonneg_right hstep hE0
    _ = _ := by ring

/-- **Separation of two solutions.** Let `ρ ≥ 0`, `θ' = ρ` and `lo² ≤ κ ≤ hi²` on `[a, b]`, with
`hi > 0`. Let `(w₁, p₁)` and `(w₂, p₂)` solve this one system, with `w₁ a > 0`, `p₁ a = 0` and
`p₂ a ≥ 0`. Then for every `t ∈ [a, b]`, with `Δθ = θ t - θ a`, `w₂ t / w₁ t` exceeds
`w₂ a / w₁ a` by at least `(p₂ a / w₁ a) * tanh (hi Δθ) / hi`. The statement writes
`tanh (hi Δθ) / hi` as `sinh (hi Δθ) / (hi * cosh (hi Δθ))`. -/
theorem div_add_tanh_le (h₁ : Solves ρ κ w₁ p₁ a b) (h₂ : Solves ρ κ w₂ p₂ a b)
    (hθ : ∀ t ∈ Icc a b, HasDerivAt θ (ρ t) t) (hρ : ∀ t ∈ Icc a b, 0 ≤ ρ t)
    (hκ : ∀ t ∈ Icc a b, lo ^ 2 ≤ κ t ∧ κ t ≤ hi ^ 2) (hhi : 0 < hi)
    (hw₁ : 0 < w₁ a) (hp₁ : p₁ a = 0) (hp₂ : 0 ≤ p₂ a) : ∀ t ∈ Icc a b,
    w₂ a / w₁ a + p₂ a / w₁ a * (sinh (hi * (θ t - θ a)) / (hi * cosh (hi * (θ t - θ a)))) ≤
      w₂ t / w₁ t := by
  have hκ0 : ∀ t ∈ Icc a b, 0 ≤ κ t := fun t ht ↦ (sq_nonneg lo).trans (hκ t ht).1
  have hpos := h₁.pos hρ hκ0 hw₁ hp₁.ge
  have hupper := h₁.le_cosh_add_sinh hθ hρ hκ hhi hw₁ hp₁.ge
  have hW := h₁.wronskian_eq h₂
  have hmodel : ∀ t ∈ Icc a b, HasDerivAt
      (fun s ↦ sinh (hi * (θ s - θ a)) / (hi * cosh (hi * (θ s - θ a))))
      (ρ t / cosh (hi * (θ t - θ a)) ^ 2) t := by
    intro t ht
    have harg := ((hθ t ht).sub_const (θ a)).const_mul hi
    have hc := cosh_pos (hi * (θ t - θ a))
    refine (harg.sinh.div (harg.cosh.const_mul hi) (mul_pos hhi hc).ne').congr_deriv ?_
    rw [div_eq_div_iff (pow_pos (mul_pos hhi hc) 2).ne' (pow_pos hc 2).ne']
    linear_combination (hi ^ 2 * ρ t * cosh (hi * (θ t - θ a)) ^ 2) *
      cosh_sq (hi * (θ t - θ a))
  have hmono : MonotoneOn (fun t ↦ w₂ t / w₁ t -
      p₂ a / w₁ a * (sinh (hi * (θ t - θ a)) / (hi * cosh (hi * (θ t - θ a))))) (Icc a b) := by
    refine monotoneOn_of_hasDerivAt_nonneg
      (fun t ht ↦ (h₁.hasDerivAt_div h₂ ht (hpos t ht).1.ne').sub
        ((hmodel t ht).const_mul (p₂ a / w₁ a))) (fun t ht ↦ ?_)
    have hc := cosh_pos (hi * (θ t - θ a))
    have hwt := (hpos t ht).1
    have hle : w₁ t ≤ w₁ a * cosh (hi * (θ t - θ a)) := by
      simpa [hp₁] using hupper t ht
    have hsq : w₁ t ^ 2 ≤ (w₁ a * cosh (hi * (θ t - θ a))) ^ 2 :=
      pow_le_pow_left₀ hwt.le hle 2
    rw [hW t ht, hp₁, zero_mul, sub_zero]
    have hfrac : p₂ a / w₁ a * (ρ t / cosh (hi * (θ t - θ a)) ^ 2) ≤
        ρ t * (w₁ a * p₂ a) / w₁ t ^ 2 := by
      rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hw₁ (pow_pos hc 2)) (pow_pos hwt 2)]
      nlinarith [mul_nonneg (mul_nonneg hp₂ (hρ t ht)) hw₁.le,
        mul_le_mul_of_nonneg_left hsq (mul_nonneg (mul_nonneg hp₂ (hρ t ht)) hw₁.le)]
    linarith
  intro t ht
  have hm := hmono ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  simp only [sub_self, mul_zero, sinh_zero, zero_div, sub_zero] at hm
  linarith

end Solves

end PDE.Analysis.ODE.Sturm
