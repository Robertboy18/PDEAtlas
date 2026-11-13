/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Formulas for the classical linear equations in one space dimension

Functions of `(t, x)` are curried, `u : ℝ → ℝ → ℝ`, and the partial derivatives are the
derivatives of the partial functions, `deriv (fun s ↦ u s x) t` and `deriv (fun y ↦ u t y) x`.

* Transport `u_t + c u_x + d u = 0`, `u (0, x) = g x`: the differentiable solutions are exactly
  `u = e ^ (-d t) g (x - c t)` (`transport_iff`), since `e ^ (d s) u (s, x - c t + c s)` is
  constant along each characteristic.
* Heat `u_t = κ u_xx` on `[0, L]` with `u (t, 0) = u (t, L) = 0`: the finite sum
  `∑ b e ^ (-κ ω ^ 2 t) sin (ω x)` with `sin (ω L) = 0` solves the problem with initial value
  `∑ b sin (ω x)` (`heatSum_solves`).
* Wave `u_tt = c ^ 2 u_xx` on `[0, L]` with the same boundary values:
  `∑ (a cos (c ω t) + b / (c ω) sin (c ω t)) sin (ω x)` with initial values `∑ a sin (ω x)`,
  `∑ b sin (ω x)` (`waveSum_solves`).
* Wave on the line: d'Alembert's formula `(f (x + c t) + f (x - c t)) / 2 +
  (G (x + c t) - G (x - c t)) / (2 c)` with `G' = g` (`dalembert_solves`).
-/

@[expose] public section

namespace CAS.ClassicalPDE

open Real

/-! ## Partial derivatives through the uncurried function -/

theorem hasDerivAt_char {u : ℝ → ℝ → ℝ} (hu : Differentiable ℝ (Function.uncurry u))
    (a c s : ℝ) : HasDerivAt (fun s ↦ u s (a + c * s))
      (fderiv ℝ (Function.uncurry u) (s, a + c * s) (1, c)) s := by
  have hγ : HasDerivAt (fun s : ℝ ↦ (s, a + c * s)) (1, c) s := by
    have h2 := ((hasDerivAt_id' s).const_mul c).const_add a
    convert (hasDerivAt_id' s).prodMk h2 using 1
    simp
  exact (hu _).hasFDerivAt.comp_hasDerivAt s hγ

theorem deriv_t {u : ℝ → ℝ → ℝ} (hu : Differentiable ℝ (Function.uncurry u)) (t x : ℝ) :
    deriv (fun s ↦ u s x) t = fderiv ℝ (Function.uncurry u) (t, x) (1, 0) := by
  have hγ : HasDerivAt (fun s : ℝ ↦ (s, x)) (1, 0) t :=
    (hasDerivAt_id' t).prodMk (hasDerivAt_const t x)
  exact ((hu _).hasFDerivAt.comp_hasDerivAt t hγ).deriv

theorem deriv_x {u : ℝ → ℝ → ℝ} (hu : Differentiable ℝ (Function.uncurry u)) (t x : ℝ) :
    deriv (fun y ↦ u t y) x = fderiv ℝ (Function.uncurry u) (t, x) (0, 1) := by
  have hγ : HasDerivAt (fun y : ℝ ↦ (t, y)) (0, 1) x :=
    (hasDerivAt_const x t).prodMk (hasDerivAt_id' x)
  exact ((hu _).hasFDerivAt.comp_hasDerivAt x hγ).deriv

/-! ## Transport -/

/-- The differentiable solutions of `u_t + c u_x + d u = 0` with `u (0, x) = g x`. -/
theorem transport_iff (c d : ℝ) {g : ℝ → ℝ} (hg : Differentiable ℝ g) {u : ℝ → ℝ → ℝ}
    (hu : Differentiable ℝ (Function.uncurry u)) :
    ((∀ t x, deriv (fun s ↦ u s x) t + c * deriv (fun y ↦ u t y) x + d * u t x = 0) ∧
        ∀ x, u 0 x = g x) ↔ ∀ t x, u t x = exp (-(d * t)) * g (x - c * t) := by
  constructor
  · rintro ⟨hpde, h0⟩ t x
    set a := x - c * t
    set φ : ℝ → ℝ := fun s ↦ exp (d * s) * u s (a + c * s) with hφ
    have hφd : ∀ s, HasDerivAt φ 0 s := by
      intro s
      have h1 := ((hasDerivAt_id' s).const_mul d).exp
      have h2 := hasDerivAt_char hu a c s
      have := h1.mul h2
      convert this using 1
      have hp := hpde s (a + c * s)
      rw [deriv_t hu, deriv_x hu] at hp
      have hlin : fderiv ℝ (Function.uncurry u) (s, a + c * s) (1, c) =
          fderiv ℝ (Function.uncurry u) (s, a + c * s) (1, 0) +
            c * fderiv ℝ (Function.uncurry u) (s, a + c * s) (0, 1) := by
        rw [show ((1 : ℝ), c) = (1, 0) + c • (0, 1) by simp, map_add, map_smul, smul_eq_mul]
      rw [hlin]
      have : exp (d * s) * (d * 1) * u s (a + c * s) + exp (d * s) *
          (fderiv ℝ (Function.uncurry u) (s, a + c * s) (1, 0) +
            c * fderiv ℝ (Function.uncurry u) (s, a + c * s) (0, 1)) =
          exp (d * s) * (fderiv ℝ (Function.uncurry u) (s, a + c * s) (1, 0) +
            c * fderiv ℝ (Function.uncurry u) (s, a + c * s) (0, 1) + d * u s (a + c * s)) := by
        ring
      rw [this, hp, mul_zero]
    have hconst := is_const_of_deriv_eq_zero (fun s ↦ (hφd s).differentiableAt)
      (fun s ↦ (hφd s).deriv) t 0
    simp only [hφ, mul_zero, add_zero, exp_zero, one_mul] at hconst
    have hx : a + c * t = x := by simp [a]
    rw [hx, h0] at hconst
    have hinv : exp (-(d * t)) * exp (d * t) = 1 := by rw [← exp_add]; simp
    calc u t x = exp (-(d * t)) * (exp (d * t) * u t x) := by
          rw [← mul_assoc, hinv, one_mul]
      _ = exp (-(d * t)) * g (x - c * t) := by rw [hconst]
  · intro h
    have hu' : u = fun t x ↦ exp (-(d * t)) * g (x - c * t) := funext fun t ↦ funext (h t)
    subst hu'
    refine ⟨fun t x ↦ ?_, fun x ↦ by simp⟩
    have ht : HasDerivAt (fun s ↦ exp (-(d * s)) * g (x - c * s))
        (exp (-(d * t)) * (-(d * 1)) * g (x - c * t) +
          exp (-(d * t)) * (deriv g (x - c * t) * (0 - c * 1))) t := by
      have h1 := ((hasDerivAt_id' t).const_mul d).fun_neg.exp
      have h2 := (hg (x - c * t)).hasDerivAt.comp t
        ((hasDerivAt_const t x).sub ((hasDerivAt_id' t).const_mul c))
      exact h1.mul h2
    have hx : HasDerivAt (fun y ↦ exp (-(d * t)) * g (y - c * t))
        (exp (-(d * t)) * (deriv g (x - c * t) * 1)) x := by
      have h2 := (hg (x - c * t)).hasDerivAt.comp x ((hasDerivAt_id' x).sub_const (c * t))
      exact h2.const_mul _
    rw [ht.deriv, hx.deriv]
    ring

/-! ## Finite sums of functions -/

theorem hasDerivAt_list_sum {α : Type*} (L : List α) (f : α → ℝ → ℝ) (f' : α → ℝ) (x : ℝ)
    (h : ∀ e ∈ L, HasDerivAt (f e) (f' e) x) :
    HasDerivAt (fun y ↦ (L.map fun e ↦ f e y).sum) (L.map f').sum x := by
  induction L with
  | nil => simpa using hasDerivAt_const x (0 : ℝ)
  | cons e L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h e (by simp)).add (ih fun e' he' ↦ h e' (by simp [he']))

/-! ## Heat equation on an interval -/

/-- `b e ^ (-κ ω ^ 2 t) sin (ω x)`. -/
noncomputable def heatTerm (κ b ω t x : ℝ) : ℝ := b * exp (-(κ * ω ^ 2 * t)) * sin (ω * x)

/-- `∑ b e ^ (-κ ω ^ 2 t) sin (ω x)` over pairs `(b, ω)`. -/
noncomputable def heatSum (κ : ℝ) (terms : List (ℝ × ℝ)) (t x : ℝ) : ℝ :=
  (terms.map fun e ↦ heatTerm κ e.1 e.2 t x).sum

theorem heatSum_solves (κ L : ℝ) (terms : List (ℝ × ℝ))
    (hL : ∀ e ∈ terms, sin (e.2 * L) = 0) :
    (∀ t x, deriv (fun s ↦ heatSum κ terms s x) t =
        κ * deriv (fun y ↦ deriv (fun z ↦ heatSum κ terms t z) y) x) ∧
      (∀ t, heatSum κ terms t 0 = 0) ∧ (∀ t, heatSum κ terms t L = 0) ∧
      ∀ x, heatSum κ terms 0 x = (terms.map fun e ↦ e.1 * sin (e.2 * x)).sum := by
  refine ⟨fun t x ↦ ?_, fun t ↦ ?_, fun t ↦ ?_, fun x ↦ ?_⟩
  · have ht := hasDerivAt_list_sum terms (fun e s ↦ heatTerm κ e.1 e.2 s x)
      (fun e ↦ -(κ * e.2 ^ 2) * heatTerm κ e.1 e.2 t x) t fun e _ ↦ by
        change HasDerivAt (fun s ↦ e.1 * exp (-(κ * e.2 ^ 2 * s)) * sin (e.2 * x)) _ t
        have := ((((hasDerivAt_id' t).const_mul (κ * e.2 ^ 2)).fun_neg.exp).const_mul e.1).mul_const
          (sin (e.2 * x))
        exact this.congr_deriv (by unfold heatTerm; ring)
    have hx₁ : ∀ y, HasDerivAt (fun z ↦ heatSum κ terms t z)
        (terms.map fun e ↦ e.1 * exp (-(κ * e.2 ^ 2 * t)) * (e.2 * cos (e.2 * y))).sum y :=
      fun y ↦ hasDerivAt_list_sum terms (fun e z ↦ heatTerm κ e.1 e.2 t z) _ y fun e _ ↦ by
        change HasDerivAt (fun z ↦ e.1 * exp (-(κ * e.2 ^ 2 * t)) * sin (e.2 * z)) _ y
        have := (((hasDerivAt_id' y).const_mul e.2).sin).const_mul
          (e.1 * exp (-(κ * e.2 ^ 2 * t)))
        exact this.congr_deriv (by ring)
    have hx₂ := hasDerivAt_list_sum terms
      (fun e y ↦ e.1 * exp (-(κ * e.2 ^ 2 * t)) * (e.2 * cos (e.2 * y)))
      (fun e ↦ -(e.2 ^ 2) * heatTerm κ e.1 e.2 t x) x fun e _ ↦ by
        have := ((((hasDerivAt_id' x).const_mul e.2).cos).const_mul e.2).const_mul
          (e.1 * exp (-(κ * e.2 ^ 2 * t)))
        exact this.congr_deriv (by unfold heatTerm; ring)
    have e₁ : deriv (fun z ↦ heatSum κ terms t z) = fun y ↦
        (terms.map fun e ↦ e.1 * exp (-(κ * e.2 ^ 2 * t)) * (e.2 * cos (e.2 * y))).sum :=
      funext fun y ↦ (hx₁ y).deriv
    rw [show (fun s ↦ heatSum κ terms s x) =
      fun s ↦ (terms.map fun e ↦ heatTerm κ e.1 e.2 s x).sum from rfl, ht.deriv, e₁, hx₂.deriv,
      ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro e _
    ring
  · simp [heatSum, heatTerm]
  · unfold heatSum
    rw [show (terms.map fun e ↦ heatTerm κ e.1 e.2 t L) = terms.map fun _ ↦ (0 : ℝ) from
      List.map_congr_left fun e he ↦ by simp [heatTerm, hL e he]]
    simp
  · simp [heatSum, heatTerm]

/-! ## Wave equation on an interval -/

/-- `(a cos (c ω t) + b / (c ω) sin (c ω t)) sin (ω x)`. -/
noncomputable def waveTerm (c a b ω t x : ℝ) : ℝ :=
  (a * cos (c * ω * t) + b / (c * ω) * sin (c * ω * t)) * sin (ω * x)

/-- The sum of `waveTerm` over triples `(a, b, ω)`. -/
noncomputable def waveSum (c : ℝ) (terms : List (ℝ × ℝ × ℝ)) (t x : ℝ) : ℝ :=
  (terms.map fun e ↦ waveTerm c e.1 e.2.1 e.2.2 t x).sum

theorem waveSum_solves (c L : ℝ) (terms : List (ℝ × ℝ × ℝ))
    (hω : ∀ e ∈ terms, c * e.2.2 ≠ 0) (hL : ∀ e ∈ terms, sin (e.2.2 * L) = 0) :
    (∀ t x, deriv (fun s ↦ deriv (fun r ↦ waveSum c terms r x) s) t =
        c ^ 2 * deriv (fun y ↦ deriv (fun z ↦ waveSum c terms t z) y) x) ∧
      (∀ t, waveSum c terms t 0 = 0) ∧ (∀ t, waveSum c terms t L = 0) ∧
      (∀ x, waveSum c terms 0 x = (terms.map fun e ↦ e.1 * sin (e.2.2 * x)).sum) ∧
      ∀ x, deriv (fun s ↦ waveSum c terms s x) 0 =
        (terms.map fun e ↦ e.2.1 * sin (e.2.2 * x)).sum := by
  -- First and second derivatives in `t`.
  have ht₁ : ∀ x s, HasDerivAt (fun r ↦ waveSum c terms r x)
      (terms.map fun e ↦ (-(e.1 * (c * e.2.2)) * sin (c * e.2.2 * s) +
        e.2.1 * cos (c * e.2.2 * s)) * sin (e.2.2 * x)).sum s := fun x s ↦
    hasDerivAt_list_sum terms (fun e r ↦ waveTerm c e.1 e.2.1 e.2.2 r x) _ s fun e he ↦ by
      have hne := hω e he
      have hc0 : c ≠ 0 := left_ne_zero_of_mul hne
      have hω0 : e.2.2 ≠ 0 := right_ne_zero_of_mul hne
      have h1 := ((hasDerivAt_id' s).const_mul (c * e.2.2)).cos.const_mul e.1
      have h2 := ((hasDerivAt_id' s).const_mul (c * e.2.2)).sin.const_mul (e.2.1 / (c * e.2.2))
      exact ((h1.add h2).mul_const (sin (e.2.2 * x))).congr_deriv (by field_simp)
  have ht₂ : ∀ x t, HasDerivAt (fun s ↦ (terms.map fun e ↦ (-(e.1 * (c * e.2.2)) *
        sin (c * e.2.2 * s) + e.2.1 * cos (c * e.2.2 * s)) * sin (e.2.2 * x)).sum)
      (terms.map fun e ↦ -(c * e.2.2) ^ 2 * waveTerm c e.1 e.2.1 e.2.2 t x).sum t := fun x t ↦
    hasDerivAt_list_sum terms _ _ t fun e he ↦ by
      have hne := hω e he
      have hc0 : c ≠ 0 := left_ne_zero_of_mul hne
      have hω0 : e.2.2 ≠ 0 := right_ne_zero_of_mul hne
      have h1 := ((hasDerivAt_id' t).const_mul (c * e.2.2)).sin.const_mul (-(e.1 * (c * e.2.2)))
      have h2 := ((hasDerivAt_id' t).const_mul (c * e.2.2)).cos.const_mul e.2.1
      exact ((h1.add h2).mul_const (sin (e.2.2 * x))).congr_deriv (by
        unfold waveTerm
        field_simp
        ring)
  -- First and second derivatives in `x`.
  have hx₁ : ∀ t y, HasDerivAt (fun z ↦ waveSum c terms t z)
      (terms.map fun e ↦ (e.1 * cos (c * e.2.2 * t) + e.2.1 / (c * e.2.2) *
        sin (c * e.2.2 * t)) * (e.2.2 * cos (e.2.2 * y))).sum y := fun t y ↦
    hasDerivAt_list_sum terms (fun e z ↦ waveTerm c e.1 e.2.1 e.2.2 t z) _ y fun e _ ↦ by
      have := (((hasDerivAt_id' y).const_mul e.2.2).sin).const_mul
        (e.1 * cos (c * e.2.2 * t) + e.2.1 / (c * e.2.2) * sin (c * e.2.2 * t))
      exact this.congr_deriv (by ring)
  have hx₂ : ∀ t x, HasDerivAt (fun y ↦ (terms.map fun e ↦ (e.1 * cos (c * e.2.2 * t) +
        e.2.1 / (c * e.2.2) * sin (c * e.2.2 * t)) * (e.2.2 * cos (e.2.2 * y))).sum)
      (terms.map fun e ↦ -(e.2.2 ^ 2) * waveTerm c e.1 e.2.1 e.2.2 t x).sum x := fun t x ↦
    hasDerivAt_list_sum terms _ _ x fun e _ ↦ by
      have := ((((hasDerivAt_id' x).const_mul e.2.2).cos).const_mul e.2.2).const_mul
        (e.1 * cos (c * e.2.2 * t) + e.2.1 / (c * e.2.2) * sin (c * e.2.2 * t))
      exact this.congr_deriv (by unfold waveTerm; ring)
  refine ⟨fun t x ↦ ?_, fun t ↦ ?_, fun t ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · have e₁ : deriv (fun r ↦ waveSum c terms r x) = fun s ↦ (terms.map fun e ↦
        (-(e.1 * (c * e.2.2)) * sin (c * e.2.2 * s) + e.2.1 * cos (c * e.2.2 * s)) *
          sin (e.2.2 * x)).sum := funext fun s ↦ (ht₁ x s).deriv
    have e₂ : deriv (fun z ↦ waveSum c terms t z) = fun y ↦ (terms.map fun e ↦
        (e.1 * cos (c * e.2.2 * t) + e.2.1 / (c * e.2.2) * sin (c * e.2.2 * t)) *
          (e.2.2 * cos (e.2.2 * y))).sum := funext fun y ↦ (hx₁ t y).deriv
    rw [e₁, e₂, (ht₂ x t).deriv, (hx₂ t x).deriv, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro e _
    ring
  · simp [waveSum, waveTerm]
  · unfold waveSum
    rw [show (terms.map fun e ↦ waveTerm c e.1 e.2.1 e.2.2 t L) = terms.map fun _ ↦ (0 : ℝ) from
      List.map_congr_left fun e he ↦ by simp [waveTerm, hL e he]]
    simp
  · simp [waveSum, waveTerm]
  · rw [(ht₁ x 0).deriv]
    congr 1
    apply List.map_congr_left
    intro e _
    simp

/-! ## Wave equation on the line -/

theorem hasDerivAt_comp_affine {f f₁ : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f₁ y) y) (x c s : ℝ) :
    HasDerivAt (fun s ↦ f (x + c * s)) (c * f₁ (x + c * s)) s := by
  have := (hf (x + c * s)).comp s (((hasDerivAt_id' s).const_mul c).const_add x)
  exact this.congr_deriv (by ring)

theorem hasDerivAt_comp_shift {f f₁ : ℝ → ℝ} (hf : ∀ y, HasDerivAt f (f₁ y) y) (a y : ℝ) :
    HasDerivAt (fun y ↦ f (y + a)) (f₁ (y + a)) y := by
  have := (hf (y + a)).comp y ((hasDerivAt_id' y).add_const a)
  exact this.congr_deriv (by ring)

/-- d'Alembert's formula solves `u_tt = c ^ 2 u_xx`, `u (0, x) = f x`, `u_t (0, x) = g x`. -/
theorem dalembert_solves (c : ℝ) (hc : c ≠ 0) {f f₁ f₂ G g g₁ : ℝ → ℝ}
    (hf : ∀ y, HasDerivAt f (f₁ y) y) (hf₁ : ∀ y, HasDerivAt f₁ (f₂ y) y)
    (hG : ∀ y, HasDerivAt G (g y) y) (hg : ∀ y, HasDerivAt g (g₁ y) y) (u : ℝ → ℝ → ℝ)
    (hu : ∀ t x, u t x = (f (x + c * t) + f (x - c * t)) / 2 +
      (G (x + c * t) - G (x - c * t)) / (2 * c)) :
    (∀ t x, deriv (fun s ↦ deriv (fun r ↦ u r x) s) t =
        c ^ 2 * deriv (fun y ↦ deriv (fun z ↦ u t z) y) x) ∧
      (∀ x, u 0 x = f x) ∧ ∀ x, deriv (fun s ↦ u s x) 0 = g x := by
  have hu' : u = fun t x ↦ (f (x + c * t) + f (x - c * t)) / 2 +
      (G (x + c * t) - G (x - c * t)) / (2 * c) := funext fun t ↦ funext (hu t)
  subst hu'
  have sub_eq : ∀ x s : ℝ, x - c * s = x + (-c) * s := fun x s ↦ by ring
  -- `u_t` and `u_tt`.
  have ht₁ : ∀ x s, HasDerivAt (fun r ↦ (f (x + c * r) + f (x - c * r)) / 2 +
      (G (x + c * r) - G (x - c * r)) / (2 * c))
      ((c * f₁ (x + c * s) - c * f₁ (x - c * s)) / 2 +
        (c * g (x + c * s) + c * g (x - c * s)) / (2 * c)) s := fun x s ↦ by
    simp only [sub_eq x]
    have a₁ := hasDerivAt_comp_affine hf x c s
    have a₂ := hasDerivAt_comp_affine hf x (-c) s
    have b₁ := hasDerivAt_comp_affine hG x c s
    have b₂ := hasDerivAt_comp_affine hG x (-c) s
    exact (((a₁.add a₂).div_const 2).add ((b₁.sub b₂).div_const (2 * c))).congr_deriv (by ring)
  have ht₂ : ∀ x t, HasDerivAt (fun s ↦ (c * f₁ (x + c * s) - c * f₁ (x - c * s)) / 2 +
      (c * g (x + c * s) + c * g (x - c * s)) / (2 * c))
      ((c ^ 2 * f₂ (x + c * t) + c ^ 2 * f₂ (x - c * t)) / 2 +
        (c * g₁ (x + c * t) - c * g₁ (x - c * t)) / 2) t := fun x t ↦ by
    simp only [sub_eq x]
    have a₁ := (hasDerivAt_comp_affine hf₁ x c t).const_mul c
    have a₂ := (hasDerivAt_comp_affine hf₁ x (-c) t).const_mul c
    have b₁ := (hasDerivAt_comp_affine hg x c t).const_mul c
    have b₂ := (hasDerivAt_comp_affine hg x (-c) t).const_mul c
    exact (((a₁.sub a₂).div_const 2).add ((b₁.add b₂).div_const (2 * c))).congr_deriv (by
      field_simp
      ring)
  -- `u_x` and `u_xx`.
  have hx₁ : ∀ t y, HasDerivAt (fun z ↦ (f (z + c * t) + f (z - c * t)) / 2 +
      (G (z + c * t) - G (z - c * t)) / (2 * c))
      ((f₁ (y + c * t) + f₁ (y - c * t)) / 2 + (g (y + c * t) - g (y - c * t)) / (2 * c)) y :=
    fun t y ↦ by
      simp only [sub_eq_add_neg]
      have a₁ := hasDerivAt_comp_shift hf (c * t) y
      have a₂ := hasDerivAt_comp_shift hf (-(c * t)) y
      have b₁ := hasDerivAt_comp_shift hG (c * t) y
      have b₂ := hasDerivAt_comp_shift hG (-(c * t)) y
      exact ((a₁.add a₂).div_const 2).add ((b₁.sub b₂).div_const (2 * c))
  have hx₂ : ∀ t x, HasDerivAt (fun y ↦ (f₁ (y + c * t) + f₁ (y - c * t)) / 2 +
      (g (y + c * t) - g (y - c * t)) / (2 * c))
      ((f₂ (x + c * t) + f₂ (x - c * t)) / 2 + (g₁ (x + c * t) - g₁ (x - c * t)) / (2 * c)) x :=
    fun t x ↦ by
      simp only [sub_eq_add_neg]
      have a₁ := hasDerivAt_comp_shift hf₁ (c * t) x
      have a₂ := hasDerivAt_comp_shift hf₁ (-(c * t)) x
      have b₁ := hasDerivAt_comp_shift hg (c * t) x
      have b₂ := hasDerivAt_comp_shift hg (-(c * t)) x
      exact ((a₁.add a₂).div_const 2).add ((b₁.sub b₂).div_const (2 * c))
  refine ⟨fun t x ↦ ?_, fun x ↦ ?_, fun x ↦ ?_⟩
  · have e₁ := funext fun s ↦ (ht₁ x s).deriv
    have e₂ := funext fun y ↦ (hx₁ t y).deriv
    rw [e₁, e₂, (ht₂ x t).deriv, (hx₂ t x).deriv]
    field_simp
  · simp
  · rw [(ht₁ x 0).deriv]
    field_simp
    ring_nf

end CAS.ClassicalPDE
