/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2CosineQuotient

/-!
# Parities of quotient tables and the exact rule for products

If `q · w = p` as functions of `(β, θ)` for a weight `w(β)` that vanishes only on a
set with dense complement and has a parity about `a`, then every parity of `p` about `a` in `β`
passes to `q` with the sign of `w` divided out, and every parity of `p` in `θ` passes to `q`
unchanged (`ParityAtβ.of_eval_mul`, `ParityAtθ.of_eval_mul`): off the zeros of `w` this is
division, and the remaining points follow by continuity. The weights `sin β` and `cos β` give the
rules for the quotient `divSinβOfCos` of a cosine table vanishing at `β = 0` and `β = π`, and
for the quotient `divCosβ` of a table odd about `π/2` (`ParityAtβ.divSinβOfCos`,
`ParityAtβ.divCosβ` and their `θ` forms). At the zeros of the weight the quotient takes the
value of a derivative: `q (β, 0) = ∂_θ p (β, 0)` for `q sin θ = p`
(`eval_zero_of_eval_mul_sin_θ`) and `q (π/2, θ) = -∂_β p (π/2, θ)` for `q cos β = p`
(`eval_pi_div_two_of_eval_mul_cos_β`).

For two families of tables with equal parities, componentwise, about `0` and `π/2` in each
variable, the products are even in both variables, so the trapezoid rule in `β` and the sine
rule in `θ` integrate `(∑_c p_c q_c) sin θ` over `[0, π/2]²` exactly
(`integral_integral_sum_mul_mul_sin_eq_rule`), the bilinear form of
`integral_integral_sum_sq_mul_sin_eq_rule`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open CAS.Analysis
open Finset

variable {Mβ Mθ Nβ Nθ : ℕ} {R : Type} [Field R] [Algebra R ℝ]

section QuotientParity

variable {a : ℝ} {e σ : Bool} {p : TrigPoly2 Mβ Mθ R} {q : TrigPoly2 Nβ Nθ R}

/-- **Parity of a quotient in `β`.** If `q · w = p` with a weight `w(β)` of sign
`σ` about `a` that vanishes only on a set with dense complement, a parity `e` of `p` about `a`
gives the parity `e == σ` of `q`. -/
theorem ParityAtβ.of_eval_mul {w : ℝ → ℝ} (hwd : Dense {x | w x ≠ 0})
    (hw : ∀ x, w (2 * a - x) = cond σ 1 (-1) * w x)
    (hq : ∀ β θ, q.eval β θ * w β = p.eval β θ) (hp : ParityAtβ a e p) :
    ParityAtβ a (e == σ) q := by
  intro θ
  have hcq : Continuous fun x ↦ q.eval x θ := q.continuous_eval_β θ
  have hs : cond (e == σ) (1 : ℝ) (-1) * cond σ 1 (-1) = cond e 1 (-1) := by
    cases e <;> cases σ <;> norm_num
  have hσ : cond σ (1 : ℝ) (-1) ≠ 0 := by cases σ <;> norm_num
  have key : (fun x ↦ q.eval (2 * a - x) θ) = fun x ↦ cond (e == σ) 1 (-1) * q.eval x θ := by
    refine Continuous.ext_on hwd (hcq.comp (continuous_const.sub continuous_id))
      (continuous_const.mul hcq) fun x hx ↦ ?_
    have hx' : w x ≠ 0 := hx
    have h1 : q.eval (2 * a - x) θ * (cond σ 1 (-1) * w x) =
        cond e 1 (-1) * (q.eval x θ * w x) := by
      rw [← hw x, hq, hp θ x, hq]
    apply mul_right_cancel₀ (mul_ne_zero hσ hx')
    rw [h1, ← hs]
    ring
  exact fun x ↦ congrFun key x

/-- **Parity of a quotient in `θ`.** If `q · w = p` with a weight `w(β)` vanishing
only on a set with dense complement, every parity of `p` in `θ` is a parity of `q`. -/
theorem ParityAtθ.of_eval_mul {w : ℝ → ℝ} (hwd : Dense {x | w x ≠ 0})
    (hq : ∀ β θ, q.eval β θ * w β = p.eval β θ) (hp : ParityAtθ a e p) : ParityAtθ a e q := by
  intro β x
  have hcq : ∀ t : ℝ, Continuous fun y ↦ q.eval y t := fun t ↦ q.continuous_eval_β t
  have key : (fun y ↦ q.eval y (2 * a - x)) = fun y ↦ cond e 1 (-1) * q.eval y x := by
    refine Continuous.ext_on hwd (hcq _) (continuous_const.mul (hcq x)) fun y hy ↦ ?_
    have hy' : w y ≠ 0 := hy
    apply mul_right_cancel₀ hy'
    have h1 := hq y (2 * a - x)
    rw [hp y x, ← hq y x] at h1
    rw [h1]
    ring
  exact congrFun key β

/-- The quotient by `sin β` of a cosine table vanishing at `β = 0` and `β = π` reverses the
parity in `β` about `0`. -/
theorem ParityAtβ.divSinβOfCos_zero {p : TrigPoly2 Mβ Mθ R} (hMβ : 1 ≤ Mβ)
    (hsin : ∀ j k l, p.coeff 1 j k l = 0) (h0 : ∀ θ, p.eval 0 θ = 0)
    (hπ : ∀ θ, p.eval Real.pi θ = 0) (hp : ParityAtβ 0 e p) :
    ParityAtβ 0 (e == false) (divSinβOfCos p) :=
  ParityAtβ.of_eval_mul dense_sin_ne_zero
    (fun x ↦ by simp [Real.sin_neg]) (eval_divSinβOfCos_mul_sin p hMβ hsin h0 hπ) hp

/-- The quotient by `sin β` keeps the parity in `β` about `π/2`. -/
theorem ParityAtβ.divSinβOfCos_pi_div_two {p : TrigPoly2 Mβ Mθ R} (hMβ : 1 ≤ Mβ)
    (hsin : ∀ j k l, p.coeff 1 j k l = 0) (h0 : ∀ θ, p.eval 0 θ = 0)
    (hπ : ∀ θ, p.eval Real.pi θ = 0) (hp : ParityAtβ (Real.pi / 2) e p) :
    ParityAtβ (Real.pi / 2) (e == true) (divSinβOfCos p) :=
  ParityAtβ.of_eval_mul dense_sin_ne_zero
    (fun x ↦ by simp [mul_div_cancel₀, Real.sin_pi_sub])
    (eval_divSinβOfCos_mul_sin p hMβ hsin h0 hπ) hp

/-- The quotient by `sin β` keeps the parities in `θ`. -/
theorem ParityAtθ.divSinβOfCos {p : TrigPoly2 Mβ Mθ R} (hMβ : 1 ≤ Mβ)
    (hsin : ∀ j k l, p.coeff 1 j k l = 0) (h0 : ∀ θ, p.eval 0 θ = 0)
    (hπ : ∀ θ, p.eval Real.pi θ = 0) (hp : ParityAtθ a e p) :
    ParityAtθ a e (divSinβOfCos p) :=
  ParityAtθ.of_eval_mul dense_sin_ne_zero
    (eval_divSinβOfCos_mul_sin p hMβ hsin h0 hπ) hp

/-- The quotient by `cos β` keeps the parity in `β` about `0`. -/
theorem ParityAtβ.divCosβ_zero {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0) (hp : ParityAtβ 0 e p) :
    ParityAtβ 0 (e == true) (divCosβ p) :=
  ParityAtβ.of_eval_mul dense_cos_ne_zero (fun x ↦ by simp)
    (eval_divCosβ_mul_cos p h) hp

/-- The quotient by `cos β` reverses the parity in `β` about `π/2`. -/
theorem ParityAtβ.divCosβ_pi_div_two {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0)
    (hp : ParityAtβ (Real.pi / 2) e p) : ParityAtβ (Real.pi / 2) (e == false) (divCosβ p) :=
  ParityAtβ.of_eval_mul dense_cos_ne_zero
    (fun x ↦ by simp [mul_div_cancel₀, Real.cos_pi_sub]) (eval_divCosβ_mul_cos p h) hp

/-- The quotient by `cos β` keeps the parities in `θ`. -/
theorem ParityAtθ.divCosβ {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0) (hp : ParityAtθ a e p) :
    ParityAtθ a e (divCosβ p) :=
  ParityAtθ.of_eval_mul dense_cos_ne_zero (eval_divCosβ_mul_cos p h) hp

/-- A quotient `q` with `q · sin β = p` reverses the parity of `p` about `β = 0`. -/
theorem ParityAtβ.of_mul_sin_zero (hq : ∀ β θ, q.eval β θ * Real.sin β = p.eval β θ)
    (hp : ParityAtβ 0 e p) : ParityAtβ 0 (e == false) q :=
  ParityAtβ.of_eval_mul dense_sin_ne_zero (fun x ↦ by simp [Real.sin_neg]) hq hp

/-- A quotient `q` with `q · sin β = p` keeps the parity of `p` about `β = π/2`. -/
theorem ParityAtβ.of_mul_sin_pi_div_two (hq : ∀ β θ, q.eval β θ * Real.sin β = p.eval β θ)
    (hp : ParityAtβ (Real.pi / 2) e p) : ParityAtβ (Real.pi / 2) (e == true) q :=
  ParityAtβ.of_eval_mul dense_sin_ne_zero (fun x ↦ by simp [mul_div_cancel₀, Real.sin_pi_sub])
    hq hp

/-- A quotient `q` with `q · sin β = p` keeps the parities of `p` in `θ`. -/
theorem ParityAtθ.of_mul_sin (hq : ∀ β θ, q.eval β θ * Real.sin β = p.eval β θ)
    (hp : ParityAtθ a e p) : ParityAtθ a e q :=
  ParityAtθ.of_eval_mul dense_sin_ne_zero hq hp

/-- At `θ = 0` a quotient `q` with `q · sin θ = p` takes the value `∂_θ p (β, 0)`. -/
theorem eval_zero_of_eval_mul_sin_θ {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ β θ, q.eval β θ * Real.sin θ = p.eval β θ) (β : ℝ) :
    q.eval β 0 = p.dθ.eval β 0 := by
  have hq := (hasDerivAt_eval_θ q β 0).fun_mul (Real.hasDerivAt_sin 0)
  rw [show (fun t ↦ q.eval β t * Real.sin t) = p.eval β from funext (h β)] at hq
  have := hq.unique (hasDerivAt_eval_θ p β 0)
  simpa using this

/-- At `β = π/2` a quotient `q` with `q · cos β = p` takes the value `-∂_β p (π/2, θ)`. -/
theorem eval_pi_div_two_of_eval_mul_cos_β {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ β θ, q.eval β θ * Real.cos β = p.eval β θ) (θ : ℝ) :
    q.eval (Real.pi / 2) θ = -p.dβ.eval (Real.pi / 2) θ := by
  have hq := (hasDerivAt_eval_β q (Real.pi / 2) θ).fun_mul
    (Real.hasDerivAt_cos (Real.pi / 2))
  rw [show (fun t ↦ q.eval t θ * Real.cos t) = fun t ↦ p.eval t θ from funext fun t ↦ h t θ] at hq
  have := hq.unique (hasDerivAt_eval_β p (Real.pi / 2) θ)
  simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, mul_zero, zero_add] at this
  linarith


/-- Off `sin θ = 0` a quotient `q` with `q · sin θ = p` is `p / sin θ`. -/
theorem eval_eq_div_of_eval_mul_sin_θ {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ β θ, q.eval β θ * Real.sin θ = p.eval β θ) {β θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    q.eval β θ = p.eval β θ / Real.sin θ := by
  rw [← h β θ]
  field_simp

/-- Off `sin θ = 0`: `∂q = (∂p - q cos θ) / sin θ`. -/
theorem eval_dθ_eq_div_of_eval_mul_sin_θ {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ β θ, q.eval β θ * Real.sin θ = p.eval β θ) {β θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    q.dθ.eval β θ = (p.dθ.eval β θ - q.eval β θ * Real.cos θ) / Real.sin θ := by
  rw [← eval_dθ_mul_sin_θ h β θ]
  field_simp
  ring

/-- Off `sin θ = 0`: `∂²q = (∂²p - 2 ∂q cos θ + q sin θ) / sin θ`. -/
theorem eval_dθ_dθ_eq_div_of_eval_mul_sin_θ {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ β θ, q.eval β θ * Real.sin θ = p.eval β θ) {β θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    q.dθ.dθ.eval β θ =
      (p.dθ.dθ.eval β θ - 2 * (q.dθ.eval β θ * Real.cos θ) + q.eval β θ * Real.sin θ) /
        Real.sin θ := by
  rw [← eval_dθ_dθ_mul_sin_θ h β θ]
  field_simp
  ring

/-- At `θ = 0`: `∂q (β, 0) = ∂²p (β, 0) / 2`. -/
theorem eval_dθ_zero_of_eval_mul_sin_θ {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ β θ, q.eval β θ * Real.sin θ = p.eval β θ) (β : ℝ) :
    q.dθ.eval β 0 = p.dθ.dθ.eval β 0 / 2 := by
  have := eval_dθ_dθ_mul_sin_θ h β 0
  simp only [Real.sin_zero, Real.cos_zero, mul_zero, mul_one, sub_zero, zero_add] at this
  linarith

/-- A table odd in `β` about `0` vanishes at `β = 0`. -/
theorem eval_zero_of_parityAtβ_zero_false {p : TrigPoly2 Mβ Mθ R} (hp : ParityAtβ 0 false p)
    (θ : ℝ) : p.eval 0 θ = 0 := by
  have h := hp θ 0
  simp only [mul_zero, sub_zero, Bool.cond_false] at h
  linarith

/-- A table odd in `β` about `0` vanishes at `β = π`. -/
theorem eval_pi_of_parityAtβ_zero_false {p : TrigPoly2 Mβ Mθ R} (hp : ParityAtβ 0 false p)
    (θ : ℝ) : p.eval Real.pi θ = 0 := by
  have hneg : p.eval (-Real.pi) θ = p.eval Real.pi θ := by
    unfold eval
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
    fin_cases i <;> simp [trigMode, Real.sin_nat_mul_pi]
  have h := hp θ Real.pi
  simp only [mul_zero, zero_sub, Bool.cond_false, hneg] at h
  linarith

/-- A table odd in `θ` about `0` vanishes at `θ = 0`. -/
theorem eval_θ_zero_of_parityAtθ_zero_false {p : TrigPoly2 Mβ Mθ R} (hp : ParityAtθ 0 false p)
    (β : ℝ) : p.eval β 0 = 0 := by
  have h := hp β 0
  simp only [mul_zero, sub_zero, Bool.cond_false] at h
  linarith

end QuotientParity

section ProductRule

/-- Tables with a common parity about `a` in `β` have an even product. -/
theorem isEvenAtβ_mul_of_parity {a : ℝ} {p : TrigPoly2 Mβ Mθ R} {q : TrigPoly2 Nβ Nθ R}
    (h : ∃ e, ParityAtβ a e p ∧ ParityAtβ a e q) : (p.mul q).IsEvenAtβ a := by
  obtain ⟨e, hp, hq⟩ := h
  exact parityAtβ_true_iff.mp (hp.mul hq (by cases e <;> rfl))

/-- Tables with a common parity about `a` in `θ` have an even product. -/
theorem isEvenAtθ_mul_of_parity {a : ℝ} {p : TrigPoly2 Mβ Mθ R} {q : TrigPoly2 Nβ Nθ R}
    (h : ∃ e, ParityAtθ a e p ∧ ParityAtθ a e q) : (p.mul q).IsEvenAtθ a := by
  obtain ⟨e, hp, hq⟩ := h
  exact parityAtθ_true_iff.mp (hp.mul hq (by cases e <;> rfl))

/-- **Exact rule for products.** For families `p`, `q` of tables with componentwise equal
parities about `0` and `π/2` in each variable, the trapezoid rule in `β` with `Mβ < 2N` and the
sine rule in `θ` with `Mθ ≤ P` integrate `(∑_c p_c q_c) sin θ` over `[0, π/2]²`. -/
theorem integral_integral_sum_mul_mul_sin_eq_rule {ι : Type*} (s : Finset ι)
    (p q : ι → TrigPoly2 Mβ Mθ R) {N P : ℕ} (hN : Mβ < 2 * N) (hP : 0 < P) (hMP : Mθ ≤ P)
    (hβ0 : ∀ c ∈ s, ∃ e, ParityAtβ 0 e (p c) ∧ ParityAtβ 0 e (q c))
    (hβπ : ∀ c ∈ s, ∃ e, ParityAtβ (Real.pi / 2) e (p c) ∧ ParityAtβ (Real.pi / 2) e (q c))
    (hθ0 : ∀ c ∈ s, ∃ e, ParityAtθ 0 e (p c) ∧ ParityAtθ 0 e (q c))
    (hθπ : ∀ c ∈ s, ∃ e, ParityAtθ (Real.pi / 2) e (p c) ∧ ParityAtθ (Real.pi / 2) e (q c)) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2),
        (∑ c ∈ s, (p c).eval β θ * (q c).eval β θ) * Real.sin θ =
      ∑ j : Fin (N + 1), ∑ n : Fin (P + 1), quarterTrapezoidWeight N j * quarterSinWeight P n *
        ∑ c ∈ s, (p c).eval (j * Real.pi / (2 * N)) (n * Real.pi / (2 * P)) *
          (q c).eval (j * Real.pi / (2 * N)) (n * Real.pi / (2 * P)) := by
  have hf : ∀ β θ, ∑ c ∈ s, (p c).eval β θ * (q c).eval β θ =
      ∑ c ∈ s, ((p c).mul (q c)).eval β θ := fun β θ ↦ by simp only [eval_mul]
  simp only [hf]
  refine integral_integral_mul_sin_eq_rule (f := fun β θ ↦ ∑ c ∈ s, ((p c).mul (q c)).eval β θ)
    hN hP hMP (fun θ ↦ IsEvenCosineSeries.sum s fun c hc ↦ ?_)
    (fun β ↦ IsEvenCosineSeries.sum s fun c hc ↦ ?_)
  · exact (isEvenCosineSeries_β (isEvenAtβ_mul_of_parity (hβ0 c hc))
      (isEvenAtβ_mul_of_parity (hβπ c hc)) θ).mono (by omega)
  · exact (isEvenCosineSeries_θ (isEvenAtθ_mul_of_parity (hθ0 c hc))
      (isEvenAtθ_mul_of_parity (hθπ c hc)) β).mono (by omega)

/-- A table even in `β` about `0` has cosine sections: `p (β, θ) = ∑_k a_k(θ) cos (kβ)`. -/
theorem eval_eq_sum_cos_of_isEvenAtβ_zero {p : TrigPoly2 Mβ Mθ R} (hp : p.IsEvenAtβ 0)
    (θ β : ℝ) : p.eval β θ = ∑ k ∈ range (Mβ + 1), p.sectionβ θ 0 k * Real.cos (k * β) := by
  have h1 := p.eval_eq_sum_sectionβ θ β
  have h2 := p.eval_eq_sum_sectionβ θ (-β)
  have hneg : p.eval (-β) θ = p.eval β θ := by simpa using hp θ β
  simp only [mul_neg, Real.cos_neg, Real.sin_neg] at h2
  have hsum : p.eval β θ + p.eval (-β) θ =
      2 * ∑ k ∈ range (Mβ + 1), p.sectionβ θ 0 k * Real.cos (k * β) := by
    rw [h2, two_mul]
    nth_rw 1 [h1]
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun k _ ↦ by ring
  linarith

/-- **Exact rule for products, any parity about `π/2` in `β`.** For families `p`, `q` of tables
with componentwise equal parities about `0` in `β` and about `0` and `π/2` in `θ`, the cosine
rule in `β` on the nodes `n π / N` of `[0, π]` with `2 Mβ ≤ N` and the sine rule in `θ` with
`Mθ ≤ P` integrate `(∑_c p_c q_c) sin θ` over `[0, π/2]²`. -/
theorem integral_integral_sum_mul_mul_sin_eq_cosineRule {ι : Type*} (s : Finset ι)
    (p q : ι → TrigPoly2 Mβ Mθ R) {N P : ℕ} (hN : 0 < N) (hD : Mβ + Mβ ≤ N) (hP : 0 < P)
    (hMP : Mθ ≤ P) (hβ0 : ∀ c ∈ s, ∃ e, ParityAtβ 0 e (p c) ∧ ParityAtβ 0 e (q c))
    (hθ0 : ∀ c ∈ s, ∃ e, ParityAtθ 0 e (p c) ∧ ParityAtθ 0 e (q c))
    (hθπ : ∀ c ∈ s, ∃ e, ParityAtθ (Real.pi / 2) e (p c) ∧ ParityAtθ (Real.pi / 2) e (q c)) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2),
        (∑ c ∈ s, (p c).eval β θ * (q c).eval β θ) * Real.sin θ =
      ∑ n : Fin (N + 1), ∑ m : Fin (P + 1), quarterCosineWeight N n * quarterSinWeight P m *
        ∑ c ∈ s, (p c).eval (n * Real.pi / N) (m * Real.pi / (2 * P)) *
          (q c).eval (n * Real.pi / N) (m * Real.pi / (2 * P)) := by
  set f : ℝ → ℝ → ℝ := fun β θ ↦ ∑ c ∈ s, ((p c).mul (q c)).eval β θ with hfdef
  have hf : ∀ β θ, ∑ c ∈ s, (p c).eval β θ * (q c).eval β θ = f β θ := fun β θ ↦ by
    simp only [hfdef, eval_mul]
  simp only [hf]
  refine integral_integral_eq_sum_sum univ univ (fun n : Fin (N + 1) ↦ (n : ℝ) * Real.pi / N)
    (fun m : Fin (P + 1) ↦ (m : ℝ) * Real.pi / (2 * P)) (fun n ↦ quarterCosineWeight N n)
    (fun m ↦ quarterSinWeight P m) (fun β ↦ ?_) (fun m _ ↦ ?_) (fun m _ ↦ ?_)
  · exact (IsEvenCosineSeries.sum s fun c hc ↦ (isEvenCosineSeries_θ
      (isEvenAtθ_mul_of_parity (hθ0 c hc)) (isEvenAtθ_mul_of_parity (hθπ c hc)) β).mono
        (by omega)).integral_mul_sin_eq_rule hP hMP
  · set θ := (m : ℝ) * Real.pi / (2 * P)
    have hcos : ∀ β, f β θ = ∑ k : Fin (Mβ + Mβ + 1),
        (∑ c ∈ s, ((p c).mul (q c)).sectionβ θ 0 k) * Real.cos (k * β) := by
      intro β
      simp only [hfdef, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun c hc ↦ ?_
      rw [eval_eq_sum_cos_of_isEvenAtβ_zero (isEvenAtβ_mul_of_parity (hβ0 c hc)) θ β,
        ← Fin.sum_univ_eq_sum_range (fun k ↦ ((p c).mul (q c)).sectionβ θ 0 k *
          Real.cos (k * β))]
    simp only [hcos]
    rw [integral_cosSeries_eq_quarterCosineRule hN hD]
  · exact (continuous_finsetSum _ fun c _ ↦
      ((p c).mul (q c)).continuous_eval_β _).intervalIntegrable _ _

/-- Tables with a common parity about `θ = π/2` have a product symmetric about the equator. -/
theorem sum_eval_mul_eval_pi_sub {ι : Type*} (s : Finset ι) (p q : ι → TrigPoly2 Mβ Mθ R)
    (h : ∀ c ∈ s, ∃ e, ParityAtθ (Real.pi / 2) e (p c) ∧ ParityAtθ (Real.pi / 2) e (q c))
    (β θ : ℝ) :
    ∑ c ∈ s, (p c).eval β (Real.pi - θ) * (q c).eval β (Real.pi - θ) =
      ∑ c ∈ s, (p c).eval β θ * (q c).eval β θ := by
  refine sum_congr rfl fun c hc ↦ ?_
  obtain ⟨e, hp, hq⟩ := h c hc
  have hθ : Real.pi - θ = 2 * (Real.pi / 2) - θ := by ring
  rw [hθ, hp β θ, hq β θ]
  cases e <;> simp

end ProductRule

end PDE.Analysis.TrigPoly2
