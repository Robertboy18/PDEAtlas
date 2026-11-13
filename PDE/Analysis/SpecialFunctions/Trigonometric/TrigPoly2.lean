/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Analysis.SpecialFunctions.Trigonometric.EvenCosineSeries
public import PDE.Analysis.Calculus.Parity

/-!
# Trigonometric polynomials in two variables

`TrigPoly2 Mβ Mθ R` is a finite table of coefficients `coeff i j k l`, with frequencies
`k ≤ Mβ` and `l ≤ Mθ`, that represents the function
`(β, θ) ↦ ∑ coeff i j k l · m_i (k β) · m_j (l θ)`, where `m_0 = cos` and `m_1 = sin`
(`trigMode`). The coefficients lie in a field `R` with an algebra map to `ℝ`; the default
`R = ℚ` gives exact rational tables, and `R = ℝ` serves fields with real parameters.

Products of two modes in one variable follow the product-to-sum formulas
`m_i (k x) m_{i'} (k' x) = (σ m_{i+i'} ((k + k') x) + σ' m_{i+i'} (|k - k'| x)) / 2`
(`trigMode_mul_trigMode`), so the product of two tables of degrees `(Mβ, Mθ)` and `(Nβ, Nθ)`
is a table of degree `(Mβ + Nβ, Mθ + Nθ)` (`TrigPoly2.mul`, `TrigPoly2.eval_mul`). Its
coefficients vanish outside the sum of the supports of the factors, in the modes and in the
class of `i + k` modulo `2` of each variable (`TrigPoly2.coeff_mul_eq_zero_of_βblock` and its
variants), and `TrigPoly2.eraseZeroModes` removes the cells of `sin (0 · x)`, which do not affect
the values. The partial
derivatives `TrigPoly2.dβ` and `TrigPoly2.dθ` act on the coefficients and keep the degrees, and
satisfy the Leibniz rule on products (`TrigPoly2.eval_dβ_mul`). `TrigPoly2.tensor` is the table
of a product of a series in `β` and a series in `θ`.

A function `f` is even about `a` (`IsEvenAt a f`) when `f (2a - x) = f x`, and odd about `a`
(`IsOddAt a f`) when `f (2a - x) = -f x`; about `0` these are `Function.Even` and `Function.Odd`
(`isEvenAt_zero_iff_even`), and the derivative rules come from `odd_deriv_of_even` and
`even_deriv_of_odd` after a shift. The predicates `TrigPoly2.IsEvenAtβ`,
`TrigPoly2.IsOddAtβ`, `TrigPoly2.IsEvenAtθ` and `TrigPoly2.IsOddAtθ` ask this of every section;
they are closed under sums and products with the usual sign rules, a derivative in one variable
exchanges even and odd in that variable and keeps the parity in the other. The parities about
`0` and `π/2` follow from the support of the coefficients: `m_i (k (-x)) = (-1)^i m_i (k x)`
and `m_i (k (π - x)) = (-1)^(i + k) m_i (k x)`.

Every section `β ↦ p.eval β θ` is a trigonometric series
`∑_{k ≤ Mβ} (a_k cos (kβ) + b_k sin (kβ))` (`TrigPoly2.eval_eq_sum_sectionβ`), in the form
taken by `IsEvenCosineSeries.of_trigSeries`, and similarly in `θ`. Parity about `0` and `π/2`
in a variable therefore makes its sections even cosine series, to which the exact
quarter-period rules apply (`TrigPoly2.isEvenCosineSeries_β`, `TrigPoly2.isEvenCosineSeries_θ`,
and `TrigPoly2.isEvenCosineSeries_sq_β`, `TrigPoly2.isEvenCosineSeries_sq_θ` for squares). For a
sum of squares of tables with these parities, the trapezoid rule in `β` and the sine rule in `θ`
give `∫∫ (∑_c p_c²) sin θ` over `[0, π/2]²` exactly
(`TrigPoly2.integral_integral_sum_sq_mul_sin_eq_rule`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open CAS.Analysis
open Finset

/-! ### Even and odd functions about a point -/

/-- `f` is even about `a`: `f (2a - x) = f x` for every `x`. -/
def IsEvenAt (a : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x, f (2 * a - x) = f x

/-- `f` is odd about `a`: `f (2a - x) = -f x` for every `x`. -/
def IsOddAt (a : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x, f (2 * a - x) = -f x

/-- Evenness about `a` is evenness of the shifted function `y ↦ f (a + y)`. -/
theorem isEvenAt_iff_even_comp_add {a : ℝ} {f : ℝ → ℝ} :
    IsEvenAt a f ↔ Function.Even fun y ↦ f (a + y) := by
  refine ⟨fun h y ↦ ?_, fun h x ↦ ?_⟩
  · dsimp only
    rw [← h (a + y)]
    ring_nf
  · have := h (x - a)
    dsimp only at this
    rw [show 2 * a - x = a + -(x - a) by ring, this, show a + (x - a) = x by ring]

/-- Oddness about `a` is oddness of the shifted function `y ↦ f (a + y)`. -/
theorem isOddAt_iff_odd_comp_add {a : ℝ} {f : ℝ → ℝ} :
    IsOddAt a f ↔ Function.Odd fun y ↦ f (a + y) := by
  refine ⟨fun h y ↦ ?_, fun h x ↦ ?_⟩
  · dsimp only
    rw [← h (a + y)]
    ring_nf
  · have := h (x - a)
    dsimp only at this
    rw [show 2 * a - x = a + -(x - a) by ring, this, show a + (x - a) = x by ring]

/-- Evenness about `0` is `Function.Even`. -/
theorem isEvenAt_zero_iff_even {f : ℝ → ℝ} : IsEvenAt 0 f ↔ Function.Even f := by
  simp [isEvenAt_iff_even_comp_add]

/-- Oddness about `0` is `Function.Odd`. -/
theorem isOddAt_zero_iff_odd {f : ℝ → ℝ} : IsOddAt 0 f ↔ Function.Odd f := by
  simp [isOddAt_iff_odd_comp_add]

namespace IsEvenAt

variable {a : ℝ} {f g : ℝ → ℝ}

/-- Evenness about `0` is `f (-x) = f x`. -/
theorem apply_neg (h : IsEvenAt 0 f) (x : ℝ) : f (-x) = f x := by
  simpa using h x

/-- Evenness about `π/2` is `f (π - x) = f x`. -/
theorem apply_pi_sub (h : IsEvenAt (Real.pi / 2) f) (x : ℝ) : f (Real.pi - x) = f x := by
  simpa [mul_div_cancel₀] using h x

/-- Evenness about `a` in the symmetric form `f (a - y) = f (a + y)`. -/
theorem apply_sub_eq_apply_add (h : IsEvenAt a f) (y : ℝ) : f (a - y) = f (a + y) := by
  rw [← h (a + y)]
  ring_nf

protected theorem const (c : ℝ) : IsEvenAt a (fun _ ↦ c) := fun _ ↦ rfl

protected theorem add (hf : IsEvenAt a f) (hg : IsEvenAt a g) :
    IsEvenAt a (fun x ↦ f x + g x) := fun x ↦ by simp only [hf x, hg x]

protected theorem neg (hf : IsEvenAt a f) : IsEvenAt a (fun x ↦ -f x) := fun x ↦ by
  simp only [hf x]

protected theorem const_mul (c : ℝ) (hf : IsEvenAt a f) : IsEvenAt a (fun x ↦ c * f x) :=
  fun x ↦ by simp only [hf x]

protected theorem mul (hf : IsEvenAt a f) (hg : IsEvenAt a g) :
    IsEvenAt a (fun x ↦ f x * g x) := fun x ↦ by simp only [hf x, hg x]

/-- An even function times an odd one is odd. -/
protected theorem mul_odd (hf : IsEvenAt a f) (hg : IsOddAt a g) :
    IsOddAt a (fun x ↦ f x * g x) := fun x ↦ by simp only [hf x, hg x, mul_neg]

protected theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, IsEvenAt a (F i)) : IsEvenAt a (fun x ↦ ∑ i ∈ s, F i x) := fun x ↦
  sum_congr rfl fun i hi ↦ h i hi x

/-- The derivative of an even function is odd (`odd_deriv_of_even` after a shift). -/
theorem hasDerivAt {f' : ℝ → ℝ} (hf : IsEvenAt a f) (hd : ∀ x, HasDerivAt f (f' x) x) :
    IsOddAt a f' := by
  have hg := odd_deriv_of_even (isEvenAt_iff_even_comp_add.mp hf)
  have hdg : ∀ y, deriv (fun y ↦ f (a + y)) y = f' (a + y) := fun y ↦
    ((hd (a + y)).comp_const_add a y).deriv
  exact isOddAt_iff_odd_comp_add.mpr fun y ↦ by simpa only [hdg] using hg y

end IsEvenAt

namespace IsOddAt

variable {a : ℝ} {f g : ℝ → ℝ}

/-- Oddness about `0` is `f (-x) = -f x`. -/
theorem apply_neg (h : IsOddAt 0 f) (x : ℝ) : f (-x) = -f x := by
  simpa using h x

/-- Oddness about `π/2` is `f (π - x) = -f x`. -/
theorem apply_pi_sub (h : IsOddAt (Real.pi / 2) f) (x : ℝ) : f (Real.pi - x) = -f x := by
  simpa [mul_div_cancel₀] using h x

protected theorem add (hf : IsOddAt a f) (hg : IsOddAt a g) :
    IsOddAt a (fun x ↦ f x + g x) := fun x ↦ by simp only [hf x, hg x, neg_add]

protected theorem neg (hf : IsOddAt a f) : IsOddAt a (fun x ↦ -f x) := fun x ↦ by
  simp only [hf x]

protected theorem const_mul (c : ℝ) (hf : IsOddAt a f) : IsOddAt a (fun x ↦ c * f x) :=
  fun x ↦ by simp only [hf x, mul_neg]

/-- The product of two odd functions is even. -/
protected theorem mul (hf : IsOddAt a f) (hg : IsOddAt a g) :
    IsEvenAt a (fun x ↦ f x * g x) := fun x ↦ by simp only [hf x, hg x, neg_mul_neg]

/-- An odd function times an even one is odd. -/
protected theorem mul_even (hf : IsOddAt a f) (hg : IsEvenAt a g) :
    IsOddAt a (fun x ↦ f x * g x) := fun x ↦ by simp only [hf x, hg x, neg_mul]

protected theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, IsOddAt a (F i)) : IsOddAt a (fun x ↦ ∑ i ∈ s, F i x) := fun x ↦ by
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun i hi ↦ h i hi x

/-- The derivative of an odd function is even (`even_deriv_of_odd` after a shift). -/
theorem hasDerivAt {f' : ℝ → ℝ} (hf : IsOddAt a f) (hd : ∀ x, HasDerivAt f (f' x) x) :
    IsEvenAt a f' := by
  have hg := even_deriv_of_odd (isOddAt_iff_odd_comp_add.mp hf)
  have hdg : ∀ y, deriv (fun y ↦ f (a + y)) y = f' (a + y) := fun y ↦
    ((hd (a + y)).comp_const_add a y).deriv
  exact isEvenAt_iff_even_comp_add.mpr fun y ↦ by simpa only [hdg] using hg y

end IsOddAt

/-! ### Trigonometric modes -/

/-- The two trigonometric modes: `trigMode 0 = cos` and `trigMode 1 = sin`. -/
def trigMode (i : Fin 2) (x : ℝ) : ℝ :=
  if i = 0 then Real.cos x else Real.sin x

@[simp] theorem trigMode_zero (x : ℝ) : trigMode 0 x = Real.cos x := rfl

@[simp] theorem trigMode_one (x : ℝ) : trigMode 1 x = Real.sin x := rfl

theorem continuous_trigMode (i : Fin 2) : Continuous (trigMode i) := by
  fin_cases i
  · exact Real.continuous_cos
  · exact Real.continuous_sin

/-- `m_i (k (-x)) = (-1)^i m_i (k x)`: the cosine is even and the sine odd. -/
theorem trigMode_mul_neg (i : Fin 2) (k x : ℝ) :
    trigMode i (k * -x) = (-1) ^ (i : ℕ) * trigMode i (k * x) := by
  fin_cases i <;> simp [mul_neg, Real.cos_neg, Real.sin_neg]

/-- `m_i (k (π - x)) = (-1)^(i + k) m_i (k x)` for a natural frequency `k`. -/
theorem trigMode_mul_pi_sub (i : Fin 2) (k : ℕ) (x : ℝ) :
    trigMode i (k * (Real.pi - x)) = (-1) ^ ((i : ℕ) + k) * trigMode i (k * x) := by
  rw [mul_sub, mul_comm (k : ℝ) Real.pi]
  fin_cases i
  · simp [Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, mul_comm Real.pi]
  · simp only [Fin.mk_one, trigMode_one, Fin.isValue]
    rw [Real.sin_sub, mul_comm Real.pi, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi, pow_add]
    ring

/-- The derivative of `x ↦ m_i (k x)`: `-k sin (kx)` for the cosine and `k cos (kx)` for the
sine. -/
theorem hasDerivAt_trigMode_mul (i : Fin 2) (k x : ℝ) :
    HasDerivAt (fun t ↦ trigMode i (k * t))
      (k * (if i = 0 then -trigMode 1 (k * x) else trigMode 0 (k * x))) x := by
  have hk : HasDerivAt (fun t ↦ k * t) k x := by simpa using (hasDerivAt_id x).const_mul k
  fin_cases i
  · simpa [mul_comm] using hk.cos
  · simpa [mul_comm] using hk.sin

/-- The sign of the term `m_{i+i'} ((k + k') x)` in the product of two modes. -/
def trigSumSign {R : Type*} [One R] [Neg R] (i i' : Fin 2) : R :=
  if i = 1 ∧ i' = 1 then -1 else 1

/-- The sign of the term `m_{i+i'} (|k - k'| x)` in the product of two modes. -/
def trigDiffSign {R : Type*} [One R] [Neg R] (i i' : Fin 2) (k k' : ℕ) : R :=
  if i = 0 ∧ i' = 1 then (if k ≤ k' then 1 else -1)
  else if i = 1 ∧ i' = 0 then (if k' ≤ k then 1 else -1) else 1

theorem map_trigSumSign {R S F : Type*} [Ring R] [Ring S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (i i' : Fin 2) : f (trigSumSign i i') = trigSumSign i i' := by
  unfold trigSumSign
  split_ifs <;> simp

theorem map_trigDiffSign {R S F : Type*} [Ring R] [Ring S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (i i' : Fin 2) (k k' : ℕ) : f (trigDiffSign i i' k k') = trigDiffSign i i' k k' := by
  unfold trigDiffSign
  split_ifs <;> simp

/-- The product-to-sum formula for two modes with natural frequencies. -/
theorem trigMode_mul_trigMode (i i' : Fin 2) (k k' : ℕ) (x : ℝ) :
    trigMode i (k * x) * trigMode i' (k' * x) =
      ((trigSumSign i i' : ℝ) * trigMode (i + i') (((k + k' : ℕ) : ℝ) * x) +
        trigDiffSign i i' k k' * trigMode (i + i') ((Nat.dist k k' : ℝ) * x)) / 2 := by
  have hsum : ((k + k' : ℕ) : ℝ) * x = k * x + k' * x := by push_cast; ring
  have hc : Real.cos ((Nat.dist k k' : ℝ) * x) = Real.cos (k * x - k' * x) := by
    rw [show (k : ℝ) * x - k' * x = 2 * k * (x / 2) - 2 * k' * (x / 2) by ring, ← cos_two_mul_dist]
    ring_nf
  have hs : ∀ a b : ℕ, (if a ≤ b then Real.sin ((Nat.dist a b : ℝ) * x)
      else -Real.sin ((Nat.dist a b : ℝ) * x)) = Real.sin (b * x - a * x) := by
    intro a b
    split_ifs with h
    · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h]; ring_nf
    · rw [Nat.dist_eq_sub_of_le_right (by omega), Nat.cast_sub (by omega), ← Real.sin_neg]
      ring_nf
  rw [hsum]
  fin_cases i <;> fin_cases i' <;> norm_num [trigSumSign, trigDiffSign]
  · rw [hc, Real.cos_add, Real.cos_sub]; ring
  · rw [hs, Real.sin_add, Real.sin_sub]; ring
  · rw [Nat.dist_comm, hs, Real.sin_add, Real.sin_sub]; ring
  · rw [hc, Real.cos_add, Real.cos_sub]; ring

/-! ### Two-variable trigonometric polynomials -/

/-- A trigonometric polynomial in `(β, θ)` of degree at most `Mβ` in `β` and `Mθ` in `θ`:
`coeff i j k l` multiplies `trigMode i (k β) * trigMode j (l θ)`. The coefficients lie in `R`,
by default `ℚ`. -/
@[ext]
structure TrigPoly2 (Mβ Mθ : ℕ) (R : Type := ℚ) where
  /-- The coefficient of `trigMode i (k β) * trigMode j (l θ)`. -/
  coeff : Fin 2 → Fin 2 → Fin (Mβ + 1) → Fin (Mθ + 1) → R

namespace TrigPoly2

variable {Mβ Mθ Nβ Nθ : ℕ} {R : Type}

/-- A table is its array of coefficients. -/
def coeffEquiv : TrigPoly2 Mβ Mθ R ≃ (Fin 2 → Fin 2 → Fin (Mβ + 1) → Fin (Mθ + 1) → R) where
  toFun := coeff
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/-- Tables add and subtract coefficientwise. -/
instance [AddCommGroup R] : AddCommGroup (TrigPoly2 Mβ Mθ R) := coeffEquiv.addCommGroup

/-- Scalars multiply every coefficient. -/
instance [Mul R] : SMul R (TrigPoly2 Mβ Mθ R) :=
  ⟨fun c p ↦ ⟨fun i j k l ↦ c * p.coeff i j k l⟩⟩

@[simp] theorem coeff_zero [AddCommGroup R] (i j : Fin 2) (k : Fin (Mβ + 1))
    (l : Fin (Mθ + 1)) : (0 : TrigPoly2 Mβ Mθ R).coeff i j k l = 0 := rfl

@[simp] theorem coeff_add [AddCommGroup R] (p q : TrigPoly2 Mβ Mθ R) (i j : Fin 2)
    (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) :
    (p + q).coeff i j k l = p.coeff i j k l + q.coeff i j k l := rfl

@[simp] theorem coeff_neg [AddCommGroup R] (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2)
    (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) : (-p).coeff i j k l = -p.coeff i j k l := rfl

@[simp] theorem coeff_sub [AddCommGroup R] (p q : TrigPoly2 Mβ Mθ R) (i j : Fin 2)
    (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) :
    (p - q).coeff i j k l = p.coeff i j k l - q.coeff i j k l := rfl

@[simp] theorem coeff_smul [Mul R] (c : R) (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2)
    (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) : (c • p).coeff i j k l = c * p.coeff i j k l := rfl

/-- The coefficient at natural frequencies, zero past the degrees. -/
def coeffN [Zero R] (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k l : ℕ) : R :=
  if h : k < Mβ + 1 ∧ l < Mθ + 1 then p.coeff i j ⟨k, h.1⟩ ⟨l, h.2⟩ else 0

@[simp] theorem coeffN_coe [Zero R] (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k : Fin (Mβ + 1))
    (l : Fin (Mθ + 1)) : p.coeffN i j k l = p.coeff i j k l := by
  simp [coeffN, k.isLt, l.isLt]

/-- The table with one coefficient `c` at `(i, j, k, l)`. -/
def monomial [Zero R] (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R) :
    TrigPoly2 Mβ Mθ R :=
  ⟨fun i' j' k' l' ↦ if i' = i ∧ j' = j ∧ k' = k ∧ l' = l then c else 0⟩

/-- The constant table. -/
def const [Zero R] (c : R) : TrigPoly2 Mβ Mθ R :=
  monomial 0 0 0 0 c

/-- The table read with degrees `(Nβ, Nθ)`: padded with zeros, or truncated. -/
def resize [Zero R] (p : TrigPoly2 Mβ Mθ R) : TrigPoly2 Nβ Nθ R :=
  ⟨fun i j k l ↦ p.coeffN i j k l⟩

/-- The table with the coefficients of `sin (0 · β)` and `sin (0 · θ)` set to zero. These
coefficients multiply the zero function, so the values do not change
(`eval_eraseZeroModes`). -/
def eraseZeroModes [Zero R] (p : TrigPoly2 Mβ Mθ R) : TrigPoly2 Mβ Mθ R :=
  ⟨fun i j k l ↦ if (i = 1 ∧ (k : ℕ) = 0) ∨ (j = 1 ∧ (l : ℕ) = 0) then 0 else p.coeff i j k l⟩

/-- The coefficients of `sin (0 · β)` and `sin (0 · θ)` vanish. -/
def ZeroModesVanish [Zero R] (p : TrigPoly2 Mβ Mθ R) : Prop :=
  ∀ i j (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)), (i = 1 ∧ (k : ℕ) = 0) ∨ (j = 1 ∧ (l : ℕ) = 0) →
    p.coeff i j k l = 0

theorem zeroModesVanish_eraseZeroModes [Zero R] (p : TrigPoly2 Mβ Mθ R) :
    p.eraseZeroModes.ZeroModesVanish := fun _ _ _ _ h ↦ by
  dsimp only [eraseZeroModes]
  rw [ite_eq_left h]

theorem eraseZeroModes_eq_self [Zero R] {p : TrigPoly2 Mβ Mθ R} (h : p.ZeroModesVanish) :
    p.eraseZeroModes = p := by
  ext i j k l
  dsimp only [eraseZeroModes]
  split_ifs with hc
  · exact (h i j k l hc).symm
  · rfl

/-- The table with every coefficient mapped by a ring homomorphism. -/
def map {S : Type} [Semiring R] [Semiring S] (f : R →+* S) (p : TrigPoly2 Mβ Mθ R) :
    TrigPoly2 Mβ Mθ S :=
  ⟨fun i j k l ↦ f (p.coeff i j k l)⟩

section Eval

variable [Field R] [Algebra R ℝ]

/-- The value at `(β, θ)`: `∑ coeff i j k l · trigMode i (k β) · trigMode j (l θ)`. -/
def eval (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
    algebraMap R ℝ (p.coeff i j k l) * trigMode i ((k : ℕ) * β) * trigMode j ((l : ℕ) * θ)

/-- The value as a sum over natural frequencies. -/
theorem eval_eq_sum_range (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    p.eval β θ = ∑ i, ∑ j, ∑ k ∈ range (Mβ + 1), ∑ l ∈ range (Mθ + 1),
      algebraMap R ℝ (p.coeffN i j k l) * trigMode i (k * β) * trigMode j (l * θ) := by
  unfold eval
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only [← coeffN_coe p i j]
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦ ∑ l ∈ range (Mθ + 1),
    algebraMap R ℝ (p.coeffN i j k l) * trigMode i (k * β) * trigMode j (l * θ))]
  refine sum_congr rfl fun k _ ↦ ?_
  exact Fin.sum_univ_eq_sum_range (fun l ↦
    algebraMap R ℝ (p.coeffN i j k l) * trigMode i (k * β) * trigMode j (l * θ)) _

@[simp] theorem eval_zero (β θ : ℝ) : (0 : TrigPoly2 Mβ Mθ R).eval β θ = 0 := by
  simp [eval]

@[simp] theorem eval_add (p q : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    (p + q).eval β θ = p.eval β θ + q.eval β θ := by
  simp only [eval, coeff_add, map_add, add_mul, sum_add_distrib]

@[simp] theorem eval_neg (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) : (-p).eval β θ = -p.eval β θ := by
  simp only [eval, coeff_neg, map_neg, neg_mul, sum_neg_distrib]

@[simp] theorem eval_sub (p q : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    (p - q).eval β θ = p.eval β θ - q.eval β θ := by
  rw [sub_eq_add_neg, eval_add, eval_neg, sub_eq_add_neg]

@[simp] theorem eval_smul (c : R) (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    (c • p).eval β θ = algebraMap R ℝ c * p.eval β θ := by
  simp only [eval, coeff_smul, map_mul, mul_sum, mul_assoc]

/-- Evaluation at `(β, θ)` as an additive map. -/
def evalAddHom (β θ : ℝ) : TrigPoly2 Mβ Mθ R →+ ℝ where
  toFun p := p.eval β θ
  map_zero' := eval_zero β θ
  map_add' p q := eval_add p q β θ

theorem eval_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    (∑ x ∈ s, f x).eval β θ = ∑ x ∈ s, (f x).eval β θ :=
  map_sum (evalAddHom (R := R) β θ) f s

@[simp] theorem eval_monomial (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R)
    (β θ : ℝ) : (monomial i j k l c).eval β θ =
      algebraMap R ℝ c * trigMode i ((k : ℕ) * β) * trigMode j ((l : ℕ) * θ) := by
  simp only [eval, monomial]
  rw [sum_eq_single i (fun i' _ hi' ↦ by simp [hi'])  (by simp), sum_eq_single j
    (fun j' _ hj' ↦ by simp [hj']) (by simp), sum_eq_single k (fun k' _ hk' ↦ by simp [hk'])
    (by simp), sum_eq_single l (fun l' _ hl' ↦ by simp [hl']) (by simp)]
  simp

@[simp] theorem eval_const (c : R) (β θ : ℝ) :
    (const c : TrigPoly2 Mβ Mθ R).eval β θ = algebraMap R ℝ c := by
  simp [const]

/-- Padding with zeros keeps the values. -/
theorem eval_resize (hβ : Mβ ≤ Nβ) (hθ : Mθ ≤ Nθ) (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    (p.resize : TrigPoly2 Nβ Nθ R).eval β θ = p.eval β θ := by
  have hN : ∀ i j (k l : ℕ), (p.resize : TrigPoly2 Nβ Nθ R).coeffN i j k l =
      p.coeffN i j k l := by
    intro i j k l
    by_cases h : k < Nβ + 1 ∧ l < Nθ + 1
    · simp [coeffN, resize, h]
    · rw [coeffN, dite_eq_right_iff.mpr fun h' ↦ absurd h' h, coeffN,
        dite_eq_right_iff.mpr fun h' ↦ absurd ⟨by omega, by omega⟩ h]
  have hz : ∀ i j (k l : ℕ), ¬ (k < Mβ + 1 ∧ l < Mθ + 1) → p.coeffN i j k l = 0 :=
    fun i j k l h ↦ dite_eq_right_iff.mpr fun h' ↦ absurd h' h
  rw [eval_eq_sum_range, eval_eq_sum_range]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  simp only [hN]
  have hθs : ∀ k ∈ range (Mβ + 1), ∑ l ∈ range (Nθ + 1), algebraMap R ℝ (p.coeffN i j k l) *
      trigMode i (k * β) * trigMode j (l * θ) = ∑ l ∈ range (Mθ + 1),
      algebraMap R ℝ (p.coeffN i j k l) * trigMode i (k * β) * trigMode j (l * θ) := by
    intro k _
    refine (sum_subset (range_subset_range.mpr (by omega)) fun l _ hl ↦ ?_).symm
    rw [hz i j k l fun h ↦ hl (mem_range.mpr h.2)]
    simp
  rw [← sum_congr rfl hθs]
  refine (sum_subset (range_subset_range.mpr (by omega)) fun k _ hk ↦ ?_).symm
  refine sum_eq_zero fun l _ ↦ ?_
  rw [hz i j k l fun h ↦ hk (mem_range.mpr h.1)]
  simp

theorem eval_map {S : Type} [Field S] [Algebra S ℝ] (f : R →+* S)
    (hf : ∀ c, algebraMap S ℝ (f c) = algebraMap R ℝ c) (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    (p.map f).eval β θ = p.eval β θ := by
  simp [eval, map, hf]

theorem eval_eraseZeroModes (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    p.eraseZeroModes.eval β θ = p.eval β θ := by
  unfold eval eraseZeroModes
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
    sum_congr rfl fun l _ ↦ ?_
  dsimp only
  split_ifs with h
  · rcases h with ⟨rfl, hk⟩ | ⟨rfl, hl⟩
    · simp [hk]
    · simp [hl]
  · rfl

theorem continuous_eval (p : TrigPoly2 Mβ Mθ R) :
    Continuous (fun x : ℝ × ℝ ↦ p.eval x.1 x.2) := by
  unfold eval
  refine continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
    continuous_finsetSum _ fun k _ ↦ continuous_finsetSum _ fun l _ ↦ ?_
  exact (continuous_const.mul ((continuous_trigMode i).comp
    (continuous_const.mul continuous_fst))).mul
    ((continuous_trigMode j).comp (continuous_const.mul continuous_snd))

theorem continuous_eval_β (p : TrigPoly2 Mβ Mθ R) (θ : ℝ) : Continuous fun β ↦ p.eval β θ :=
  p.continuous_eval.comp (f := fun β ↦ (β, θ)) (continuous_id.prodMk continuous_const)

theorem continuous_eval_θ (p : TrigPoly2 Mβ Mθ R) (β : ℝ) : Continuous (p.eval β) :=
  p.continuous_eval.comp (f := fun θ ↦ (β, θ)) (continuous_const.prodMk continuous_id)

/-! ### Products -/

/-- The product of the terms `(i, j, k, l)` and `(i', j', k', l')`, with coefficient `c`, by the
product-to-sum formula in each variable. -/
def mulTerm (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (i' j' : Fin 2)
    (k' : Fin (Nβ + 1)) (l' : Fin (Nθ + 1)) (c : R) : TrigPoly2 (Mβ + Nβ) (Mθ + Nθ) R :=
  let K₁ : Fin (Mβ + Nβ + 1) := ⟨k + k', by omega⟩
  let K₂ : Fin (Mβ + Nβ + 1) := ⟨Nat.dist k k', by unfold Nat.dist; omega⟩
  let L₁ : Fin (Mθ + Nθ + 1) := ⟨l + l', by omega⟩
  let L₂ : Fin (Mθ + Nθ + 1) := ⟨Nat.dist l l', by unfold Nat.dist; omega⟩
  let I := i + i'
  let J := j + j'
  monomial I J K₁ L₁ (c * trigSumSign i i' * trigSumSign j j' / 4) +
    monomial I J K₁ L₂ (c * trigSumSign i i' * trigDiffSign j j' l l' / 4) +
    monomial I J K₂ L₁ (c * trigDiffSign i i' k k' * trigSumSign j j' / 4) +
    monomial I J K₂ L₂ (c * trigDiffSign i i' k k' * trigDiffSign j j' l l' / 4)

theorem eval_mulTerm (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (i' j' : Fin 2)
    (k' : Fin (Nβ + 1)) (l' : Fin (Nθ + 1)) (c : R) (β θ : ℝ) :
    (mulTerm i j k l i' j' k' l' c).eval β θ =
      algebraMap R ℝ c * (trigMode i ((k : ℕ) * β) * trigMode j ((l : ℕ) * θ)) *
        (trigMode i' ((k' : ℕ) * β) * trigMode j' ((l' : ℕ) * θ)) := by
  rw [show algebraMap R ℝ c * (trigMode i ((k : ℕ) * β) * trigMode j ((l : ℕ) * θ)) *
      (trigMode i' ((k' : ℕ) * β) * trigMode j' ((l' : ℕ) * θ)) = algebraMap R ℝ c *
      (trigMode i ((k : ℕ) * β) * trigMode i' ((k' : ℕ) * β)) *
      (trigMode j ((l : ℕ) * θ) * trigMode j' ((l' : ℕ) * θ)) by ring,
    trigMode_mul_trigMode, trigMode_mul_trigMode]
  simp only [mulTerm, eval_add, eval_monomial, map_div₀, map_mul, map_trigSumSign,
    map_trigDiffSign, map_ofNat]
  ring

/-- The product of two tables; its degrees are the sums of the degrees. -/
def mul (p : TrigPoly2 Mβ Mθ R) (q : TrigPoly2 Nβ Nθ R) : TrigPoly2 (Mβ + Nβ) (Mθ + Nθ) R :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ i', ∑ j', ∑ k', ∑ l',
    mulTerm i j k l i' j' k' l' (p.coeff i j k l * q.coeff i' j' k' l')

/-- The product table evaluates to the product of the values. -/
theorem eval_mul (p : TrigPoly2 Mβ Mθ R) (q : TrigPoly2 Nβ Nθ R) (β θ : ℝ) :
    (p.mul q).eval β θ = p.eval β θ * q.eval β θ := by
  simp only [mul, eval_sum, eval_mulTerm]
  rw [eval, eval]
  simp only [sum_mul]
  simp only [mul_sum, map_mul]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
    sum_congr rfl fun l _ ↦ sum_congr rfl fun i' _ ↦ sum_congr rfl fun j' _ ↦
    sum_congr rfl fun k' _ ↦ sum_congr rfl fun l' _ ↦ ?_
  ring

/-- Coefficient extraction as an additive map. -/
def coeffAddHom (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) :
    TrigPoly2 Mβ Mθ R →+ R where
  toFun p := p.coeff i j k l
  map_zero' := rfl
  map_add' _ _ := rfl

omit [Algebra R ℝ] in
theorem coeff_sum {ι : Type*} (s : Finset ι) (f : ι → TrigPoly2 Mβ Mθ R) (i j : Fin 2)
    (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) :
    (∑ x ∈ s, f x).coeff i j k l = ∑ x ∈ s, (f x).coeff i j k l :=
  map_sum (coeffAddHom i j k l) f s

omit [Algebra R ℝ] in
theorem mulTerm_zero (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (i' j' : Fin 2)
    (k' : Fin (Nβ + 1)) (l' : Fin (Nθ + 1)) : mulTerm i j k l i' j' k' l' (0 : R) = 0 := by
  ext
  simp [mulTerm, monomial]

omit [Algebra R ℝ] in
/-- A product term has no coefficient outside its four frequencies `(k ± k', l ± l')` in the
modes `(i + i', j + j')`. -/
theorem coeff_mulTerm_eq_zero (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (i' j' : Fin 2)
    (k' : Fin (Nβ + 1)) (l' : Fin (Nθ + 1)) (c : R) {I J : Fin 2} {K : Fin (Mβ + Nβ + 1)}
    {L : Fin (Mθ + Nθ + 1)}
    (h : ¬(I = i + i' ∧ J = j + j' ∧ ((K : ℕ) = k + k' ∨ (K : ℕ) = Nat.dist k k') ∧
      ((L : ℕ) = l + l' ∨ (L : ℕ) = Nat.dist l l'))) :
    (mulTerm i j k l i' j' k' l' c).coeff I J K L = 0 := by
  simp only [mulTerm, coeff_add, monomial]
  rw [ite_eq_right fun hc ↦ h ⟨hc.1, hc.2.1, Or.inl (congrArg Fin.val hc.2.2.1),
      Or.inl (congrArg Fin.val hc.2.2.2)⟩,
    ite_eq_right fun hc ↦ h ⟨hc.1, hc.2.1, Or.inl (congrArg Fin.val hc.2.2.1),
      Or.inr (congrArg Fin.val hc.2.2.2)⟩,
    ite_eq_right fun hc ↦ h ⟨hc.1, hc.2.1, Or.inr (congrArg Fin.val hc.2.2.1),
      Or.inl (congrArg Fin.val hc.2.2.2)⟩,
    ite_eq_right fun hc ↦ h ⟨hc.1, hc.2.1, Or.inr (congrArg Fin.val hc.2.2.1),
      Or.inr (congrArg Fin.val hc.2.2.2)⟩]
  simp

omit [Algebra R ℝ] in
/-- The coefficients of a product vanish where no pair of supported coefficients of the
factors can contribute. -/
theorem coeff_mul_eq_zero {p : TrigPoly2 Mβ Mθ R} {q : TrigPoly2 Nβ Nθ R}
    {P : Fin 2 → Fin 2 → Fin (Mβ + 1) → Fin (Mθ + 1) → Prop}
    {Q : Fin 2 → Fin 2 → Fin (Nβ + 1) → Fin (Nθ + 1) → Prop}
    (hp : ∀ i j k l, ¬P i j k l → p.coeff i j k l = 0)
    (hq : ∀ i j k l, ¬Q i j k l → q.coeff i j k l = 0) {I J : Fin 2} {K : Fin (Mβ + Nβ + 1)}
    {L : Fin (Mθ + Nθ + 1)}
    (h : ∀ i j k l i' j' k' l', P i j k l → Q i' j' k' l' → I = i + i' → J = j + j' →
      ((K : ℕ) = k + k' ∨ (K : ℕ) = Nat.dist k k') →
      ((L : ℕ) = l + l' ∨ (L : ℕ) = Nat.dist l l') → False) :
    (p.mul q).coeff I J K L = 0 := by
  simp only [mul, coeff_sum]
  refine sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ sum_eq_zero fun k _ ↦ sum_eq_zero
    fun l _ ↦ sum_eq_zero fun i' _ ↦ sum_eq_zero fun j' _ ↦ sum_eq_zero fun k' _ ↦
    sum_eq_zero fun l' _ ↦ ?_
  by_cases hP : P i j k l
  · by_cases hQ : Q i' j' k' l'
    · exact coeff_mulTerm_eq_zero _ _ _ _ _ _ _ _ _ fun ⟨hI, hJ, hK, hL⟩ ↦
        h i j k l i' j' k' l' hP hQ hI hJ hK hL
    · rw [hq _ _ _ _ hQ, mul_zero, mulTerm_zero]
      rfl
  · rw [hp _ _ _ _ hP, zero_mul, mulTerm_zero]
    rfl

omit [Algebra R ℝ] in
/-- Factors supported in the `β`-modes `i₀` and `i₁` have a product supported in `i₀ + i₁`. -/
theorem coeff_mul_eq_zero_of_βblock {p : TrigPoly2 Mβ Mθ R} {q : TrigPoly2 Nβ Nθ R}
    {i₀ i₁ : Fin 2} (hp : ∀ i j k l, i ≠ i₀ → p.coeff i j k l = 0)
    (hq : ∀ i j k l, i ≠ i₁ → q.coeff i j k l = 0) {I : Fin 2} (hI : I ≠ i₀ + i₁) (J : Fin 2)
    (K : Fin (Mβ + Nβ + 1)) (L : Fin (Mθ + Nθ + 1)) : (p.mul q).coeff I J K L = 0 :=
  coeff_mul_eq_zero (P := fun i _ _ _ ↦ i = i₀) (Q := fun i _ _ _ ↦ i = i₁) hp hq
    fun _ _ _ _ _ _ _ _ hP hQ hI' _ _ _ ↦ hI (hP ▸ hQ ▸ hI')

omit [Algebra R ℝ] in
/-- Factors supported in the `θ`-modes `j₀` and `j₁` have a product supported in `j₀ + j₁`. -/
theorem coeff_mul_eq_zero_of_θblock {p : TrigPoly2 Mβ Mθ R} {q : TrigPoly2 Nβ Nθ R}
    {j₀ j₁ : Fin 2} (hp : ∀ i j k l, j ≠ j₀ → p.coeff i j k l = 0)
    (hq : ∀ i j k l, j ≠ j₁ → q.coeff i j k l = 0) (I : Fin 2) {J : Fin 2} (hJ : J ≠ j₀ + j₁)
    (K : Fin (Mβ + Nβ + 1)) (L : Fin (Mθ + Nθ + 1)) : (p.mul q).coeff I J K L = 0 :=
  coeff_mul_eq_zero (P := fun _ j _ _ ↦ j = j₀) (Q := fun _ j _ _ ↦ j = j₁) hp hq
    fun _ _ _ _ _ _ _ _ hP hQ _ hJ' _ _ ↦ hJ (hP ▸ hQ ▸ hJ')

omit [Algebra R ℝ] in
/-- The class of `i + k` modulo `2` (the parity about `π/2` in `β`) adds under products. -/
theorem coeff_mul_eq_zero_of_βclass {p : TrigPoly2 Mβ Mθ R} {q : TrigPoly2 Nβ Nθ R}
    {cp cq : ℕ} (hp : ∀ i j k l, (i.val + k.val) % 2 ≠ cp → p.coeff i j k l = 0)
    (hq : ∀ i j k l, (i.val + k.val) % 2 ≠ cq → q.coeff i j k l = 0) {I : Fin 2}
    {K : Fin (Mβ + Nβ + 1)} (hIK : ((I : ℕ) + K) % 2 ≠ (cp + cq) % 2) (J : Fin 2)
    (L : Fin (Mθ + Nθ + 1)) : (p.mul q).coeff I J K L = 0 :=
  coeff_mul_eq_zero (P := fun i _ k _ ↦ (i.val + k.val) % 2 = cp)
    (Q := fun i _ k _ ↦ (i.val + k.val) % 2 = cq) hp hq
    fun i _ k _ i' _ k' _ hP hQ hI _ hK _ ↦ hIK (by
      rw [hI, Fin.val_add]
      unfold Nat.dist at hK
      rcases hK with hK | hK <;> rw [hK] <;> omega)

omit [Algebra R ℝ] in
/-- The class of `j + l` modulo `2` (the parity about `π/2` in `θ`) adds under products. -/
theorem coeff_mul_eq_zero_of_θclass {p : TrigPoly2 Mβ Mθ R} {q : TrigPoly2 Nβ Nθ R}
    {cp cq : ℕ} (hp : ∀ i j k l, (j.val + l.val) % 2 ≠ cp → p.coeff i j k l = 0)
    (hq : ∀ i j k l, (j.val + l.val) % 2 ≠ cq → q.coeff i j k l = 0) (I : Fin 2) {J : Fin 2}
    (K : Fin (Mβ + Nβ + 1)) {L : Fin (Mθ + Nθ + 1)}
    (hJL : ((J : ℕ) + L) % 2 ≠ (cp + cq) % 2) : (p.mul q).coeff I J K L = 0 :=
  coeff_mul_eq_zero (P := fun _ j _ l ↦ (j.val + l.val) % 2 = cp)
    (Q := fun _ j _ l ↦ (j.val + l.val) % 2 = cq) hp hq
    fun _ j _ l _ j' _ l' hP hQ _ hJ _ hL ↦ hJL (by
      rw [hJ, Fin.val_add]
      unfold Nat.dist at hL
      rcases hL with hL | hL <;> rw [hL] <;> omega)

/-! ### Partial derivatives -/

/-- The derivative in `β`: `cos (kβ) ↦ -k sin (kβ)` and `sin (kβ) ↦ k cos (kβ)`. -/
def dβ (p : TrigPoly2 Mβ Mθ R) : TrigPoly2 Mβ Mθ R :=
  ⟨fun i j k l ↦ ((k : ℕ) : R) * (if i = 0 then p.coeff 1 j k l else -p.coeff 0 j k l)⟩

/-- The derivative in `θ`: `cos (lθ) ↦ -l sin (lθ)` and `sin (lθ) ↦ l cos (lθ)`. -/
def dθ (p : TrigPoly2 Mβ Mθ R) : TrigPoly2 Mβ Mθ R :=
  ⟨fun i j k l ↦ ((l : ℕ) : R) * (if j = 0 then p.coeff i 1 k l else -p.coeff i 0 k l)⟩

theorem hasDerivAt_eval_β (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    HasDerivAt (fun t ↦ p.eval t θ) ((dβ p).eval β θ) β := by
  have h : HasDerivAt (fun t ↦ p.eval t θ) (∑ i, ∑ j, ∑ k : Fin (Mβ + 1),
      ∑ l : Fin (Mθ + 1), algebraMap R ℝ (p.coeff i j k l) * ((k : ℕ) *
        (if i = 0 then -trigMode 1 ((k : ℕ) * β) else trigMode 0 ((k : ℕ) * β))) *
        trigMode j ((l : ℕ) * θ)) β := by
    unfold eval
    refine HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦
      HasDerivAt.fun_sum fun k _ ↦ HasDerivAt.fun_sum fun l _ ↦ ?_
    exact ((hasDerivAt_trigMode_mul i _ β).const_mul _).mul_const _
  convert h using 1
  unfold eval dβ
  conv_lhs => rw [Fin.sum_univ_two]
  conv_rhs => rw [Fin.sum_univ_two]
  rw [add_comm]
  congr 1 <;> refine sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
    <;> simp only [Fin.isValue, ↓reduceIte, one_ne_zero, map_mul, map_natCast, map_neg]
    <;> ring

theorem hasDerivAt_eval_θ (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    HasDerivAt (p.eval β) ((dθ p).eval β θ) θ := by
  have h : HasDerivAt (fun t ↦ p.eval β t) (∑ i, ∑ j, ∑ k : Fin (Mβ + 1),
      ∑ l : Fin (Mθ + 1), algebraMap R ℝ (p.coeff i j k l) * trigMode i ((k : ℕ) * β) *
        ((l : ℕ) * (if j = 0 then -trigMode 1 ((l : ℕ) * θ) else trigMode 0 ((l : ℕ) * θ))))
      θ := by
    unfold eval
    refine HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦
      HasDerivAt.fun_sum fun k _ ↦ HasDerivAt.fun_sum fun l _ ↦ ?_
    exact (hasDerivAt_trigMode_mul j _ θ).const_mul _
  convert h using 1
  unfold eval dθ
  refine sum_congr rfl fun i _ ↦ ?_
  conv_lhs => rw [Fin.sum_univ_two]
  conv_rhs => rw [Fin.sum_univ_two]
  rw [add_comm]
  congr 1 <;> refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
    <;> simp only [Fin.isValue, ↓reduceIte, one_ne_zero, map_mul, map_natCast, map_neg]
    <;> ring

/-- The Leibniz rule for the `β`-derivative of a product table. -/
theorem eval_dβ_mul (p : TrigPoly2 Mβ Mθ R) (q : TrigPoly2 Nβ Nθ R) (β θ : ℝ) :
    (p.mul q).dβ.eval β θ = (p.dβ.mul q).eval β θ + (p.mul q.dβ).eval β θ := by
  have h : HasDerivAt (fun t ↦ (p.mul q).eval t θ)
      ((dβ p).eval β θ * q.eval β θ + p.eval β θ * (dβ q).eval β θ) β := by
    simp only [eval_mul]
    exact (hasDerivAt_eval_β p β θ).mul (hasDerivAt_eval_β q β θ)
  rw [eval_mul, eval_mul, (hasDerivAt_eval_β (p.mul q) β θ).unique h]

/-- The Leibniz rule for the `θ`-derivative of a product table. -/
theorem eval_dθ_mul (p : TrigPoly2 Mβ Mθ R) (q : TrigPoly2 Nβ Nθ R) (β θ : ℝ) :
    (p.mul q).dθ.eval β θ = (p.dθ.mul q).eval β θ + (p.mul q.dθ).eval β θ := by
  have h : HasDerivAt (fun t ↦ (p.mul q).eval β t)
      ((dθ p).eval β θ * q.eval β θ + p.eval β θ * (dθ q).eval β θ) θ := by
    simp only [eval_mul]
    exact (hasDerivAt_eval_θ p β θ).mul (hasDerivAt_eval_θ q β θ)
  rw [eval_mul, eval_mul, (hasDerivAt_eval_θ (p.mul q) β θ).unique h]

/-- The table of the product of a series in `β` and a series in `θ`. -/
def tensor (a : Fin 2 → Fin (Mβ + 1) → R) (b : Fin 2 → Fin (Mθ + 1) → R) : TrigPoly2 Mβ Mθ R :=
  ⟨fun i j k l ↦ a i k * b j l⟩

theorem eval_tensor (a : Fin 2 → Fin (Mβ + 1) → R) (b : Fin 2 → Fin (Mθ + 1) → R) (β θ : ℝ) :
    (tensor a b).eval β θ =
      (∑ i, ∑ k : Fin (Mβ + 1), algebraMap R ℝ (a i k) * trigMode i ((k : ℕ) * β)) *
        ∑ j, ∑ l : Fin (Mθ + 1), algebraMap R ℝ (b j l) * trigMode j ((l : ℕ) * θ) := by
  simp only [eval, tensor, map_mul]
  simp only [sum_mul]
  simp only [mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_comm]
  exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ by ring

/-! ### Parity in each variable -/

/-- Every section in `β` is even about `a`. -/
def IsEvenAtβ (a : ℝ) (p : TrigPoly2 Mβ Mθ R) : Prop :=
  ∀ θ, IsEvenAt a (fun β ↦ p.eval β θ)

/-- Every section in `β` is odd about `a`. -/
def IsOddAtβ (a : ℝ) (p : TrigPoly2 Mβ Mθ R) : Prop :=
  ∀ θ, IsOddAt a (fun β ↦ p.eval β θ)

/-- Every section in `θ` is even about `a`. -/
def IsEvenAtθ (a : ℝ) (p : TrigPoly2 Mβ Mθ R) : Prop :=
  ∀ β, IsEvenAt a (p.eval β)

/-- Every section in `θ` is odd about `a`. -/
def IsOddAtθ (a : ℝ) (p : TrigPoly2 Mβ Mθ R) : Prop :=
  ∀ β, IsOddAt a (p.eval β)

variable {a : ℝ} {p p' : TrigPoly2 Mβ Mθ R} {q : TrigPoly2 Nβ Nθ R}

theorem IsEvenAtβ.add (hp : p.IsEvenAtβ a) (hp' : p'.IsEvenAtβ a) : (p + p').IsEvenAtβ a :=
  fun θ x ↦ by simp only [eval_add, hp θ x, hp' θ x]

theorem IsOddAtβ.add (hp : p.IsOddAtβ a) (hp' : p'.IsOddAtβ a) : (p + p').IsOddAtβ a :=
  fun θ x ↦ by simp only [eval_add, hp θ x, hp' θ x, neg_add]

theorem IsEvenAtθ.add (hp : p.IsEvenAtθ a) (hp' : p'.IsEvenAtθ a) : (p + p').IsEvenAtθ a :=
  fun β x ↦ by simp only [eval_add, hp β x, hp' β x]

theorem IsOddAtθ.add (hp : p.IsOddAtθ a) (hp' : p'.IsOddAtθ a) : (p + p').IsOddAtθ a :=
  fun β x ↦ by simp only [eval_add, hp β x, hp' β x, neg_add]

theorem IsEvenAtβ.smul (c : R) (hp : p.IsEvenAtβ a) : (c • p).IsEvenAtβ a :=
  fun θ x ↦ by simp only [eval_smul, hp θ x]

theorem IsOddAtβ.smul (c : R) (hp : p.IsOddAtβ a) : (c • p).IsOddAtβ a :=
  fun θ x ↦ by simp only [eval_smul, hp θ x, mul_neg]

theorem IsEvenAtθ.smul (c : R) (hp : p.IsEvenAtθ a) : (c • p).IsEvenAtθ a :=
  fun β x ↦ by simp only [eval_smul, hp β x]

theorem IsOddAtθ.smul (c : R) (hp : p.IsOddAtθ a) : (c • p).IsOddAtθ a :=
  fun β x ↦ by simp only [eval_smul, hp β x, mul_neg]

theorem IsEvenAtβ.neg (hp : p.IsEvenAtβ a) : (-p).IsEvenAtβ a :=
  fun θ x ↦ by simp only [eval_neg, hp θ x]

theorem IsOddAtβ.neg (hp : p.IsOddAtβ a) : (-p).IsOddAtβ a :=
  fun θ x ↦ by simp only [eval_neg, hp θ x]

theorem IsEvenAtθ.neg (hp : p.IsEvenAtθ a) : (-p).IsEvenAtθ a :=
  fun β x ↦ by simp only [eval_neg, hp β x]

theorem IsOddAtθ.neg (hp : p.IsOddAtθ a) : (-p).IsOddAtθ a :=
  fun β x ↦ by simp only [eval_neg, hp β x]

theorem IsEvenAtβ.mul (hp : p.IsEvenAtβ a) (hq : q.IsEvenAtβ a) : (p.mul q).IsEvenAtβ a :=
  fun θ x ↦ by simp only [eval_mul, hp θ x, hq θ x]

theorem IsEvenAtβ.mul_odd (hp : p.IsEvenAtβ a) (hq : q.IsOddAtβ a) : (p.mul q).IsOddAtβ a :=
  fun θ x ↦ by simp only [eval_mul, hp θ x, hq θ x, mul_neg]

theorem IsOddAtβ.mul_even (hp : p.IsOddAtβ a) (hq : q.IsEvenAtβ a) : (p.mul q).IsOddAtβ a :=
  fun θ x ↦ by simp only [eval_mul, hp θ x, hq θ x, neg_mul]

theorem IsOddAtβ.mul (hp : p.IsOddAtβ a) (hq : q.IsOddAtβ a) : (p.mul q).IsEvenAtβ a :=
  fun θ x ↦ by simp only [eval_mul, hp θ x, hq θ x, neg_mul_neg]

theorem IsEvenAtθ.mul (hp : p.IsEvenAtθ a) (hq : q.IsEvenAtθ a) : (p.mul q).IsEvenAtθ a :=
  fun β x ↦ by simp only [eval_mul, hp β x, hq β x]

theorem IsEvenAtθ.mul_odd (hp : p.IsEvenAtθ a) (hq : q.IsOddAtθ a) : (p.mul q).IsOddAtθ a :=
  fun β x ↦ by simp only [eval_mul, hp β x, hq β x, mul_neg]

theorem IsOddAtθ.mul_even (hp : p.IsOddAtθ a) (hq : q.IsEvenAtθ a) : (p.mul q).IsOddAtθ a :=
  fun β x ↦ by simp only [eval_mul, hp β x, hq β x, neg_mul]

theorem IsOddAtθ.mul (hp : p.IsOddAtθ a) (hq : q.IsOddAtθ a) : (p.mul q).IsEvenAtθ a :=
  fun β x ↦ by simp only [eval_mul, hp β x, hq β x, neg_mul_neg]

theorem IsEvenAtβ.sum {ι : Type*} (s : Finset ι) {P : ι → TrigPoly2 Mβ Mθ R}
    (h : ∀ c ∈ s, (P c).IsEvenAtβ a) : (∑ c ∈ s, P c).IsEvenAtβ a := fun θ x ↦ by
  simp only [eval_sum]
  exact IsEvenAt.sum s (F := fun c β ↦ (P c).eval β θ) (fun c hc ↦ h c hc θ) x

theorem IsOddAtβ.sum {ι : Type*} (s : Finset ι) {P : ι → TrigPoly2 Mβ Mθ R}
    (h : ∀ c ∈ s, (P c).IsOddAtβ a) : (∑ c ∈ s, P c).IsOddAtβ a := fun θ x ↦ by
  simp only [eval_sum]
  exact IsOddAt.sum s (F := fun c β ↦ (P c).eval β θ) (fun c hc ↦ h c hc θ) x

theorem IsEvenAtθ.sum {ι : Type*} (s : Finset ι) {P : ι → TrigPoly2 Mβ Mθ R}
    (h : ∀ c ∈ s, (P c).IsEvenAtθ a) : (∑ c ∈ s, P c).IsEvenAtθ a := fun β x ↦ by
  simp only [eval_sum]
  exact IsEvenAt.sum s (F := fun c θ ↦ (P c).eval β θ) (fun c hc ↦ h c hc β) x

theorem IsOddAtθ.sum {ι : Type*} (s : Finset ι) {P : ι → TrigPoly2 Mβ Mθ R}
    (h : ∀ c ∈ s, (P c).IsOddAtθ a) : (∑ c ∈ s, P c).IsOddAtθ a := fun β x ↦ by
  simp only [eval_sum]
  exact IsOddAt.sum s (F := fun c θ ↦ (P c).eval β θ) (fun c hc ↦ h c hc β) x

/-- The `β`-derivative of a table even in `β` about `a` is odd there. -/
theorem IsEvenAtβ.dβ (hp : p.IsEvenAtβ a) : p.dβ.IsOddAtβ a :=
  fun θ ↦ (hp θ).hasDerivAt fun β ↦ hasDerivAt_eval_β p β θ

/-- The `β`-derivative of a table odd in `β` about `a` is even there. -/
theorem IsOddAtβ.dβ (hp : p.IsOddAtβ a) : p.dβ.IsEvenAtβ a :=
  fun θ ↦ (hp θ).hasDerivAt fun β ↦ hasDerivAt_eval_β p β θ

/-- The `θ`-derivative of a table even in `θ` about `a` is odd there. -/
theorem IsEvenAtθ.dθ (hp : p.IsEvenAtθ a) : p.dθ.IsOddAtθ a :=
  fun β ↦ (hp β).hasDerivAt fun θ ↦ hasDerivAt_eval_θ p β θ

/-- The `θ`-derivative of a table odd in `θ` about `a` is even there. -/
theorem IsOddAtθ.dθ (hp : p.IsOddAtθ a) : p.dθ.IsEvenAtθ a :=
  fun β ↦ (hp β).hasDerivAt fun θ ↦ hasDerivAt_eval_θ p β θ

/-- The `θ`-derivative keeps the parity in `β`. -/
theorem IsEvenAtβ.dθ (hp : p.IsEvenAtβ a) : p.dθ.IsEvenAtβ a := fun θ x ↦ by
  have h : p.eval (2 * a - x) = p.eval x := funext fun t ↦ hp t x
  have h' := hasDerivAt_eval_θ p (2 * a - x) θ
  rw [h] at h'
  exact h'.unique (hasDerivAt_eval_θ p x θ)

/-- The `θ`-derivative keeps the parity in `β`. -/
theorem IsOddAtβ.dθ (hp : p.IsOddAtβ a) : p.dθ.IsOddAtβ a := fun θ x ↦ by
  have h : p.eval (2 * a - x) = fun t ↦ -p.eval x t := funext fun t ↦ hp t x
  have h' := hasDerivAt_eval_θ p (2 * a - x) θ
  rw [h] at h'
  exact h'.unique (hasDerivAt_eval_θ p x θ).neg

/-- The `β`-derivative keeps the parity in `θ`. -/
theorem IsEvenAtθ.dβ (hp : p.IsEvenAtθ a) : p.dβ.IsEvenAtθ a := fun β x ↦ by
  have h : (fun t ↦ p.eval t (2 * a - x)) = fun t ↦ p.eval t x := funext fun t ↦ hp t x
  have h' := hasDerivAt_eval_β p β (2 * a - x)
  rw [h] at h'
  exact h'.unique (hasDerivAt_eval_β p β x)

/-- The `β`-derivative keeps the parity in `θ`. -/
theorem IsOddAtθ.dβ (hp : p.IsOddAtθ a) : p.dβ.IsOddAtθ a := fun β x ↦ by
  have h : (fun t ↦ p.eval t (2 * a - x)) = fun t ↦ -p.eval t x := funext fun t ↦ hp t x
  have h' := hasDerivAt_eval_β p β (2 * a - x)
  rw [h] at h'
  exact h'.unique (hasDerivAt_eval_β p β x).neg

/-! ### Parity from the support of the coefficients -/

/-- If every nonzero coefficient has `(-1)^i = s`, then `p (-β, θ) = s p (β, θ)`. -/
theorem eval_neg_β_of_coeff {s : ℝ}
    (h : ∀ i j k l, p.coeff i j k l ≠ 0 → (-1 : ℝ) ^ (i : ℕ) = s) (β θ : ℝ) :
    p.eval (-β) θ = s * p.eval β θ := by
  simp only [eval, mul_sum]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
    sum_congr rfl fun l _ ↦ ?_
  by_cases hc : p.coeff i j k l = 0
  · simp [hc]
  · rw [trigMode_mul_neg, ← h i j k l hc]
    ring

/-- If every nonzero coefficient has `(-1)^j = s`, then `p (β, -θ) = s p (β, θ)`. -/
theorem eval_neg_θ_of_coeff {s : ℝ}
    (h : ∀ i j k l, p.coeff i j k l ≠ 0 → (-1 : ℝ) ^ (j : ℕ) = s) (β θ : ℝ) :
    p.eval β (-θ) = s * p.eval β θ := by
  simp only [eval, mul_sum]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
    sum_congr rfl fun l _ ↦ ?_
  by_cases hc : p.coeff i j k l = 0
  · simp [hc]
  · rw [trigMode_mul_neg, ← h i j k l hc]
    ring

/-- If every nonzero coefficient has `(-1)^(i + k) = s`, then `p (π - β, θ) = s p (β, θ)`. -/
theorem eval_pi_sub_β_of_coeff {s : ℝ}
    (h : ∀ i j k l, p.coeff i j k l ≠ 0 → (-1 : ℝ) ^ ((i : ℕ) + k) = s) (β θ : ℝ) :
    p.eval (Real.pi - β) θ = s * p.eval β θ := by
  simp only [eval, mul_sum]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
    sum_congr rfl fun l _ ↦ ?_
  by_cases hc : p.coeff i j k l = 0
  · simp [hc]
  · rw [trigMode_mul_pi_sub, ← h i j k l hc]
    ring

/-- If every nonzero coefficient has `(-1)^(j + l) = s`, then `p (β, π - θ) = s p (β, θ)`. -/
theorem eval_pi_sub_θ_of_coeff {s : ℝ}
    (h : ∀ i j k l, p.coeff i j k l ≠ 0 → (-1 : ℝ) ^ ((j : ℕ) + l) = s) (β θ : ℝ) :
    p.eval β (Real.pi - θ) = s * p.eval β θ := by
  simp only [eval, mul_sum]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦
    sum_congr rfl fun l _ ↦ ?_
  by_cases hc : p.coeff i j k l = 0
  · simp [hc]
  · rw [trigMode_mul_pi_sub, ← h i j k l hc]
    ring

private theorem two_mul_zero_sub (x : ℝ) : 2 * 0 - x = -x := by ring

/-- `2 (π/2) - x = π - x`, the reflection of the parity relations at `π/2`. -/
theorem two_mul_pi_div_two_sub (x : ℝ) : 2 * (Real.pi / 2) - x = Real.pi - x := by ring

/-- No sines in `β`: even in `β` about `0`. -/
theorem isEvenAtβ_zero_of_coeff (h : ∀ j k l, p.coeff 1 j k l = 0) : p.IsEvenAtβ 0 :=
  fun θ x ↦ by
    simp only [two_mul_zero_sub]
    rw [eval_neg_β_of_coeff (s := 1) (fun i j k l hc ↦ ?_), one_mul]
    fin_cases i
    · simp
    · exact absurd (h j k l) hc

/-- No cosines in `β`: odd in `β` about `0`. -/
theorem isOddAtβ_zero_of_coeff (h : ∀ j k l, p.coeff 0 j k l = 0) : p.IsOddAtβ 0 :=
  fun θ x ↦ by
    simp only [two_mul_zero_sub]
    rw [eval_neg_β_of_coeff (s := -1) (fun i j k l hc ↦ ?_), neg_one_mul]
    fin_cases i
    · exact absurd (h j k l) hc
    · simp

/-- No sines in `θ`: even in `θ` about `0`. -/
theorem isEvenAtθ_zero_of_coeff (h : ∀ i k l, p.coeff i 1 k l = 0) : p.IsEvenAtθ 0 :=
  fun β x ↦ by
    simp only [two_mul_zero_sub]
    rw [eval_neg_θ_of_coeff (s := 1) (fun i j k l hc ↦ ?_), one_mul]
    fin_cases j
    · simp
    · exact absurd (h i k l) hc

/-- No cosines in `θ`: odd in `θ` about `0`. -/
theorem isOddAtθ_zero_of_coeff (h : ∀ i k l, p.coeff i 0 k l = 0) : p.IsOddAtθ 0 :=
  fun β x ↦ by
    simp only [two_mul_zero_sub]
    rw [eval_neg_θ_of_coeff (s := -1) (fun i j k l hc ↦ ?_), neg_one_mul]
    fin_cases j
    · exact absurd (h i k l) hc
    · simp

/-- Only `cos (kβ)` with `k` even and `sin (kβ)` with `k` odd: even in `β` about `π/2`. -/
theorem isEvenAtβ_pi_div_two_of_coeff (h : ∀ i j k l, Odd (i.val + k.val) → p.coeff i j k l = 0) :
    p.IsEvenAtβ (Real.pi / 2) := fun θ x ↦ by
  simp only [two_mul_pi_div_two_sub]
  rw [eval_pi_sub_β_of_coeff (s := 1) (fun i j k l hc ↦ ?_), one_mul]
  rcases Nat.even_or_odd ((i : ℕ) + k) with he | ho
  · exact he.neg_one_pow
  · exact absurd (h i j k l ho) hc

/-- Only `cos (kβ)` with `k` odd and `sin (kβ)` with `k` even: odd in `β` about `π/2`. -/
theorem isOddAtβ_pi_div_two_of_coeff (h : ∀ i j k l, Even (i.val + k.val) → p.coeff i j k l = 0) :
    p.IsOddAtβ (Real.pi / 2) := fun θ x ↦ by
  simp only [two_mul_pi_div_two_sub]
  rw [eval_pi_sub_β_of_coeff (s := -1) (fun i j k l hc ↦ ?_), neg_one_mul]
  rcases Nat.even_or_odd ((i : ℕ) + k) with he | ho
  · exact absurd (h i j k l he) hc
  · exact ho.neg_one_pow

/-- Only `cos (lθ)` with `l` even and `sin (lθ)` with `l` odd: even in `θ` about `π/2`. -/
theorem isEvenAtθ_pi_div_two_of_coeff (h : ∀ i j k l, Odd (j.val + l.val) → p.coeff i j k l = 0) :
    p.IsEvenAtθ (Real.pi / 2) := fun β x ↦ by
  simp only [two_mul_pi_div_two_sub]
  rw [eval_pi_sub_θ_of_coeff (s := 1) (fun i j k l hc ↦ ?_), one_mul]
  rcases Nat.even_or_odd ((j : ℕ) + l) with he | ho
  · exact he.neg_one_pow
  · exact absurd (h i j k l ho) hc

/-- Only `cos (lθ)` with `l` odd and `sin (lθ)` with `l` even: odd in `θ` about `π/2`. -/
theorem isOddAtθ_pi_div_two_of_coeff (h : ∀ i j k l, Even (j.val + l.val) → p.coeff i j k l = 0) :
    p.IsOddAtθ (Real.pi / 2) := fun β x ↦ by
  simp only [two_mul_pi_div_two_sub]
  rw [eval_pi_sub_θ_of_coeff (s := -1) (fun i j k l hc ↦ ?_), neg_one_mul]
  rcases Nat.even_or_odd ((j : ℕ) + l) with he | ho
  · exact absurd (h i j k l he) hc
  · exact ho.neg_one_pow

section Monomial

variable {i j : Fin 2} {k : Fin (Mβ + 1)} {l : Fin (Mθ + 1)} (c : R)

theorem isEvenAtβ_zero_monomial (hi : i = 0) : (monomial i j k l c).IsEvenAtβ 0 :=
  isEvenAtβ_zero_of_coeff fun _ _ _ ↦ by simp [monomial, hi]

theorem isOddAtβ_zero_monomial (hi : i = 1) : (monomial i j k l c).IsOddAtβ 0 :=
  isOddAtβ_zero_of_coeff fun _ _ _ ↦ by simp [monomial, hi]

theorem isEvenAtθ_zero_monomial (hj : j = 0) : (monomial i j k l c).IsEvenAtθ 0 :=
  isEvenAtθ_zero_of_coeff fun _ _ _ ↦ by simp [monomial, hj]

theorem isOddAtθ_zero_monomial (hj : j = 1) : (monomial i j k l c).IsOddAtθ 0 :=
  isOddAtθ_zero_of_coeff fun _ _ _ ↦ by simp [monomial, hj]

theorem isEvenAtβ_pi_div_two_monomial (h : Even (i.val + k.val)) :
    (monomial i j k l c).IsEvenAtβ (Real.pi / 2) :=
  isEvenAtβ_pi_div_two_of_coeff fun i' j' k' l' ho ↦ by
    simp only [monomial]
    split_ifs with h'
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
      exact absurd h (Nat.not_even_iff_odd.mpr ho)
    · rfl

theorem isOddAtβ_pi_div_two_monomial (h : Odd (i.val + k.val)) :
    (monomial i j k l c).IsOddAtβ (Real.pi / 2) :=
  isOddAtβ_pi_div_two_of_coeff fun i' j' k' l' he ↦ by
    simp only [monomial]
    split_ifs with h'
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
      exact absurd h (Nat.not_odd_iff_even.mpr he)
    · rfl

theorem isEvenAtθ_pi_div_two_monomial (h : Even (j.val + l.val)) :
    (monomial i j k l c).IsEvenAtθ (Real.pi / 2) :=
  isEvenAtθ_pi_div_two_of_coeff fun i' j' k' l' ho ↦ by
    simp only [monomial]
    split_ifs with h'
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
      exact absurd h (Nat.not_even_iff_odd.mpr ho)
    · rfl

theorem isOddAtθ_pi_div_two_monomial (h : Odd (j.val + l.val)) :
    (monomial i j k l c).IsOddAtθ (Real.pi / 2) :=
  isOddAtθ_pi_div_two_of_coeff fun i' j' k' l' he ↦ by
    simp only [monomial]
    split_ifs with h'
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
      exact absurd h (Nat.not_odd_iff_even.mpr he)
    · rfl

end Monomial

/-! ### Sections and even cosine series -/

/-- The coefficient of `trigMode i (k β)` in the section `β ↦ p.eval β θ`; zero past `Mβ`. -/
def sectionβ (p : TrigPoly2 Mβ Mθ R) (θ : ℝ) (i : Fin 2) (k : ℕ) : ℝ :=
  ∑ j, ∑ l ∈ range (Mθ + 1), algebraMap R ℝ (p.coeffN i j k l) * trigMode j (l * θ)

/-- The coefficient of `trigMode j (l θ)` in the section `θ ↦ p.eval β θ`; zero past `Mθ`. -/
def sectionθ (p : TrigPoly2 Mβ Mθ R) (β : ℝ) (j : Fin 2) (l : ℕ) : ℝ :=
  ∑ i, ∑ k ∈ range (Mβ + 1), algebraMap R ℝ (p.coeffN i j k l) * trigMode i (k * β)

/-- Every section in `β` is the trigonometric series of `IsEvenCosineSeries.of_trigSeries`. -/
theorem eval_eq_sum_sectionβ (p : TrigPoly2 Mβ Mθ R) (θ β : ℝ) :
    p.eval β θ = ∑ k ∈ range (Mβ + 1),
      (p.sectionβ θ 0 k * Real.cos (k * β) + p.sectionβ θ 1 k * Real.sin (k * β)) := by
  have h : ∀ k : ℕ, p.sectionβ θ 0 k * Real.cos (k * β) + p.sectionβ θ 1 k * Real.sin (k * β) =
      ∑ i, p.sectionβ θ i k * trigMode i (k * β) := fun k ↦
    (Fin.sum_univ_two (fun i ↦ p.sectionβ θ i k * trigMode i (k * β))).symm
  simp only [h]
  simp only [sectionβ, sum_mul, eval_eq_sum_range]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [sum_comm]
  exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ by ring

/-- Every section in `θ` is the trigonometric series of `IsEvenCosineSeries.of_trigSeries`. -/
theorem eval_eq_sum_sectionθ (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    p.eval β θ = ∑ l ∈ range (Mθ + 1),
      (p.sectionθ β 0 l * Real.cos (l * θ) + p.sectionθ β 1 l * Real.sin (l * θ)) := by
  have h : ∀ l : ℕ, p.sectionθ β 0 l * Real.cos (l * θ) + p.sectionθ β 1 l * Real.sin (l * θ) =
      ∑ j, p.sectionθ β j l * trigMode j (l * θ) := fun l ↦
    (Fin.sum_univ_two (fun j ↦ p.sectionθ β j l * trigMode j (l * θ))).symm
  simp only [h]
  simp only [sectionθ, sum_mul, eval_eq_sum_range]
  conv_rhs => rw [sum_comm]
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [sum_comm]

/-- Even in `β` about `0` and `π/2`: every section in `β` is an even cosine series. -/
theorem isEvenCosineSeries_β (h0 : p.IsEvenAtβ 0) (hπ : p.IsEvenAtβ (Real.pi / 2)) (θ : ℝ) :
    IsEvenCosineSeries (Mβ / 2) (fun β ↦ p.eval β θ) :=
  IsEvenCosineSeries.of_trigSeries (p.sectionβ θ 0) (p.sectionβ θ 1)
    (fun β ↦ p.eval_eq_sum_sectionβ θ β) (fun x ↦ (h0 θ).apply_neg x)
    (fun x ↦ (hπ θ).apply_pi_sub x)

/-- Even in `θ` about `0` and `π/2`: every section in `θ` is an even cosine series. -/
theorem isEvenCosineSeries_θ (h0 : p.IsEvenAtθ 0) (hπ : p.IsEvenAtθ (Real.pi / 2)) (β : ℝ) :
    IsEvenCosineSeries (Mθ / 2) (p.eval β) :=
  IsEvenCosineSeries.of_trigSeries (p.sectionθ β 0) (p.sectionθ β 1)
    (fun θ ↦ p.eval_eq_sum_sectionθ β θ) (fun x ↦ (h0 β).apply_neg x)
    (fun x ↦ (hπ β).apply_pi_sub x)

private theorem isEvenAtβ_mul_self {a : ℝ} (h : p.IsEvenAtβ a ∨ p.IsOddAtβ a) :
    (p.mul p).IsEvenAtβ a :=
  h.elim (fun h ↦ h.mul h) fun h ↦ h.mul h

private theorem isEvenAtθ_mul_self {a : ℝ} (h : p.IsEvenAtθ a ∨ p.IsOddAtθ a) :
    (p.mul p).IsEvenAtθ a :=
  h.elim (fun h ↦ h.mul h) fun h ↦ h.mul h

/-- Even or odd in `β` about `0` and about `π/2`: the squared sections in `β` are even cosine
series of degree `Mβ`. -/
theorem isEvenCosineSeries_sq_β (h0 : p.IsEvenAtβ 0 ∨ p.IsOddAtβ 0)
    (hπ : p.IsEvenAtβ (Real.pi / 2) ∨ p.IsOddAtβ (Real.pi / 2)) (θ : ℝ) :
    IsEvenCosineSeries Mβ (fun β ↦ p.eval β θ ^ 2) :=
  ((isEvenCosineSeries_β (isEvenAtβ_mul_self h0) (isEvenAtβ_mul_self hπ) θ).mono
    (by omega)).congr fun β ↦ by rw [eval_mul, sq]

/-- Even or odd in `θ` about `0` and about `π/2`: the squared sections in `θ` are even cosine
series of degree `Mθ`. -/
theorem isEvenCosineSeries_sq_θ (h0 : p.IsEvenAtθ 0 ∨ p.IsOddAtθ 0)
    (hπ : p.IsEvenAtθ (Real.pi / 2) ∨ p.IsOddAtθ (Real.pi / 2)) (β : ℝ) :
    IsEvenCosineSeries Mθ (fun θ ↦ p.eval β θ ^ 2) :=
  ((isEvenCosineSeries_θ (isEvenAtθ_mul_self h0) (isEvenAtθ_mul_self hπ) β).mono
    (by omega)).congr fun θ ↦ by rw [eval_mul, sq]

/-- The exact quadrant rule for a sum of squares of tables, each even or odd about `0` and
about `π/2` in each variable: the trapezoid rule in `β` with `Mβ < 2N` and the sine rule in `θ`
with `Mθ ≤ P` integrate `(∑_c p_c (β, θ)²) sin θ` over `[0, π/2]²`. -/
theorem integral_integral_sum_sq_mul_sin_eq_rule {ι : Type*} (s : Finset ι)
    (p : ι → TrigPoly2 Mβ Mθ R) {N P : ℕ} (hN : Mβ < 2 * N) (hP : 0 < P) (hMP : Mθ ≤ P)
    (hβ0 : ∀ c ∈ s, (p c).IsEvenAtβ 0 ∨ (p c).IsOddAtβ 0)
    (hβπ : ∀ c ∈ s, (p c).IsEvenAtβ (Real.pi / 2) ∨ (p c).IsOddAtβ (Real.pi / 2))
    (hθ0 : ∀ c ∈ s, (p c).IsEvenAtθ 0 ∨ (p c).IsOddAtθ 0)
    (hθπ : ∀ c ∈ s, (p c).IsEvenAtθ (Real.pi / 2) ∨ (p c).IsOddAtθ (Real.pi / 2)) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2),
        (∑ c ∈ s, (p c).eval β θ ^ 2) * Real.sin θ =
      ∑ j : Fin (N + 1), ∑ n : Fin (P + 1), quarterTrapezoidWeight N j * quarterSinWeight P n *
        ∑ c ∈ s, (p c).eval (j * Real.pi / (2 * N)) (n * Real.pi / (2 * P)) ^ 2 :=
  integral_integral_mul_sin_eq_rule (f := fun β θ ↦ ∑ c ∈ s, (p c).eval β θ ^ 2) hN hP hMP
    (fun θ ↦ IsEvenCosineSeries.sum s fun c hc ↦
      isEvenCosineSeries_sq_β (hβ0 c hc) (hβπ c hc) θ)
    (fun β ↦ IsEvenCosineSeries.sum s fun c hc ↦
      isEvenCosineSeries_sq_θ (hθ0 c hc) (hθπ c hc) β)

end Eval

end TrigPoly2

end PDE.Analysis
