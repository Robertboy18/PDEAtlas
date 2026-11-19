/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Quotient

/-!
# Coefficient changes, smoothness, derivatives and signed parities of trigonometric tables

* A ring homomorphism of the coefficients commutes with sums, scalar multiples, products,
  padding, partial derivatives and the quotients by `sin` (`TrigPoly2.map_mul`,
  `TrigPoly2.map_dβ`, `TrigPoly2.map_divSinβ`, ...), so a table built from rational data is the
  image of a rational table under `Rat.castHom ℝ`.
* The coordinate tables `cosβ`, `sinβ`, `cosθ`, `sinθ` have the values of their names.
* The value `(β, θ) ↦ p.eval β θ` is smooth (`contDiff_eval`); the derivatives of the weighted
  sections `t ↦ cos t · p (t, θ)` and `t ↦ c · p (β, t)` are values of the derivative tables, and
  a quotient identity `q · sin = p` passes to the derivatives (`eval_dθ_mul_sin_θ`, ...).
* `ParityAtβ a e p` states that every section in `β` is even (`e = true`) or odd (`e = false`)
  about `a`; it is closed under sums, scalar multiples and padding with the same sign, under
  products with the product of the signs, and under `dβ` with the opposite sign
  (`ParityAtβ.mul`, `ParityAtβ.dβ`), and the quotients by `sin` keep or fix it
  (`ParityAtβ.divSinθ`, `parityAtβ_zero_divSinβ`). With the signs written as booleans these
  rules are deterministic; the tactic `trig_parity` of `TrigPoly2Parity` composes them.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset

variable {Mβ Mθ Nβ Nθ : ℕ} {R : Type}

/-! ### The coordinate tables -/

section Coordinates

variable [Zero R] [One R]

/-- `cos β` as a table. -/
def cosβ : TrigPoly2 1 0 R := monomial 0 0 1 0 1

/-- `sin β` as a table. -/
def sinβ : TrigPoly2 1 0 R := monomial 1 0 1 0 1

/-- `cos θ` as a table. -/
def cosθ : TrigPoly2 0 1 R := monomial 0 0 0 1 1

/-- `sin θ` as a table. -/
def sinθ : TrigPoly2 0 1 R := monomial 0 1 0 1 1

end Coordinates

variable [Field R]

/-! ### Supports -/

/-- The `θ`-derivative of a table without sines in `θ` has no cosines in `θ`. -/
theorem coeff_dθ_zero_of_coeff_one {p : TrigPoly2 Mβ Mθ R} (h : ∀ i k l, p.coeff i 1 k l = 0)
    (i : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) : p.dθ.coeff i 0 k l = 0 := by
  simp [dθ, h]

/-- The quotient by `sin β` avoids every mode in `θ` that the sines in `β` of its numerator
avoid. -/
theorem coeff_divSinβ_of_coeff_one {p : TrigPoly2 Mβ Mθ R} {j : Fin 2}
    (h : ∀ k l, p.coeff 1 j k l = 0) (i : Fin 2) (n : Fin (Mβ - 1 + 1)) (l : Fin (Mθ + 1)) :
    (divSinβ p).coeff i j n l = 0 := by
  have hN : ∀ k : ℕ, p.coeffN 1 j k l = 0 := fun k ↦ by
    unfold coeffN
    split_ifs with hkl
    · exact h ⟨k, hkl.1⟩ ⟨l, hkl.2⟩
    · rfl
  simp [divSinβ, hN]

/-! ### Change of coefficients -/

section Map

variable {S : Type} [Field S] (f : R →+* S)

theorem coeffN_map (p : TrigPoly2 Mβ Mθ R) (i j : Fin 2) (k l : ℕ) :
    (p.map f).coeffN i j k l = f (p.coeffN i j k l) := by
  unfold coeffN
  split_ifs <;> simp [map]

@[simp] theorem map_zero : (0 : TrigPoly2 Mβ Mθ R).map f = 0 := by
  ext; simp [map]

@[simp] theorem map_add (p q : TrigPoly2 Mβ Mθ R) : (p + q).map f = p.map f + q.map f := by
  ext; simp [map]

@[simp] theorem map_neg (p : TrigPoly2 Mβ Mθ R) : (-p).map f = -p.map f := by
  ext; simp [map]

@[simp] theorem map_sub (p q : TrigPoly2 Mβ Mθ R) : (p - q).map f = p.map f - q.map f := by
  ext; simp [map]

@[simp] theorem map_smul (c : R) (p : TrigPoly2 Mβ Mθ R) : (c • p).map f = f c • p.map f := by
  ext; simp [map]

theorem map_sum {ι : Type*} (s : Finset ι) (g : ι → TrigPoly2 Mβ Mθ R) :
    (∑ x ∈ s, g x).map f = ∑ x ∈ s, (g x).map f := by
  ext i j k l
  simp only [map, coeff_sum, _root_.map_sum]

@[simp] theorem map_monomial (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (c : R) :
    (monomial i j k l c).map f = monomial i j k l (f c) := by
  ext; simp only [map, monomial]; split_ifs <;> simp

@[simp] theorem map_resize (p : TrigPoly2 Mβ Mθ R) :
    (p.resize : TrigPoly2 Nβ Nθ R).map f = ((p.map f).resize : TrigPoly2 Nβ Nθ S) := by
  ext i j k l
  exact (coeffN_map f p i j k l).symm

@[simp] theorem map_dβ (p : TrigPoly2 Mβ Mθ R) : p.dβ.map f = (p.map f).dβ := by
  ext i; simp only [map, dβ]; split_ifs <;> simp

@[simp] theorem map_dθ (p : TrigPoly2 Mβ Mθ R) : p.dθ.map f = (p.map f).dθ := by
  ext i j; simp only [map, dθ]; split_ifs <;> simp

@[simp] theorem map_divSinβ (p : TrigPoly2 Mβ Mθ R) :
    (divSinβ p).map f = divSinβ (p.map f) := by
  ext i j n l
  change f ((divSinβ p).coeff i j n l) = (divSinβ (p.map f)).coeff i j n l
  simp only [divSinβ, coeffN_map]
  split_ifs <;> simp

@[simp] theorem map_divSinθ (p : TrigPoly2 Mβ Mθ R) :
    (divSinθ p).map f = divSinθ (p.map f) := by
  ext i j k n
  change f ((divSinθ p).coeff i j k n) = (divSinθ (p.map f)).coeff i j k n
  simp only [divSinθ, coeffN_map]
  split_ifs <;> simp

theorem map_mulTerm (i j : Fin 2) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) (i' j' : Fin 2)
    (k' : Fin (Nβ + 1)) (l' : Fin (Nθ + 1)) (c : R) :
    (mulTerm i j k l i' j' k' l' c).map f = mulTerm i j k l i' j' k' l' (f c) := by
  simp only [mulTerm, map_add, map_monomial, map_div₀, _root_.map_mul, map_trigSumSign,
    map_trigDiffSign, map_ofNat]

@[simp] theorem map_mul (p : TrigPoly2 Mβ Mθ R) (q : TrigPoly2 Nβ Nθ R) :
    (p.mul q).map f = (p.map f).mul (q.map f) := by
  simp only [mul, map_sum, map_mulTerm, _root_.map_mul]
  rfl

@[simp] theorem map_cosβ : (cosβ : TrigPoly2 1 0 R).map f = cosβ := by
  simp [cosβ]

@[simp] theorem map_sinβ : (sinβ : TrigPoly2 1 0 R).map f = sinβ := by
  simp [sinβ]

@[simp] theorem map_cosθ : (cosθ : TrigPoly2 0 1 R).map f = cosθ := by
  simp [cosθ]

@[simp] theorem map_sinθ : (sinθ : TrigPoly2 0 1 R).map f = sinθ := by
  simp [sinθ]

end Map

variable [Algebra R ℝ]

@[simp] theorem eval_cosβ (β θ : ℝ) : (cosβ : TrigPoly2 1 0 R).eval β θ = Real.cos β := by
  simp [cosβ]

@[simp] theorem eval_sinβ (β θ : ℝ) : (sinβ : TrigPoly2 1 0 R).eval β θ = Real.sin β := by
  simp [sinβ]

@[simp] theorem eval_cosθ (β θ : ℝ) : (cosθ : TrigPoly2 0 1 R).eval β θ = Real.cos θ := by
  simp [cosθ]

@[simp] theorem eval_sinθ (β θ : ℝ) : (sinθ : TrigPoly2 0 1 R).eval β θ = Real.sin θ := by
  simp [sinθ]

/-! ### Smoothness -/

private theorem contDiff_trigMode {n : WithTop ℕ∞} (i : Fin 2) : ContDiff ℝ n (trigMode i) := by
  fin_cases i
  · exact Real.contDiff_cos
  · exact Real.contDiff_sin

/-- The value of a table is a smooth function of `(β, θ)`. -/
theorem contDiff_eval (p : TrigPoly2 Mβ Mθ R) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : ℝ × ℝ ↦ p.eval x.1 x.2) := by
  unfold eval
  refine ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦ ContDiff.sum fun k _ ↦
    ContDiff.sum fun l _ ↦ ?_
  exact (contDiff_const.mul ((contDiff_trigMode i).comp (contDiff_const.mul contDiff_fst))).mul
    ((contDiff_trigMode j).comp (contDiff_const.mul contDiff_snd))

/-! ### Derivatives of weighted sections -/

/-- The derivative of `t ↦ cos t · p (t, θ)`. -/
theorem hasDerivAt_cos_mul_eval_β (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    HasDerivAt (fun t ↦ Real.cos t * p.eval t θ)
      (-Real.sin β * p.eval β θ + Real.cos β * p.dβ.eval β θ) β := by
  convert (Real.hasDerivAt_cos β).fun_mul (hasDerivAt_eval_β p β θ) using 1

theorem deriv_cos_mul_eval_β (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    deriv (fun t ↦ Real.cos t * p.eval t θ) β =
      -Real.sin β * p.eval β θ + Real.cos β * p.dβ.eval β θ :=
  (hasDerivAt_cos_mul_eval_β p β θ).deriv

theorem deriv_deriv_cos_mul_eval_β (p : TrigPoly2 Mβ Mθ R) (β θ : ℝ) :
    deriv (deriv fun t ↦ Real.cos t * p.eval t θ) β =
      -Real.cos β * p.eval β θ - 2 * (Real.sin β * p.dβ.eval β θ) +
        Real.cos β * p.dβ.dβ.eval β θ := by
  rw [show (deriv fun t ↦ Real.cos t * p.eval t θ) =
      fun t ↦ -Real.sin t * p.eval t θ + Real.cos t * p.dβ.eval t θ from
    funext fun t ↦ deriv_cos_mul_eval_β p t θ]
  have h := ((Real.hasDerivAt_sin β).fun_neg.fun_mul (hasDerivAt_eval_β p β θ)).fun_add
    ((Real.hasDerivAt_cos β).fun_mul (hasDerivAt_eval_β p.dβ β θ))
  rw [h.deriv]
  ring

theorem deriv_const_mul_eval_θ (p : TrigPoly2 Mβ Mθ R) (c β θ : ℝ) :
    deriv (fun t ↦ c * p.eval β t) θ = c * p.dθ.eval β θ :=
  ((hasDerivAt_eval_θ p β θ).const_mul c).deriv

theorem deriv_deriv_const_mul_eval_θ (p : TrigPoly2 Mβ Mθ R) (c β θ : ℝ) :
    deriv (deriv fun t ↦ c * p.eval β t) θ = c * p.dθ.dθ.eval β θ := by
  rw [show (deriv fun t ↦ c * p.eval β t) = fun t ↦ c * p.dθ.eval β t from
    funext fun t ↦ deriv_const_mul_eval_θ p c β t, deriv_const_mul_eval_θ]

theorem deriv_sin_mul_const_mul_eval_θ (p : TrigPoly2 Mβ Mθ R) (c β θ : ℝ) :
    deriv (fun t ↦ Real.sin t * (c * p.eval β t)) θ =
      Real.cos θ * (c * p.eval β θ) + Real.sin θ * (c * p.dθ.eval β θ) :=
  ((Real.hasDerivAt_sin θ).fun_mul ((hasDerivAt_eval_θ p β θ).const_mul c)).deriv

/-! ### Derivatives of quotient identities -/

/-- A quotient identity in `β` passes to the `θ`-derivatives. -/
theorem eval_dθ_mul_sin_β {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ β θ, q.eval β θ * Real.sin β = p.eval β θ) (β θ : ℝ) :
    q.dθ.eval β θ * Real.sin β = p.dθ.eval β θ := by
  have hq := (hasDerivAt_eval_θ q β θ).mul_const (Real.sin β)
  rw [show (fun t ↦ q.eval β t * Real.sin β) = p.eval β from funext (h β)] at hq
  exact hq.unique (hasDerivAt_eval_θ p β θ)

/-- A quotient identity in `θ` passes to the `θ`-derivatives by the product rule. -/
theorem eval_dθ_mul_sin_θ {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ β θ, q.eval β θ * Real.sin θ = p.eval β θ) (β θ : ℝ) :
    q.dθ.eval β θ * Real.sin θ + q.eval β θ * Real.cos θ = p.dθ.eval β θ := by
  have hq := (hasDerivAt_eval_θ q β θ).fun_mul (Real.hasDerivAt_sin θ)
  rw [show (fun t ↦ q.eval β t * Real.sin t) = p.eval β from funext (h β)] at hq
  exact hq.unique (hasDerivAt_eval_θ p β θ)

/-- A quotient identity in `θ` passes to the second `θ`-derivatives. -/
theorem eval_dθ_dθ_mul_sin_θ {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ β θ, q.eval β θ * Real.sin θ = p.eval β θ) (β θ : ℝ) :
    q.dθ.dθ.eval β θ * Real.sin θ + 2 * (q.dθ.eval β θ * Real.cos θ) -
      q.eval β θ * Real.sin θ = p.dθ.dθ.eval β θ := by
  have h1 := eval_dθ_mul_sin_θ h
  have hq := ((hasDerivAt_eval_θ q.dθ β θ).fun_mul (Real.hasDerivAt_sin θ)).fun_add
    ((hasDerivAt_eval_θ q β θ).fun_mul (Real.hasDerivAt_cos θ))
  rw [show (fun t ↦ q.dθ.eval β t * Real.sin t + q.eval β t * Real.cos t) = p.dθ.eval β from
    funext (h1 β)] at hq
  rw [← hq.unique (hasDerivAt_eval_θ p.dθ β θ)]
  ring

/-! ### Parities with a sign -/

/-- Every section in `β` is even (`e = true`) or odd (`e = false`) about `a`. -/
def ParityAtβ (a : ℝ) (e : Bool) (p : TrigPoly2 Mβ Mθ R) : Prop :=
  ∀ θ x, p.eval (2 * a - x) θ = cond e 1 (-1) * p.eval x θ

/-- Every section in `θ` is even (`e = true`) or odd (`e = false`) about `a`. -/
def ParityAtθ (a : ℝ) (e : Bool) (p : TrigPoly2 Mβ Mθ R) : Prop :=
  ∀ β x, p.eval β (2 * a - x) = cond e 1 (-1) * p.eval β x

section Parity

variable {a : ℝ} {e e' g : Bool} {p q : TrigPoly2 Mβ Mθ R} {r : TrigPoly2 Nβ Nθ R}

theorem parityAtβ_true_iff : ParityAtβ a true p ↔ p.IsEvenAtβ a :=
  ⟨fun h θ x ↦ by simpa using h θ x, fun h θ x ↦ by simpa using h θ x⟩

theorem parityAtβ_false_iff : ParityAtβ a false p ↔ p.IsOddAtβ a :=
  ⟨fun h θ x ↦ by simpa using h θ x, fun h θ x ↦ by simpa using h θ x⟩

theorem parityAtθ_true_iff : ParityAtθ a true p ↔ p.IsEvenAtθ a :=
  ⟨fun h β x ↦ by simpa using h β x, fun h β x ↦ by simpa using h β x⟩

theorem parityAtθ_false_iff : ParityAtθ a false p ↔ p.IsOddAtθ a :=
  ⟨fun h β x ↦ by simpa using h β x, fun h β x ↦ by simpa using h β x⟩

theorem ParityAtβ.add (hp : ParityAtβ a e p) (hq : ParityAtβ a e q) : ParityAtβ a e (p + q) :=
  fun θ x ↦ by rw [eval_add, eval_add, hp, hq, mul_add]

theorem ParityAtβ.sub (hp : ParityAtβ a e p) (hq : ParityAtβ a e q) : ParityAtβ a e (p - q) :=
  fun θ x ↦ by rw [eval_sub, eval_sub, hp, hq, mul_sub]

theorem ParityAtβ.smul (c : R) (hp : ParityAtβ a e p) : ParityAtβ a e (c • p) :=
  fun θ x ↦ by rw [eval_smul, eval_smul, hp, mul_left_comm]

theorem ParityAtβ.mul (hp : ParityAtβ a e p) (hr : ParityAtβ a e' r) (hg : g = (e == e')) :
    ParityAtβ a g (p.mul r) := fun θ x ↦ by
  rw [eval_mul, eval_mul, hp, hr, hg]
  cases e <;> cases e' <;> simp

theorem ParityAtβ.resize (hp : ParityAtβ a e p) (h₁ : Mβ ≤ Nβ) (h₂ : Mθ ≤ Nθ) :
    ParityAtβ a e (p.resize : TrigPoly2 Nβ Nθ R) :=
  fun θ x ↦ by rw [eval_resize h₁ h₂, eval_resize h₁ h₂, hp]

theorem ParityAtβ.dβ (hp : ParityAtβ a e p) (hg : g = !e) : ParityAtβ a g p.dβ := by
  subst hg
  cases e
  · exact parityAtβ_true_iff.mpr (parityAtβ_false_iff.mp hp).dβ
  · exact parityAtβ_false_iff.mpr (parityAtβ_true_iff.mp hp).dβ

theorem ParityAtβ.dθ (hp : ParityAtβ a e p) : ParityAtβ a e p.dθ := by
  cases e
  · exact parityAtβ_false_iff.mpr (parityAtβ_false_iff.mp hp).dθ
  · exact parityAtβ_true_iff.mpr (parityAtβ_true_iff.mp hp).dθ

theorem ParityAtθ.add (hp : ParityAtθ a e p) (hq : ParityAtθ a e q) : ParityAtθ a e (p + q) :=
  fun β x ↦ by rw [eval_add, eval_add, hp, hq, mul_add]

theorem ParityAtθ.sub (hp : ParityAtθ a e p) (hq : ParityAtθ a e q) : ParityAtθ a e (p - q) :=
  fun β x ↦ by rw [eval_sub, eval_sub, hp, hq, mul_sub]

theorem ParityAtθ.smul (c : R) (hp : ParityAtθ a e p) : ParityAtθ a e (c • p) :=
  fun β x ↦ by rw [eval_smul, eval_smul, hp, mul_left_comm]

theorem ParityAtθ.mul (hp : ParityAtθ a e p) (hr : ParityAtθ a e' r) (hg : g = (e == e')) :
    ParityAtθ a g (p.mul r) := fun β x ↦ by
  rw [eval_mul, eval_mul, hp, hr, hg]
  cases e <;> cases e' <;> simp

theorem ParityAtθ.resize (hp : ParityAtθ a e p) (h₁ : Mβ ≤ Nβ) (h₂ : Mθ ≤ Nθ) :
    ParityAtθ a e (p.resize : TrigPoly2 Nβ Nθ R) :=
  fun β x ↦ by rw [eval_resize h₁ h₂, eval_resize h₁ h₂, hp]

theorem ParityAtθ.dθ (hp : ParityAtθ a e p) (hg : g = !e) : ParityAtθ a g p.dθ := by
  subst hg
  cases e
  · exact parityAtθ_true_iff.mpr (parityAtθ_false_iff.mp hp).dθ
  · exact parityAtθ_false_iff.mpr (parityAtθ_true_iff.mp hp).dθ

theorem ParityAtθ.dβ (hp : ParityAtθ a e p) : ParityAtθ a e p.dβ := by
  cases e
  · exact parityAtθ_false_iff.mpr (parityAtθ_false_iff.mp hp).dβ
  · exact parityAtθ_true_iff.mpr (parityAtθ_true_iff.mp hp).dβ

theorem parityAtβ_zero_sinβ : ParityAtβ 0 false (sinβ : TrigPoly2 1 0 R) :=
  fun _ x ↦ by simp [Real.sin_neg]

theorem parityAtβ_pi_div_two_sinβ : ParityAtβ (Real.pi / 2) true (sinβ : TrigPoly2 1 0 R) :=
  fun _ x ↦ by simp [two_mul_pi_div_two_sub, Real.sin_pi_sub]

theorem parityAtβ_zero_cosβ : ParityAtβ 0 true (cosβ : TrigPoly2 1 0 R) :=
  fun _ x ↦ by simp [Real.cos_neg]

theorem parityAtβ_pi_div_two_cosβ : ParityAtβ (Real.pi / 2) false (cosβ : TrigPoly2 1 0 R) :=
  fun _ x ↦ by simp [two_mul_pi_div_two_sub, Real.cos_pi_sub]

theorem parityAtβ_sinθ (a : ℝ) : ParityAtβ a true (sinθ : TrigPoly2 0 1 R) :=
  fun _ _ ↦ by simp

theorem parityAtβ_cosθ (a : ℝ) : ParityAtβ a true (cosθ : TrigPoly2 0 1 R) :=
  fun _ _ ↦ by simp

theorem parityAtθ_zero_sinθ : ParityAtθ 0 false (sinθ : TrigPoly2 0 1 R) :=
  fun _ x ↦ by simp [Real.sin_neg]

theorem parityAtθ_pi_div_two_sinθ : ParityAtθ (Real.pi / 2) true (sinθ : TrigPoly2 0 1 R) :=
  fun _ x ↦ by simp [two_mul_pi_div_two_sub, Real.sin_pi_sub]

theorem parityAtθ_zero_cosθ : ParityAtθ 0 true (cosθ : TrigPoly2 0 1 R) :=
  fun _ x ↦ by simp [Real.cos_neg]

theorem parityAtθ_pi_div_two_cosθ : ParityAtθ (Real.pi / 2) false (cosθ : TrigPoly2 0 1 R) :=
  fun _ x ↦ by simp [two_mul_pi_div_two_sub, Real.cos_pi_sub]

theorem parityAtθ_sinβ (a : ℝ) : ParityAtθ a true (sinβ : TrigPoly2 1 0 R) :=
  fun _ _ ↦ by simp

theorem parityAtθ_cosβ (a : ℝ) : ParityAtθ a true (cosβ : TrigPoly2 1 0 R) :=
  fun _ _ ↦ by simp

theorem parityAtβ_zero_table (a : ℝ) (e : Bool) : ParityAtβ a e (0 : TrigPoly2 Mβ Mθ R) :=
  fun _ _ ↦ by simp

theorem parityAtθ_zero_table (a : ℝ) (e : Bool) : ParityAtθ a e (0 : TrigPoly2 Mβ Mθ R) :=
  fun _ _ ↦ by simp

/-- The quotient by `sin β` is even in `β` about `0`. -/
theorem parityAtβ_zero_divSinβ (p : TrigPoly2 Mβ Mθ R) : ParityAtβ 0 true (divSinβ p) :=
  parityAtβ_true_iff.mpr (isEvenAtβ_zero_divSinβ p)

/-- The quotient by `sin β` keeps the parity in `β` about `π/2`. -/
theorem ParityAtβ.divSinβ_pi_div_two (hp : ParityAtβ (Real.pi / 2) e p)
    (h : ∀ j k l, p.coeff 0 j k l = 0) : ParityAtβ (Real.pi / 2) e (divSinβ p) := by
  cases e
  · exact parityAtβ_false_iff.mpr (isOddAtβ_pi_div_two_divSinβ h (parityAtβ_false_iff.mp hp))
  · exact parityAtβ_true_iff.mpr (isEvenAtβ_pi_div_two_divSinβ h (parityAtβ_true_iff.mp hp))

/-- The quotient by `sin β` keeps the parities in `θ`. -/
theorem ParityAtθ.divSinβ (hp : ParityAtθ a e p) (h : ∀ j k l, p.coeff 0 j k l = 0) :
    ParityAtθ a e (divSinβ p) := by
  cases e
  · exact parityAtθ_false_iff.mpr ((parityAtθ_false_iff.mp hp).divSinβ h)
  · exact parityAtθ_true_iff.mpr ((parityAtθ_true_iff.mp hp).divSinβ h)

/-- The quotient by `sin θ` is even in `θ` about `0`. -/
theorem parityAtθ_zero_divSinθ (p : TrigPoly2 Mβ Mθ R) : ParityAtθ 0 true (divSinθ p) :=
  parityAtθ_true_iff.mpr (isEvenAtθ_zero_divSinθ p)

/-- The quotient by `sin θ` keeps the parity in `θ` about `π/2`. -/
theorem ParityAtθ.divSinθ_pi_div_two (hp : ParityAtθ (Real.pi / 2) e p)
    (h : ∀ i k l, p.coeff i 0 k l = 0) : ParityAtθ (Real.pi / 2) e (divSinθ p) := by
  cases e
  · exact parityAtθ_false_iff.mpr (isOddAtθ_pi_div_two_divSinθ h (parityAtθ_false_iff.mp hp))
  · exact parityAtθ_true_iff.mpr (isEvenAtθ_pi_div_two_divSinθ h (parityAtθ_true_iff.mp hp))

/-- The quotient by `sin θ` keeps the parities in `β`. -/
theorem ParityAtβ.divSinθ (hp : ParityAtβ a e p) (h : ∀ i k l, p.coeff i 0 k l = 0) :
    ParityAtβ a e (divSinθ p) := by
  cases e
  · exact parityAtβ_false_iff.mpr ((parityAtβ_false_iff.mp hp).divSinθ h)
  · exact parityAtβ_true_iff.mpr ((parityAtβ_true_iff.mp hp).divSinθ h)

end Parity

end PDE.Analysis.TrigPoly2
