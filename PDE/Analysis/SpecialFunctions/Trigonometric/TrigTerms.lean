/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.Analysis.SpecialFunctions.Trigonometric.CosineQuadrature

/-!
# Sparse trigonometric sums and their integrals against `sin θ`

A `TrigTerm` is `c cos (f θ)` or `c sin (f θ)` with a rational coefficient and an integer
frequency, and a list of terms is their sum (`trigTermsEval`). Products of lists are lists again by
the product-to-sum identities (`trigTermsMul`, `trigTermsEval_trigTermsMul`). Each term integrates
against `sin θ` on `(0, π)` in closed form: `∫ cos (qθ) sin θ = (1 + (-1)^q) / (1 - q²)` and
`∫ sin (qθ) sin θ = ±π/2` at `q = ±1`, zero otherwise. So the integral of a list is a rational
number plus `π` times a rational number (`integral_trigTermsEval_mul_sin`). The coefficients stay
in the trigonometric basis, so sums of positive coefficients are evaluated without the
cancellation of the power basis.
-/

@[expose] public section

namespace PDE.Analysis

open CAS.Analysis
open Real
open scoped BigOperators

/-- A term `c cos (f θ)` (`isSin = false`) or `c sin (f θ)` (`isSin = true`). -/
structure TrigTerm where
  /-- The coefficient. -/
  coeff : ℚ
  /-- The integer frequency. -/
  freq : ℤ
  /-- Whether the term is a sine. -/
  isSin : Bool

namespace TrigTerm

/-- The value of a term at `θ`. -/
noncomputable def eval (t : TrigTerm) (θ : ℝ) : ℝ :=
  (t.coeff : ℝ) * (if t.isSin then Real.sin (t.freq * θ) else Real.cos (t.freq * θ))

/-- The product of two terms as two terms, by the product-to-sum identities. -/
def mul (s t : TrigTerm) : List TrigTerm :=
  let c := s.coeff * t.coeff / 2
  match s.isSin, t.isSin with
  | false, false => [⟨c, s.freq - t.freq, false⟩, ⟨c, s.freq + t.freq, false⟩]
  | true, true => [⟨c, s.freq - t.freq, false⟩, ⟨-c, s.freq + t.freq, false⟩]
  | false, true => [⟨c, s.freq + t.freq, true⟩, ⟨-c, s.freq - t.freq, true⟩]
  | true, false => [⟨c, s.freq + t.freq, true⟩, ⟨c, s.freq - t.freq, true⟩]

/-- The rational part of `∫₀^π term · sin θ`. -/
def ratMoment (t : TrigTerm) : ℚ :=
  if t.isSin then 0 else t.coeff * ((1 + (-1) ^ t.freq.natAbs) / (1 - (t.freq : ℚ) ^ 2))

/-- The coefficient of `π` in `∫₀^π term · sin θ`. -/
def piMoment (t : TrigTerm) : ℚ :=
  if t.isSin then t.coeff * ((if t.freq = 1 then 1 / 2 else 0) - (if t.freq = -1 then 1 / 2 else 0))
  else 0

end TrigTerm

/-- The sum of a list of terms. -/
noncomputable def trigTermsEval (l : List TrigTerm) (θ : ℝ) : ℝ :=
  (l.map fun t ↦ t.eval θ).sum

/-- The product of two lists of terms. -/
def trigTermsMul (l m : List TrigTerm) : List TrigTerm :=
  l.flatMap fun s ↦ m.flatMap fun t ↦ s.mul t

theorem TrigTerm.eval_mul (s t : TrigTerm) (θ : ℝ) :
    trigTermsEval (s.mul t) θ = s.eval θ * t.eval θ := by
  rcases s with ⟨a, f, bs⟩
  rcases t with ⟨b, g, bt⟩
  have hc1 : Real.cos ((f : ℝ) * θ - g * θ) = Real.cos (f * θ) * Real.cos (g * θ) +
      Real.sin (f * θ) * Real.sin (g * θ) := Real.cos_sub _ _
  have hc2 : Real.cos ((f : ℝ) * θ + g * θ) = Real.cos (f * θ) * Real.cos (g * θ) -
      Real.sin (f * θ) * Real.sin (g * θ) := Real.cos_add _ _
  have hs1 : Real.sin ((f : ℝ) * θ + g * θ) = Real.sin (f * θ) * Real.cos (g * θ) +
      Real.cos (f * θ) * Real.sin (g * θ) := Real.sin_add _ _
  have hs2 : Real.sin ((f : ℝ) * θ - g * θ) = Real.sin (f * θ) * Real.cos (g * θ) -
      Real.cos (f * θ) * Real.sin (g * θ) := Real.sin_sub _ _
  cases bs <;> cases bt <;>
    simp only [TrigTerm.mul, trigTermsEval, TrigTerm.eval, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte, Int.cast_sub, Int.cast_add,
      sub_mul, add_mul] <;> push_cast <;> simp only [hc1, hc2, hs1, hs2] <;> ring

@[simp] theorem trigTermsEval_nil (θ : ℝ) : trigTermsEval [] θ = 0 := rfl

theorem trigTermsEval_cons (t : TrigTerm) (l : List TrigTerm) (θ : ℝ) :
    trigTermsEval (t :: l) θ = t.eval θ + trigTermsEval l θ := by
  simp [trigTermsEval]

theorem trigTermsEval_append (l m : List TrigTerm) (θ : ℝ) :
    trigTermsEval (l ++ m) θ = trigTermsEval l θ + trigTermsEval m θ := by
  simp [trigTermsEval, List.map_append, List.sum_append]

theorem trigTermsEval_flatMap {α : Type*} (l : List α) (F : α → List TrigTerm) (θ : ℝ) :
    trigTermsEval (l.flatMap F) θ = (l.map fun a ↦ trigTermsEval (F a) θ).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, trigTermsEval_append, ih, List.map_cons, List.sum_cons]

/-- The product of lists evaluates to the product of the values. -/
theorem trigTermsEval_trigTermsMul (l m : List TrigTerm) (θ : ℝ) :
    trigTermsEval (trigTermsMul l m) θ = trigTermsEval l θ * trigTermsEval m θ := by
  simp only [trigTermsMul, trigTermsEval_flatMap, TrigTerm.eval_mul]
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, List.sum_cons, ih, trigTermsEval_cons, add_mul]
    congr 1
    rw [trigTermsEval, ← List.sum_map_mul_left]

theorem continuous_trigTermEval (t : TrigTerm) : Continuous t.eval := by
  unfold TrigTerm.eval
  split_ifs <;> fun_prop

theorem continuous_trigTermsEval (l : List TrigTerm) : Continuous (trigTermsEval l) := by
  induction l with
  | nil => exact continuous_const
  | cons t l ih =>
    have : trigTermsEval (t :: l) = fun θ ↦ t.eval θ + trigTermsEval l θ :=
      funext fun θ ↦ trigTermsEval_cons t l θ
    rw [this]
    exact (continuous_trigTermEval t).add ih

/-- `∫₀^π cos (q θ) sin θ dθ = (1 + (-1)^|q|) / (1 - q²)` for every integer `q`. -/
theorem integral_cos_int_mul_mul_sin (q : ℤ) :
    ∫ θ in (0 : ℝ)..π, Real.cos (q * θ) * Real.sin θ =
      (1 + (-1) ^ q.natAbs) / (1 - (q : ℝ) ^ 2) := by
  have hc (θ : ℝ) : Real.cos (q * θ) = Real.cos ((q.natAbs : ℕ) * θ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    rcases abs_choice (q : ℝ) with h | h <;> rw [h]
    rw [neg_mul, Real.cos_neg]
  simp_rw [hc]
  rw [integral_cos_nat_mul_mul_sin_zero_to_pi, Nat.cast_natAbs, Int.cast_abs, sq_abs]

/-- `∫₀^π sin (q θ) sin θ dθ` is `π / 2` at `q = 1`, `-π / 2` at `q = -1` and zero otherwise. -/
theorem integral_sin_int_mul_mul_sin (q : ℤ) :
    ∫ θ in (0 : ℝ)..π, Real.sin (q * θ) * Real.sin θ =
      π * ((if q = 1 then 1 / 2 else 0) - (if q = -1 then 1 / 2 else 0)) := by
  have hprod (θ : ℝ) : Real.sin (q * θ) * Real.sin θ =
      (Real.cos (((q - 1 : ℤ) : ℝ) * θ) - Real.cos (((q + 1 : ℤ) : ℝ) * θ)) / 2 := by
    push_cast
    rw [show ((q : ℝ) - 1) * θ = q * θ - θ by ring, show ((q : ℝ) + 1) * θ = q * θ + θ by ring,
      Real.cos_sub, Real.cos_add]
    ring
  have hcos (p : ℤ) : ∫ θ in (0 : ℝ)..π, Real.cos ((p : ℝ) * θ) =
      if p = 0 then π else 0 := by
    have hc (θ : ℝ) : Real.cos (p * θ) = Real.cos ((p.natAbs : ℕ) * θ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      rcases abs_choice (p : ℝ) with h | h <;> rw [h]
      rw [neg_mul, Real.cos_neg]
    simp_rw [hc]
    rw [integral_cos_nat_mul_zero_to_pi]
    simp [Int.natAbs_eq_zero]
  simp_rw [hprod]
  have i1 : IntervalIntegrable (fun θ : ℝ ↦ Real.cos (((q - 1 : ℤ) : ℝ) * θ))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ : ℝ ↦ Real.cos (((q + 1 : ℤ) : ℝ) * θ))
      MeasureTheory.volume 0 π := (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub i1 i2, hcos, hcos]
  by_cases h1 : q = 1
  · subst h1
    norm_num
    ring
  · by_cases h2 : q = -1
    · subst h2
      norm_num
      ring
    · have e1 : q - 1 ≠ 0 := fun h ↦ h1 (by omega)
      have e2 : q + 1 ≠ 0 := fun h ↦ h2 (by omega)
      simp [e1, e2, h1, h2]

/-- The integral of one term against `sin θ` on `(0, π)`. -/
theorem TrigTerm.integral_eval_mul_sin (t : TrigTerm) :
    ∫ θ in (0 : ℝ)..π, t.eval θ * Real.sin θ = t.ratMoment + π * t.piMoment := by
  rcases t with ⟨c, f, b⟩
  cases b
  · simp only [TrigTerm.eval, TrigTerm.ratMoment, TrigTerm.piMoment, Bool.false_eq_true,
      ↓reduceIte, mul_assoc]
    rw [intervalIntegral.integral_const_mul, integral_cos_int_mul_mul_sin]
    push_cast
    ring
  · simp only [TrigTerm.eval, TrigTerm.ratMoment, TrigTerm.piMoment, ↓reduceIte, mul_assoc]
    rw [intervalIntegral.integral_const_mul, integral_sin_int_mul_mul_sin]
    split_ifs <;> push_cast <;> ring

/-- The integral of a list against `sin θ` on `(0, π)`: the sum of the rational parts plus `π`
times the sum of the `π` parts. -/
theorem integral_trigTermsEval_mul_sin (l : List TrigTerm) :
    ∫ θ in (0 : ℝ)..π, trigTermsEval l θ * Real.sin θ =
      ((l.map TrigTerm.ratMoment).sum : ℚ) + π * ((l.map TrigTerm.piMoment).sum : ℚ) := by
  induction l with
  | nil => simp
  | cons t l ih =>
    have hsplit : (fun θ ↦ trigTermsEval (t :: l) θ * Real.sin θ) =
        fun θ ↦ t.eval θ * Real.sin θ + trigTermsEval l θ * Real.sin θ := by
      funext θ
      rw [trigTermsEval_cons, add_mul]
    have i1 : IntervalIntegrable (fun θ ↦ t.eval θ * Real.sin θ) MeasureTheory.volume 0 π :=
      ((continuous_trigTermEval t).mul continuous_sin).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ ↦ trigTermsEval l θ * Real.sin θ)
        MeasureTheory.volume 0 π :=
      ((continuous_trigTermsEval l).mul continuous_sin).intervalIntegrable _ _
    rw [hsplit, intervalIntegral.integral_add i1 i2, TrigTerm.integral_eval_mul_sin, ih]
    simp only [List.map_cons, List.sum_cons]
    push_cast
    ring

/-- The derivative of a term. -/
def TrigTerm.deriv (t : TrigTerm) : TrigTerm :=
  if t.isSin then ⟨t.coeff * t.freq, t.freq, false⟩ else ⟨-(t.coeff * t.freq), t.freq, true⟩

theorem TrigTerm.hasDerivAt_eval (t : TrigTerm) (θ : ℝ) :
    HasDerivAt t.eval (t.deriv.eval θ) θ := by
  rcases t with ⟨c, f, b⟩
  have hl : HasDerivAt (fun x : ℝ ↦ (f : ℝ) * x) f θ := by
    simpa using (hasDerivAt_id θ).const_mul (f : ℝ)
  cases b
  · have h := (hl.cos).const_mul (c : ℝ)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)
    · simp only [TrigTerm.deriv, TrigTerm.eval, Bool.false_eq_true, ↓reduceIte]
      push_cast
      ring
    · simp [TrigTerm.eval]
  · have h := (hl.sin).const_mul (c : ℝ)
    refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x ↦ ?_)
    · simp only [TrigTerm.deriv, TrigTerm.eval, Bool.false_eq_true, ↓reduceIte]
      push_cast
      ring
    · simp [TrigTerm.eval]

/-- A list of terms has the list of derivatives as its derivative. -/
theorem hasDerivAt_trigTermsEval (l : List TrigTerm) (θ : ℝ) :
    HasDerivAt (trigTermsEval l) (trigTermsEval (l.map TrigTerm.deriv) θ) θ := by
  induction l with
  | nil =>
    change HasDerivAt (fun _ ↦ (0 : ℝ)) 0 θ
    exact hasDerivAt_const θ 0
  | cons t l ih =>
    have hfun : trigTermsEval (t :: l) = fun x ↦ t.eval x + trigTermsEval l x :=
      funext fun x ↦ trigTermsEval_cons t l x
    rw [hfun, List.map_cons, trigTermsEval_cons]
    exact (t.hasDerivAt_eval θ).add ih

/-! ### Fixed-point moments -/

/-- The rational parts of the moments of a list on the grid `2 ^ (-p)`, each rounded down. -/
def trigTermsRatMomentFloor (p : ℕ) (l : List TrigTerm) : ℤ :=
  (l.map fun t ↦ ⌊(2 : ℚ) ^ p * t.ratMoment⌋).sum

/-- The `π` parts of the moments of a list on the grid `2 ^ (-p)`, each rounded down. -/
def trigTermsPiMomentFloor (p : ℕ) (l : List TrigTerm) : ℤ :=
  (l.map fun t ↦ ⌊(2 : ℚ) ^ p * t.piMoment⌋).sum

/-- Rounding each moment down loses less than one grid unit per term. -/
theorem trigTermsRatMomentFloor_mem (p : ℕ) (l : List TrigTerm) :
    (trigTermsRatMomentFloor p l : ℚ) ≤ 2 ^ p * (l.map TrigTerm.ratMoment).sum ∧
      2 ^ p * (l.map TrigTerm.ratMoment).sum ≤ trigTermsRatMomentFloor p l + l.length := by
  induction l with
  | nil => simp [trigTermsRatMomentFloor]
  | cons t l ih =>
    simp only [trigTermsRatMomentFloor, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [Int.cast_add, Nat.cast_succ, mul_add]
    have h1 := Int.floor_le ((2 : ℚ) ^ p * t.ratMoment)
    have h2 := Int.lt_floor_add_one ((2 : ℚ) ^ p * t.ratMoment)
    constructor <;> linarith [ih.1, ih.2]

/-- Rounding each `π` part down loses less than one grid unit per term. -/
theorem trigTermsPiMomentFloor_mem (p : ℕ) (l : List TrigTerm) :
    (trigTermsPiMomentFloor p l : ℚ) ≤ 2 ^ p * (l.map TrigTerm.piMoment).sum ∧
      2 ^ p * (l.map TrigTerm.piMoment).sum ≤ trigTermsPiMomentFloor p l + l.length := by
  induction l with
  | nil => simp [trigTermsPiMomentFloor]
  | cons t l ih =>
    simp only [trigTermsPiMomentFloor, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [Int.cast_add, Nat.cast_succ, mul_add]
    have h1 := Int.floor_le ((2 : ℚ) ^ p * t.piMoment)
    have h2 := Int.lt_floor_add_one ((2 : ℚ) ^ p * t.piMoment)
    constructor <;> linarith [ih.1, ih.2]

end PDE.Analysis
