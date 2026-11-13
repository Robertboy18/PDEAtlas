/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2Bounds

/-!
# Weighted coefficient moments and derivative bounds of trigonometric tables

The moment `p.moment a b = ∑ |c_{ijkl}| k ^ a l ^ b` of a table bounds every mixed partial
derivative `∂_β^a ∂_θ^b` of its value: the iterated derivatives of the value are the values of
the iterated derivative tables (`iteratedDeriv_eval_β`, `iteratedDeriv_eval_θ`), whose `ℓ¹`
norm is the moment (`l1Norm_iterate_dβ_dθ`), so
`abs_iteratedDeriv_iteratedDeriv_eval_le_moment` follows from `abs_eval_le_l1Norm`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset

variable {Mβ Mθ : ℕ} {R : Type} [Field R] [Algebra R ℝ]

/-- The coefficient moment `∑ |c_{ijkl}| k ^ a l ^ b`. -/
def moment (p : TrigPoly2 Mβ Mθ R) (a b : ℕ) : ℝ :=
  ∑ i, ∑ j, ∑ k : Fin (Mβ + 1), ∑ l : Fin (Mθ + 1),
    |algebraMap R ℝ (p.coeff i j k l)| * (k : ℝ) ^ a * (l : ℝ) ^ b

theorem moment_nonneg (p : TrigPoly2 Mβ Mθ R) (a b : ℕ) : 0 ≤ p.moment a b :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ by
    positivity

/-- The moment as a sum over natural frequencies. -/
theorem moment_eq_sum_range (p : TrigPoly2 Mβ Mθ R) (a b : ℕ) :
    p.moment a b = ∑ i, ∑ j, ∑ k ∈ range (Mβ + 1), ∑ l ∈ range (Mθ + 1),
      |algebraMap R ℝ (p.coeffN i j k l)| * (k : ℝ) ^ a * (l : ℝ) ^ b := by
  unfold moment
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [← Fin.sum_univ_eq_sum_range (fun k ↦ ∑ l ∈ range (Mθ + 1),
    |algebraMap R ℝ (p.coeffN i j k l)| * (k : ℝ) ^ a * (l : ℝ) ^ b)]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l ↦
    |algebraMap R ℝ (p.coeffN i j k l)| * (k : ℝ) ^ a * (l : ℝ) ^ b)]
  simp

/-- Changing the coefficients by a ring homomorphism compatible with the embeddings into `ℝ`
keeps the moments. -/
theorem moment_map {S : Type} [Field S] [Algebra S ℝ] (f : R →+* S)
    (hf : ∀ c, algebraMap S ℝ (f c) = algebraMap R ℝ c) (p : TrigPoly2 Mβ Mθ R) (a b : ℕ) :
    (p.map f).moment a b = p.moment a b := by
  simp [moment, map, hf]

/-- Iterated derivatives in `β` of the value are values of the iterated derivative table. -/
theorem iteratedDeriv_eval_β (p : TrigPoly2 Mβ Mθ R) (a : ℕ) (θ : ℝ) :
    iteratedDeriv a (fun t ↦ p.eval t θ) = fun β ↦ (dβ^[a] p).eval β θ := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [iteratedDeriv_succ, ih]
    funext β
    rw [(hasDerivAt_eval_β _ β θ).deriv, Function.iterate_succ_apply']

/-- Iterated derivatives in `θ` of the value are values of the iterated derivative table. -/
theorem iteratedDeriv_eval_θ (p : TrigPoly2 Mβ Mθ R) (b : ℕ) (β : ℝ) :
    iteratedDeriv b (fun u ↦ p.eval β u) = fun θ ↦ (dθ^[b] p).eval β θ := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [iteratedDeriv_succ, ih]
    funext θ
    rw [(hasDerivAt_eval_θ _ β θ).deriv, Function.iterate_succ_apply']

/-- The mixed iterated derivative `∂_β^a ∂_θ^b` of the value is the value of
`dβ^[a] (dθ^[b] p)`. -/
theorem iteratedDeriv_iteratedDeriv_eval (p : TrigPoly2 Mβ Mθ R) (a b : ℕ) (β θ : ℝ) :
    iteratedDeriv a (fun t ↦ iteratedDeriv b (fun u ↦ p.eval t u) θ) β =
      (dβ^[a] (dθ^[b] p)).eval β θ := by
  simp only [iteratedDeriv_eval_θ]
  rw [iteratedDeriv_eval_β]

/-- The absolute coefficients of the four blocks at the frequencies `(k, l)`. -/
private def blockAbs (p : TrigPoly2 Mβ Mθ R) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) : ℝ :=
  ∑ i, ∑ j, |algebraMap R ℝ (p.coeff i j k l)|

private theorem sum_four_comm (f : Fin 2 → Fin 2 → Fin (Mβ + 1) → Fin (Mθ + 1) → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
  calc ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ i, ∑ k, ∑ l, ∑ j, f i j k l := by
        refine sum_congr rfl fun i _ ↦ ?_
        rw [sum_comm]
        exact sum_congr rfl fun k _ ↦ sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
        rw [sum_comm]
        exact sum_congr rfl fun k _ ↦ sum_comm

private theorem blockAbs_dβ (q : TrigPoly2 Mβ Mθ R) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) :
    blockAbs q.dβ k l = (k : ℝ) * blockAbs q k l := by
  simp only [blockAbs, dβ, Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, map_mul,
    map_natCast, map_neg, abs_mul, abs_neg, Nat.abs_cast]
  ring

private theorem blockAbs_dθ (q : TrigPoly2 Mβ Mθ R) (k : Fin (Mβ + 1)) (l : Fin (Mθ + 1)) :
    blockAbs q.dθ k l = (l : ℝ) * blockAbs q k l := by
  simp only [blockAbs, dθ, Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, map_mul,
    map_natCast, map_neg, abs_mul, abs_neg, Nat.abs_cast]
  ring

private theorem blockAbs_iterate (p : TrigPoly2 Mβ Mθ R) (a b : ℕ) (k : Fin (Mβ + 1))
    (l : Fin (Mθ + 1)) :
    blockAbs (dβ^[a] (dθ^[b] p)) k l = (k : ℝ) ^ a * (l : ℝ) ^ b * blockAbs p k l := by
  induction a with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
    induction b with
    | zero => simp
    | succ b ih => rw [Function.iterate_succ_apply', blockAbs_dθ, ih, pow_succ]; ring
  | succ a ih => rw [Function.iterate_succ_apply', blockAbs_dβ, ih, pow_succ]; ring

/-- The `ℓ¹` norm of the mixed iterated derivative table is the moment. -/
theorem l1Norm_iterate_dβ_dθ (p : TrigPoly2 Mβ Mθ R) (a b : ℕ) :
    (dβ^[a] (dθ^[b] p)).l1Norm = p.moment a b := by
  unfold l1Norm moment
  rw [sum_four_comm, sum_four_comm]
  refine sum_congr rfl fun k _ ↦ sum_congr rfl fun l _ ↦ ?_
  have h := blockAbs_iterate p a b k l
  simp only [blockAbs] at h
  rw [h, mul_comm, sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_mul]
  exact sum_congr rfl fun j _ ↦ by ring

/-- The moment `∑ |c| k ^ a l ^ b` bounds the mixed partial derivative `∂_β^a ∂_θ^b` of the
value everywhere. -/
theorem abs_iteratedDeriv_iteratedDeriv_eval_le_moment (p : TrigPoly2 Mβ Mθ R) (a b : ℕ)
    (β θ : ℝ) :
    |iteratedDeriv a (fun t ↦ iteratedDeriv b (fun u ↦ p.eval t u) θ) β| ≤ p.moment a b := by
  rw [iteratedDeriv_iteratedDeriv_eval, ← l1Norm_iterate_dβ_dθ]
  exact abs_eval_le_l1Norm _ β θ

end PDE.Analysis.TrigPoly2
