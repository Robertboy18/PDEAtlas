/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Symbolic.Calculus.MixedDerivatives
public import CAS.Expr.PolynomialSyntax
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Mixed derivatives of an expression composed with functions

The variables of an expression `expr : Expr (Fin m)` may stand for functions
`f j : ℝ^n → ℝ` rather than for coordinates. `jetDiff expr` is the chain-rule expression in
`m + m` variables: the first block holds the values `f j y` and the second their
derivatives, and `partialDeriv_eval_comp` proves that it computes `∂[i] (expr ∘ f)`.
Iterating `jetDiff` along a word of coordinate directions gives `mixedJetExpr`, whose
variables are indexed by `jetSlot` and filled by `jetValues` with actual mixed derivatives
of the inputs.

## Main results

* `iteratedPartialDeriv_eval_jetValues`: for inputs of class `C^k`, `k` the length of the
  word, and `ValidJetAlong expr f word`, the mixed derivative of `y ↦ expr.eval (f · y)`
  is `mixedJetExpr` evaluated on the jet table.
* `IsPolynomial.validJetAlong`: polynomial expressions satisfy the validity hypothesis for
  every input, so only the regularity of the inputs remains to be proved.

The inputs need not be given by expressions. An input may be an integral whose
derivatives have separately proved enclosures.
-/

@[expose] public section

namespace CAS.Verified.Expr

open PDE

/-- Chain-rule expression in a block of values followed by a block of derivatives. -/
def jetDiff {m : ℕ} (expr : Expr (Fin m)) : Expr (Fin (m + m)) :=
  simplify (addList ((List.finRange m).map fun j ↦
    .mul ((expr.diff j).mapVars fun k ↦ .var (k.castAdd m)) (.var (Fin.natAdd m j))))

/-- Chain-rule compilation preserves polynomial syntax in the enlarged variable set. -/
theorem IsPolynomial.jetDiff {m : ℕ} {expr : Expr (Fin m)} (h : expr.IsPolynomial) :
    expr.jetDiff.IsPolynomial := by
  apply IsPolynomial.simplify
  apply isPolynomial_addList
  intro term he
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
  exact ⟨(h.diff j).mapVars _ (fun _ ↦ trivial), trivial⟩

/-- Evaluating the chain-rule expression contracts the symbolic gradient with a tangent. -/
theorem eval_jetDiff {m : ℕ} (expr : Expr (Fin m)) (v d : Fin m → ℝ) :
    expr.jetDiff.eval (Fin.append v d) =
      ∑ j : Fin m, (expr.diff j).eval v * d j := by
  simp only [jetDiff, eval_simplify, eval_addList, List.map_map,
    ← Fin.sum_univ_def, Function.comp_apply, eval, eval_mapVars, Fin.append_left,
    Fin.append_right]

/-- Chain-rule soundness for an expression evaluated on an actual Euclidean field. -/
theorem partialDeriv_eval_comp {n m : ℕ} (expr : Expr (Fin m))
    (f : ℝ^n → ℝ^m) (i : Fin n) (x : ℝ^n)
    (hf : DifferentiableAt ℝ f x) (hvalid : expr.ValidAt (f x)) :
    (∂[i] (fun y ↦ expr.eval (f y))) x =
      expr.jetDiff.eval (Fin.append (f x)
        (fun j ↦ (∂[i] (fun y ↦ f y j)) x)) := by
  rw [eval_jetDiff]
  have hcomp := fderiv_comp x (expr.hasFDerivAt_eval (f x) hvalid).differentiableAt hf
  have happ := congrArg
    (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i (1 : ℝ))) hcomp
  change (∂[i] (fun y ↦ expr.eval (f y))) x =
    (fderiv ℝ (fun z : ℝ^m ↦ expr.eval z) (f x))
      ((fderiv ℝ f x) (EuclideanSpace.single i (1 : ℝ))) at happ
  rw [fderiv_apply_eq_sum_partialDeriv_mul] at happ
  apply happ.trans
  apply Finset.sum_congr rfl
  intro j _
  rw [expr.partialDeriv_eval_eq (f x) j hvalid]
  congr 1
  exact partialDeriv_apply i j hf

/-- Number of value and derivative slots after a specified number of chain rules. -/
def jetDimension (m : ℕ) (k : ℕ) : ℕ :=
  Nat.rec m (fun _ slots ↦ slots + slots) k

/-- Repeated chain-rule expression, iterating `jetDiff` `k` times. The derivative
directions enter only through the jet values. -/
def mixedJetExpr {m : ℕ} (expr : Expr (Fin m)) (k : ℕ) :
    Expr (Fin (jetDimension m k)) :=
  Nat.rec (motive := fun j ↦ Expr (Fin (jetDimension m j)))
    expr (fun _ value ↦ value.jetDiff) k

/-- Every iterated chain-rule expression for polynomial syntax is polynomial. -/
theorem IsPolynomial.mixedJetExpr {m : ℕ} {expr : Expr (Fin m)} (h : expr.IsPolynomial)
    (k : ℕ) : (expr.mixedJetExpr k).IsPolynomial := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.jetDiff

/-- Original input index and outermost-first derivative word represented by a jet slot. -/
def jetSlot {n : ℕ} (m : ℕ) (word : List (Fin n)) :
    Fin (jetDimension m word.length) → Fin m × List (Fin n) :=
  List.rec (motive := fun rest ↦
      Fin (jetDimension m rest.length) → Fin m × List (Fin n))
    (fun j ↦ (j, [])) (fun i _ slots ↦ Fin.append slots
      (fun j ↦ let slot := slots j; (slot.1, i :: slot.2))) word

/-- Adding a physical derivative keeps the old slots and appends their derivatives. -/
theorem jetSlot_cons {n m : ℕ} (i : Fin n) (rest : List (Fin n)) :
    jetSlot m (i :: rest) = Fin.append (jetSlot m rest)
      (fun j ↦ let slot := jetSlot m rest j; (slot.1, i :: slot.2)) := rfl

/-- A slot differentiates its original input at most as often as the length of the word. -/
theorem jetSlot_length_le {n m : ℕ} (word : List (Fin n))
    (j : Fin (jetDimension m word.length)) :
    (jetSlot m word j).2.length ≤ word.length := by
  induction word with
  | nil => exact Nat.zero_le _
  | cons i rest ih =>
      refine Fin.addCases (m := jetDimension m rest.length) (n := jetDimension m rest.length)
        (fun k ↦ ?_) (fun k ↦ ?_) j
      · simpa only [jetSlot_cons, Fin.append_left, List.length_cons] using
          (ih k).trans (Nat.le_succ _)
      · simpa only [jetSlot_cons, Fin.append_right, List.length_cons] using
          Nat.succ_le_succ (ih k)

/-- The jet table at `x`: each slot holds the mixed derivative of its input function
named by `jetSlot`. -/
noncomputable def jetValues {n m : ℕ} (f : Fin m → ℝ^n → ℝ)
    (word : List (Fin n)) (x : ℝ^n) : ℝ^(jetDimension m word.length) :=
  WithLp.toLp 2 fun j ↦ iteratedPartialDeriv (jetSlot m word j).2
    (f (jetSlot m word j).1) x

/-- Finite regularity of the source inputs controls every slot of a jet table. -/
theorem contDiff_jetValues {n m k : ℕ} (f : Fin m → ℝ^n → ℝ)
    (word : List (Fin n)) (hf : ∀ j, ContDiff ℝ (k + word.length : ℕ) (f j)) :
    ContDiff ℝ k (jetValues f word) := by
  apply (contDiff_piLp 2).2
  intro j
  have hlen := jetSlot_length_le word j
  exact (contDiff_iteratedPartialDeriv_of_le (hf (jetSlot m word j).1)
    (jetSlot m word j).2 (by omega)).of_le (by
      exact_mod_cast (show k ≤ k + word.length - (jetSlot m word j).2.length by omega))

/-- Validity of every intermediate chain-rule expression at every jet table along the word.
This is the hypothesis of repeated differentiation; polynomial expressions satisfy it by
`IsPolynomial.validJetAlong`. -/
def ValidJetAlong {n m : ℕ} (expr : Expr (Fin m)) (f : Fin m → ℝ^n → ℝ)
    (word : List (Fin n)) : Prop :=
  List.rec True (fun _ rest valid ↦ valid ∧
    ∀ x, (mixedJetExpr expr rest.length).ValidAt (jetValues f rest x)) word

/-- Polynomial expressions are valid along every jet table, independently of its values. -/
theorem IsPolynomial.validJetAlong {n m : ℕ} {expr : Expr (Fin m)}
    (h : expr.IsPolynomial) (f : Fin m → ℝ^n → ℝ) (word : List (Fin n)) :
    expr.ValidJetAlong f word := by
  induction word with
  | nil => trivial
  | cons i rest ih => exact ⟨ih, fun x ↦ (h.mixedJetExpr rest.length).validAt _⟩

/-- Repeated symbolic chain rules compute the actual mixed derivative from source jets. -/
theorem iteratedPartialDeriv_eval_jetValues {n m : ℕ} (expr : Expr (Fin m))
    (f : Fin m → ℝ^n → ℝ) (word : List (Fin n))
    (hf : ∀ j, ContDiff ℝ word.length (f j)) (hvalid : ValidJetAlong expr f word)
    (x : ℝ^n) :
    iteratedPartialDeriv word (fun y ↦ expr.eval (fun j ↦ f j y)) x =
      (mixedJetExpr expr word.length).eval (jetValues f word x) := by
  induction word generalizing x with
  | nil => rfl
  | cons i rest ih =>
      have heq : (fun y ↦ iteratedPartialDeriv rest
          (fun z ↦ expr.eval (fun j ↦ f j z)) y) =
          fun y ↦ (mixedJetExpr expr rest.length).eval (jetValues f rest y) := by
        funext y
        exact ih (fun j ↦ (hf j).of_le (by simp)) hvalid.1 y
      change partialDeriv i _ x = _
      rw [heq, partialDeriv_eval_comp _ _ i x
        ((contDiff_jetValues f rest (k := 1) (by
          intro j
          simpa [Nat.add_comm] using hf j)).differentiable (by norm_num) x) (hvalid.2 x)]
      congr 1
      funext j
      refine Fin.addCases (m := jetDimension m rest.length) (n := jetDimension m rest.length)
        (fun k ↦ ?_) (fun k ↦ ?_) j
      · simp only [jetValues, jetSlot_cons, Fin.append_left]
      · simp only [jetValues, jetSlot_cons, Fin.append_right, iteratedPartialDeriv]

attribute [inherit_doc jetDiff]
  jetDiff.eq_1

attribute [inherit_doc jetDimension]
  jetDimension.eq_1

attribute [inherit_doc mixedJetExpr]
  mixedJetExpr.eq_1

attribute [inherit_doc jetSlot]
  jetSlot.eq_1

attribute [inherit_doc jetValues]
  jetValues.eq_1

attribute [inherit_doc ValidJetAlong]
  ValidJetAlong.eq_1

end CAS.Verified.Expr
