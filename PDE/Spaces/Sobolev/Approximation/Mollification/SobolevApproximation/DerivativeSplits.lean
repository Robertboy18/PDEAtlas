/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.DerivativeSplits
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# The principal Leibniz split

The iterated Leibniz formula contains one term where every derivative falls on the second
factor. These lemmas identify that term as the head of `derivativeSplits` and characterize the
remaining terms.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

namespace Approximation

variable {n : ℕ}

/-- The list of Leibniz derivative splits is nonempty. -/
theorem derivativeSplits_ne_nil (α : List (Fin n)) : derivativeSplits (n := n) α ≠ [] := by
  induction α with
  | nil => simp [derivativeSplits]
  | cons i rest ih =>
      -- Assigning the leading index to the second component gives a split.
      simp [derivativeSplits, ih]

/-- The first Leibniz split assigns every derivative to the second factor. -/
theorem derivativeSplits_head? (α : List (Fin n)) :
    (derivativeSplits (n := n) α).head? = some ([], α) := by
  induction α with
  | nil => simp [derivativeSplits]
  | cons i rest ih =>
      -- The first branch preserves the distinguished split `([], rest)`.
      cases h : derivativeSplits (n := n) rest with
      | nil =>
          cases (derivativeSplits_ne_nil (n := n) rest) h
      | cons p ps =>
          have hp : p = ([], rest) := by
            have : (some p) = some ([], rest) := by simpa [h] using ih
            exact Option.some.inj this
          subst hp
          simp [derivativeSplits, h]

/-- The principal split is the unique split with no derivative on the first factor. -/
theorem derivativeSplits_filter_first_nil (α : List (Fin n)) :
    (derivativeSplits (n := n) α).filter (fun q ↦ decide (q.1 = [])) = [([], α)] := by
  classical
  induction α with
  | nil =>
      simp [derivativeSplits]
  | cons i rest ih =>
      -- An empty first component forces every index into the second component.
      have h2 :
          List.filter
              (fun p : List (Fin n) × List (Fin n) ↦ decide (i :: p.1 = []))
              (derivativeSplits (n := n) rest) =
            [] := by
        -- The branch that prepends `i` to the first component never contributes.
        induction (derivativeSplits (n := n) rest) with
        | nil => simp
        | cons p ps ih' =>
            have hp : decide (i :: p.1 = []) = false := by simp
            simp
      -- The first branch is governed by the induction hypothesis; the second contributes nothing.
      have hcomp1 :
          ((fun q : List (Fin n) × List (Fin n) ↦ decide (q.1 = [])) ∘ fun p ↦ (p.1, i :: p.2)) =
            (fun p : List (Fin n) × List (Fin n) ↦ decide (p.1 = [])) := by
        rfl
      have hcomp2 :
          ((fun q : List (Fin n) × List (Fin n) ↦ decide (q.1 = [])) ∘ fun p ↦ (i :: p.1, p.2)) =
            (fun p : List (Fin n) × List (Fin n) ↦ decide (i :: p.1 = [])) := by
        rfl
      simp [derivativeSplits, List.filter_append, List.filter_map, hcomp1, hcomp2, ih]

/-- Every split after the head differentiates the first factor at least once. -/
theorem derivativeSplits_tail_first_ne_nil (α : List (Fin n)) :
    ∀ q ∈ (derivativeSplits (n := n) α).tail, q.1 ≠ [] := by
  classical
  -- Removing the distinguished head leaves no split with empty first component.
  have hhead : ([], α) ∈ (derivativeSplits (n := n) α).head? := by
    simp [derivativeSplits_head? (n := n) α]
  have hcons : ([], α) :: (derivativeSplits (n := n) α).tail = derivativeSplits (n := n) α :=
    List.cons_head?_tail hhead
  have hfilter :
      ((derivativeSplits (n := n) α).tail.filter (fun q ↦ decide (q.1 = []))) = [] := by
    have h := congrArg (fun l ↦ l.filter (fun q ↦ decide (q.1 = []))) hcons
    have h' :
        ([], α) :: ((derivativeSplits (n := n) α).tail.filter (fun q ↦ decide (q.1 = []))) = [([],
          α)] := by
      -- The head `([], α)` is the unique split selected by the predicate.
      simpa [List.filter_cons, derivativeSplits_filter_first_nil (n := n) α] using h
    exact (List.cons.inj h').2
  intro q hq hq0
  have : q ∈ (derivativeSplits (n := n) α).tail.filter (fun q ↦ decide (q.1 = [])) := by
    exact List.mem_filter.2 ⟨hq, by simp [hq0]⟩
  simp [hfilter] at this

end Approximation

end SobolevSpace
