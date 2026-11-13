/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Tactic.ToDual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset

/-!
# Derivative-word splittings

The combinatorial operation underlying iterated Leibniz rules. A derivative
word is split by assigning each occurrence, in order, to
one of two factors. Repeated coordinates remain repeated, so multiplicities
are represented by repeated list entries rather than separate coefficients.
-/

@[expose] public section

namespace SobolevSpace

variable {n : ℕ}

/-- All ordered assignments of a derivative word to two factors. -/
def derivativeSplits : List (Fin n) → List (List (Fin n) × List (Fin n))
  | [] => [([], [])]
  | i :: rest =>
      (derivativeSplits rest).map (fun q ↦ (q.1, i :: q.2)) ++
        (derivativeSplits rest).map (fun q ↦ (i :: q.1, q.2))

/-- Splitting a derivative word neither creates nor deletes derivatives. -/
theorem derivativeSplits_length {α : List (Fin n)}
    {q : List (Fin n) × List (Fin n)} (hq : q ∈ derivativeSplits α) :
    q.1.length + q.2.length = α.length := by
  induction α generalizing q with
  | nil =>
      simp [derivativeSplits] at hq
      subst q
      simp
  | cons i rest ih =>
      simp only [derivativeSplits, List.mem_append, List.mem_map] at hq
      rcases hq with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
      · have := ih hr
        simp only [List.length_cons]
        omega
      · have := ih hr
        simp only [List.length_cons]
        omega

/-- Splitting a word of length `m` into two factors has `2 ^ m` ordered assignments. -/
theorem length_derivativeSplits (α : List (Fin n)) :
    (derivativeSplits α).length = 2 ^ α.length := by
  induction α with
  | nil => simp [derivativeSplits]
  | cons i α ih =>
    simp only [derivativeSplits, List.length_append, List.length_map, ih, List.length_cons,
      pow_succ]
    omega

end SobolevSpace
