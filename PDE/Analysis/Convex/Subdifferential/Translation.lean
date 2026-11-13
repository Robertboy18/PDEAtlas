/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Subdifferential.Basic

/-!
# Finite constant shifts of extended energies

Adding a finite real constant preserves every supporting vector. The
cancellation holds for signed extended energies, including infinite
competitors.
-/

@[expose] public section

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A finite real energy shift leaves the Hilbert subdifferential unchanged. -/
theorem subdifferential_add_const (I : H → EReal) (c : ℝ) (u : H) :
    subdifferential (fun x ↦ I x + (c : EReal)) u = subdifferential I u := by
  ext v
  change (∀ w, (I u + (c : EReal)) + (inner ℝ v (w - u) : EReal) ≤ I w + (c : EReal)) ↔
    ∀ w, I u + (inner ℝ v (w - u) : EReal) ≤ I w
  apply forall_congr' fun w ↦ ?_
  rw [add_right_comm]
  exact (EReal.addLECancellable_coe c).add_le_add_iff_right

end PDE.Analysis.Convex
