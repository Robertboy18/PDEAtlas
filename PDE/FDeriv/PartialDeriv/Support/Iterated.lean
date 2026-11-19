/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv

/-!
# Support of iterated coordinate derivatives

Iterated coordinate differentiation does not enlarge topological support, so it preserves
compact support. The argument uses
Mathlib's support theorem for Fréchet derivatives and works for every real normed codomain,
without a smoothness assumption.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open Function

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- A finite word of coordinate derivatives vanishes outside the original support. -/
theorem tsupport_iteratedPartialDeriv_subset (α : List (Fin n)) (f : ℝ^n → F) :
    tsupport (iteratedPartialDeriv α f) ⊆ tsupport f := by
  induction α with
  | nil => exact Set.Subset.rfl
  | cons i α ih =>
    exact (tsupport_fderiv_apply_subset ℝ
      (f := iteratedPartialDeriv α f) (EuclideanSpace.single i 1)).trans ih

end PDE

/-- Compact support is preserved by every finite word of coordinate derivatives. -/
theorem HasCompactSupport.iteratedPartialDeriv {f : ℝ^n → F}
    (hf : HasCompactSupport f) (α : List (Fin n)) :
    HasCompactSupport (iteratedPartialDeriv α f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (PDE.tsupport_iteratedPartialDeriv_subset α f)
