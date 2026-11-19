/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.FDeriv.PartialDeriv

/-!
# Composition of coordinate derivative blocks

Mixed derivatives in two coordinates combine by adding their multiplicities.
Only the blocks that commute need differentiability: an outer block can be
applied to the resulting equality without further regularity.
-/

@[expose] public section

open PDE (partialDeriv)

namespace PDE

/-- Two mixed coordinate blocks combine by adding their respective orders.
Regularity through order `b + c + d` suffices because the outer block of length
`a` is applied only after the inner blocks have been identified. -/
theorem iterate_partialDeriv_mixed_compose
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ^n → E} (i j : Fin n) (a b c d : ℕ)
    (hf : ContDiff ℝ (b + c + d) f) :
    (partialDeriv i)^[a] ((partialDeriv j)^[b]
        ((partialDeriv i)^[c] ((partialDeriv j)^[d] f))) =
      (partialDeriv i)^[a + c] ((partialDeriv j)^[b + d] f) := by
  rw [iterate_partialDeriv_comm j i b c
    (contDiff_iterate_partialDeriv j d (b + c) hf)]
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply]

end PDE
