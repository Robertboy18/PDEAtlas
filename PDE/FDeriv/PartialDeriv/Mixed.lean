/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv

/-!
# Finite regularity for mixed coordinate derivatives

Two coordinate blocks of lengths `a` and `b` use `a + b` derivatives.
One further coordinate derivative can pass through both blocks when the
original function has one more derivative. The coordinates need not be
distinct, and the target may be any real normed vector space.
-/

@[expose] public section

open PDE (partialDeriv)

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace PDE

/-- Two blocks of coordinate derivatives lower the differentiability order by
the sum of their lengths. -/
theorem contDiff_iterate_partialDeriv_iterate
    (i j : Fin n) (a b m : ℕ) {f : ℝ^n → E}
    (hf : ContDiff ℝ ((m + a + b : ℕ) : WithTop ℕ∞) f) :
    ContDiff ℝ (m : WithTop ℕ∞)
      ((partialDeriv i)^[a] ((partialDeriv j)^[b] f)) :=
  contDiff_iterate_partialDeriv i a m
    (contDiff_iterate_partialDeriv j b (m + a) hf)

/-- A coordinate derivative commutes through two mixed blocks of lengths `a` and `b`
when `f` is `C^(a + b + 1)`. -/
theorem partialDeriv_iterate_partialDeriv_iterate_comm
    (i j : Fin n) (a b : ℕ) (f : ℝ^n → E)
    (hf : ContDiff ℝ ((a + b + 1 : ℕ) : WithTop ℕ∞) f) (k : Fin n) :
    (∂[k] ((partialDeriv i)^[a] ((partialDeriv j)^[b] f))) =
      (partialDeriv i)^[a] ((partialDeriv j)^[b] (∂[k] f)) := by
  have hj : ContDiff ℝ ((a + 1 : ℕ) : WithTop ℕ∞)
      ((partialDeriv j)^[b] f) := by
    apply contDiff_iterate_partialDeriv j b (a + 1)
    simpa only [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hf
  have hlow : ContDiff ℝ ((b + 1 : ℕ) : WithTop ℕ∞) f :=
    hf.of_le (by exact_mod_cast (show b + 1 ≤ a + b + 1 by omega))
  have houter :
      (∂[k] ((partialDeriv i)^[a] ((partialDeriv j)^[b] f))) =
        (partialDeriv i)^[a] (∂[k] ((partialDeriv j)^[b] f)) :=
    partialDeriv_iterate_partialDeriv_comm k i a hj
  have hinner : (∂[k] ((partialDeriv j)^[b] f)) =
      (partialDeriv j)^[b] (∂[k] f) :=
    partialDeriv_iterate_partialDeriv_comm k j b hlow
  rw [houter, hinner]

end PDE
