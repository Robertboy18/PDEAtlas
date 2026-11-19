/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generation.Resolvent
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Positivity.Finset

/-!
# Hilbert space range conditions for contraction generators

Dissipativity gives the contraction resolvent estimate by Cauchy–Schwarz. Once
the positive shifts are onto, orthogonal separation also gives density of the
operator domain. Both conclusions are stated for Mathlib's `LinearPMap`.
-/

@[expose] public section

namespace PDE.Analysis.Evolution

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {A : E →ₗ.[ℝ] E}

/-- Dissipativity and surjectivity of every positive shift give the resolvent bound. -/
theorem hasContractionResolvent_of_inner_nonpos
    (hinner : ∀ x : A.domain, ⟪A x, (x : E)⟫_ℝ ≤ 0)
    (hrange : ∀ lambda : ℝ, 0 < lambda →
      Function.Surjective (lambda • A.domain.subtype - A.toFun)) :
    HasContractionResolvent A where
  surjective := hrange
  bound lambda hlambda x := by
    have hi := hinner x
    have hb := real_inner_le_norm (lambda • (x : E) - A x) (x : E)
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hb
    by_cases hx : ‖(x : E)‖ = 0
    · rw [hx]
      positivity
    · have hxpos : 0 < ‖(x : E)‖ := (norm_nonneg _).lt_of_ne' hx
      have hcancel : lambda * ‖(x : E)‖ ≤ ‖lambda • (x : E) - A x‖ := by nlinarith
      rw [← div_eq_inv_mul, le_div_iff₀ hlambda]
      simpa only [mul_comm] using hcancel

/-- A dissipative operator with an onto positive shift has dense domain. -/
theorem HasContractionResolvent.dense_domain_of_inner_nonpos [CompleteSpace E]
    (hA : HasContractionResolvent A)
    (hinner : ∀ x : A.domain, ⟪A x, (x : E)⟫_ℝ ≤ 0) :
    Dense (A.domain : Set E) := by
  have horth : A.domainᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    change f = 0
    obtain ⟨x, hx⟩ := hA.surjective 1 zero_lt_one f
    change (1 : ℝ) • (x : E) - A x = f at hx
    rw [one_smul] at hx
    have hz := hf (x : E) x.property
    rw [← hx, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm] at hz
    have hnorm : ‖(x : E)‖ = 0 := by nlinarith [hinner x, sq_nonneg ‖(x : E)‖]
    have hxzero : x = 0 := Subtype.val_injective (norm_eq_zero.mp hnorm)
    simpa [hxzero] using hx.symm
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]

end PDE.Analysis.Evolution
