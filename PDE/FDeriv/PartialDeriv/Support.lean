/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv

/-!
# Support of coordinate derivatives

Coordinate differentiation cannot enlarge topological support. These facts
apply to arbitrary functions: off the support the function is locally zero,
so Mathlib's total derivative is zero there.
-/

@[expose] public noncomputable section

open PDE

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ^n → E}

namespace PDE

/-- The topological support of an ordinary coordinate derivative is
contained in that of the original function. -/
theorem tsupport_partialDeriv_subset (i : Fin n) :
    tsupport (∂[i] f) ⊆ tsupport f :=
  tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i (1 : ℝ))

/-- The coordinate derivative vanishes outside the original topological
support, with no differentiability assumption. -/
theorem partialDeriv_eq_zero_of_notMem_tsupport (i : Fin n) {x : ℝ^n}
    (hx : x ∉ tsupport f) : (∂[i] f) x = 0 := by
  change fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) = 0
  rw [fderiv_of_notMem_tsupport ℝ hx]
  simp

end PDE

/-- Coordinate derivatives preserve compact support for arbitrary maps
into a real normed space. -/
theorem HasCompactSupport.partialDeriv (hf : HasCompactSupport f) (i : Fin n) :
    HasCompactSupport (∂[i] f) :=
  hf.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
