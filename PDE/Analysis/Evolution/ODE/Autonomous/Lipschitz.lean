/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Nonautonomous.Lipschitz

/-!
# Globally Lipschitz autonomous equations in Banach spaces

A globally Lipschitz field on a Banach space has an integral curve on the closed
half-line `[0, ∞)` through every initial state: the whole-line solution of the
time-independent equation, restricted to `[0, ∞)`.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- One autonomous solution exists on the whole closed half-line in any complete Banach
space. The derivative at zero is the right derivative in Mathlib's integral-curve predicate. -/
theorem exists_isIntegralCurveOn_Ici_of_lipschitz {F : E → E} {K : NNReal}
    (hF : LipschitzWith K F) (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧ IsIntegralCurveOn u (fun _ ↦ F) (Ici 0) := by
  obtain ⟨u, hu0, hu⟩ := exists_eq_hasDerivAt_of_lipschitz (F := fun _ ↦ F)
    (hF.continuous.comp continuous_snd) (fun _ ↦ hF) 0 x₀
  exact ⟨u, hu0, fun t _ ↦ (hu t).hasDerivWithinAt⟩

end PDE.Analysis.Evolution
