/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Finite solution families for bounded autonomous fields

A global velocity bound lets the Picard–Lindelöf state ball grow with the prescribed
time interval. Mathlib then constructs one jointly continuous family for all initial
states in a prescribed ball. No compactness of state balls or global Lipschitz
constant is needed.
-/

@[expose] public section

open Metric Set

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A bounded autonomous field Lipschitz on bounded balls admits a jointly continuous
solution family on any finite symmetric interval and any bounded initial ball. -/
theorem exists_continuousOn_solution_family_of_bounded {F : E → E} {M : NNReal}
    (hbound : ∀ x, ‖F x‖ ≤ M)
    (hF : ∀ R : ℝ, 0 < R → ∃ K : NNReal, LipschitzOnWith K F (closedBall 0 R))
    (R T : NNReal) :
    ∃ α : E × ℝ → E,
      (∀ x ∈ closedBall 0 R, α (x, 0) = x ∧
        ∀ t ∈ Icc (-(T : ℝ)) T,
          HasDerivWithinAt (fun s ↦ α (x, s)) (F (α (x, t))) (Icc (-(T : ℝ)) T) t) ∧
      ContinuousOn α (closedBall 0 R ×ˢ Icc (-(T : ℝ)) T) := by
  let A : NNReal := R + M * T + 1
  obtain ⟨K, hK⟩ := hF A (by dsimp [A]; positivity)
  have hpic : IsPicardLindelof (fun _ ↦ F)
      (⟨0, neg_nonpos.mpr T.coe_nonneg, T.coe_nonneg⟩ : Icc (-(T : ℝ)) T)
      (0 : E) A R M K :=
    IsPicardLindelof.of_time_independent (fun x _ ↦ hbound x) hK (by
      simp only [sub_zero, zero_sub, neg_neg, max_self]
      dsimp [A]
      linarith)
  exact hpic.exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn

end PDE.Analysis.Evolution
