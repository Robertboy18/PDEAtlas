/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# Finite products of functions of temperate growth

Polynomial multipliers of distributions often arrive as finite products. Temperate
growth is preserved by these products, as it is by sums.
-/

@[expose] public section

namespace Function

variable {ι E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedCommRing R] [NormedAlgebra ℝ R]

/-- A finite product of smooth functions of temperate growth has temperate growth. -/
@[fun_prop]
theorem HasTemperateGrowth.prod {f : ι → E → R} {s : Finset ι}
    (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x ↦ ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    obtain ⟨ha, hs⟩ := by simpa using hf
    simpa [has] using! ha.mul (ih hs)

end Function
