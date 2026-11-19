/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Reflection

/-!
# Translation of a weak time derivative

Translating a path and its distributional velocity translates the domain of
the weak derivative. Two time reflections give the change of variables, so
this statement applies without selecting a continuous representative.
-/

@[expose] public section

namespace PDE.Analysis.Evolution

open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Translation preserves a local weak derivative on the translated open domain. -/
theorem HasWeakTimeDerivativeOn.comp_const_add {U : Set ℝ} (hU : IsOpen U)
    {u g : ℝ → H} (h : HasWeakTimeDerivativeOn U u g) (s : ℝ) :
    HasWeakTimeDerivativeOn ((fun t ↦ s + t) ⁻¹' U)
      (fun t ↦ u (s + t)) (fun t ↦ g (s + t)) := by
  have hshift := (h.reflect hU (s / 2)).reflect
    (hU.preimage (contDiff_reflectTime (s / 2)).continuous) 0
  have htime (t : ℝ) : reflectTime (s / 2) (reflectTime 0 t) = s + t := by
    simp [reflectTime, ← mul_div_assoc]
  simpa only [Function.comp_def, preimage_preimage, htime, neg_neg] using hshift

end PDE.Analysis.Evolution
