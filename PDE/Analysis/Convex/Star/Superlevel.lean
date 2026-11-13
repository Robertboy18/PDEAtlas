/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LevelSets.Filled

/-!
# Star-convexity of filled superlevel sets

Radial nonincrease outside a nonempty star-convex inner set makes every filled
superlevel set star-convex. This geometric implication uses no differential equation.
-/

@[expose] public section

open Set PDE.Analysis

/-- Dilation comparison makes filled superlevel sets star-convex. -/
theorem StarConvex.filledSuperlevel
    {E : Type*} [AddCommGroup E] [Module ℝ E] {K W : Set E} {u : E → ℝ} {c : ℝ}
    (hK : StarConvex ℝ 0 K) (hW : StarConvex ℝ 0 W) (hKne : K.Nonempty)
    (hcompare : ∀ {a : ℝ}, 1 < a → ∀ {x : E}, x ∉ K → a • x ∈ W → u (a • x) ≤ u x) :
    StarConvex ℝ 0 (filledSuperlevel K W u c) := by
  rw [starConvex_zero_iff]
  intro x hx t ht0 ht1
  rcases hx with hxK | ⟨hx, hcx⟩
  · exact Or.inl (hK.smul_mem hxK ht0 ht1)
  · by_cases htxK : t • x ∈ K
    · exact Or.inl htxK
    · have htpos : 0 < t := by
        by_contra h
        have ht : t = 0 := le_antisymm (le_of_not_gt h) ht0
        obtain ⟨z, hz⟩ := hKne
        apply htxK
        simpa [ht] using hK.smul_mem hz (t := (0 : ℝ)) le_rfl zero_le_one
      refine Or.inr ⟨⟨hW.smul_mem hx.1 ht0 ht1, htxK⟩, ?_⟩
      rcases ht1.eq_or_lt with ht | ht
      · simpa only [ht, one_smul] using hcx
      · have hinv : 1 < t⁻¹ := (one_lt_inv₀ htpos).mpr ht
        have hle := hcompare hinv htxK
          (show t⁻¹ • (t • x) ∈ W by simpa only [inv_smul_smul₀ htpos.ne'] using hx.1)
        exact hcx.trans_le (by simpa only [inv_smul_smul₀ htpos.ne'] using hle)
