/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth representatives below an interior half-space level

A function smooth on an open half-space has a globally smooth representative
agreeing locally at every point below a strictly smaller level. A scalar
transition cuts off the function before the original boundary, so no boundary
regularity or extension across that boundary is assumed. The target may be
vector-valued and the differentiability order may be infinite.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- Cutting off before the boundary preserves all germs on a smaller closed half-space. -/
theorem ContDiffOn.exists_contDiff_eventuallyEq_on_halfSpace
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ∞}
    {f : E → F} (ℓ : E →L[ℝ] ℝ) {a b : ℝ}
    (hf : ContDiffOn ℝ k f {x | ℓ x < b}) (hab : a < b) :
    ∃ g : E → F, ContDiff ℝ k g ∧ ∀ x, ℓ x ≤ a → f =ᶠ[𝓝 x] g := by
  obtain ⟨r, har, hrb⟩ := exists_between hab
  obtain ⟨R, hrR, hRb⟩ := exists_between hrb
  let θ (x : E) := Real.smoothTransition ((R - ℓ x) / (R - r))
  have hθ : ContDiff ℝ k θ := Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub ℓ.contDiff).div_const (R - r))
  refine ⟨fun x ↦ θ x • f x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ℓ x < b
    · exact hθ.contDiffAt.smul
        (hf.contDiffAt ((isOpen_lt ℓ.continuous continuous_const).mem_nhds hx))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      have hxR : R < ℓ x := hRb.trans_le (le_of_not_gt hx)
      filter_upwards [(isOpen_lt continuous_const ℓ.continuous).mem_nhds hxR] with y hy
      have hzero : θ y = 0 := Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy.le) (sub_nonneg.mpr hrR.le))
      rw [hzero, zero_smul]
  · intro x hx
    have hxr : ℓ x < r := hx.trans_lt har
    filter_upwards [(isOpen_lt ℓ.continuous continuous_const).mem_nhds hxr] with y hy
    have hone : θ y = 1 := Real.smoothTransition.one_of_one_le
      ((one_le_div (sub_pos.mpr hrR)).mpr (sub_le_sub_left hy.le R))
    rw [hone, one_smul]
