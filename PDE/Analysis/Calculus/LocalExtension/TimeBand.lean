/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.HalfSpace
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth representatives on an interior time band

A function smooth where a continuous linear coordinate lies in an open interval
has a globally smooth representative agreeing locally throughout every smaller
closed interval. No regularity at either endpoint of the open interval is needed.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- Temporal cutoffs preserve the germs on a closed band inside an open band. -/
theorem ContDiffOn.exists_contDiff_eventuallyEq_on_band
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ∞}
    {f : E → F} (ℓ : E →L[ℝ] ℝ) {s₀ s τ T : ℝ}
    (hf : ContDiffOn ℝ k f {x | s₀ < ℓ x ∧ ℓ x < T})
    (hs : s₀ < s) (hτ : τ < T) :
    ∃ g : E → F, ContDiff ℝ k g ∧ ∀ x, ℓ x ∈ Icc s τ → f =ᶠ[𝓝 x] g := by
  obtain ⟨l, hsl, hls⟩ := exists_between hs
  obtain ⟨r, hlr, hrs⟩ := exists_between hls
  let θ (x : E) := Real.smoothTransition ((ℓ x - l) / (r - l))
  have hθ : ContDiff ℝ k θ := Real.smoothTransition.contDiff.comp
    ((ℓ.contDiff.sub contDiff_const).div_const (r - l))
  have hcut : ContDiffOn ℝ k (fun x ↦ θ x • f x) {x | ℓ x < T} := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    by_cases hlow : s₀ < ℓ x
    · exact hθ.contDiffAt.smul (hf.contDiffAt
        (((isOpen_lt continuous_const ℓ.continuous).inter
          (isOpen_lt ℓ.continuous continuous_const)).mem_nhds ⟨hlow, hx⟩))
    · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      have hxl : ℓ x < l := (le_of_not_gt hlow).trans_lt hsl
      filter_upwards [(isOpen_lt ℓ.continuous continuous_const).mem_nhds hxl] with y hy
      have hzero : θ y = 0 := Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy.le) (sub_nonneg.mpr hlr.le))
      rw [hzero, zero_smul]
  obtain ⟨g, hg, heq⟩ := hcut.exists_contDiff_eventuallyEq_on_halfSpace ℓ hτ
  refine ⟨g, hg, ?_⟩
  intro x hx
  refine Filter.EventuallyEq.trans ?_ (heq x hx.2)
  have hrx : r < ℓ x := hrs.trans_le hx.1
  filter_upwards [(isOpen_lt continuous_const ℓ.continuous).mem_nhds hrx] with y hy
  have hone : θ y = 1 := Real.smoothTransition.one_of_one_le
    ((one_le_div (sub_pos.mpr hlr)).mpr (sub_le_sub_right hy.le l))
  rw [hone, one_smul]
