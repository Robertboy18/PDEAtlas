/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.Variable.Interior

/-!
# Local Hölder bounds for the Schauder bootstrap

C¹ functions are Hölder of every exponent at most one on compact convex
sets. Composition of a Hölder field with a C¹ map preserves its exponent
on a compact field image. These bounds discharge the regularity of the
coefficients and commutator factors in the interior bootstrap.
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal ENNReal

namespace PDE.Elliptic.Regularity.Schauder

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Finite C¹ regularity gives every Hölder exponent through one on a
compact convex set. The Hölder constant is obtained from the derivative
bound and the diameter, not assumed. -/
theorem exists_holderOnWith_of_contDiffOn
    {s : Set E} (hs : IsCompact s) (hc : Convex ℝ s)
    {f : E → F} (hf : ContDiffOn ℝ 1 f s) {γ : ℝ≥0} (hγ : γ ≤ 1) :
    ∃ C : ℝ≥0, HolderOnWith C γ f s := by
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith one_ne_zero hc hs
  let D := (ediam s).toNNReal
  have hD : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D := by
    intro x hx y hy
    rw [show (D : ℝ≥0∞) = ediam s from ENNReal.coe_toNNReal hs.isBounded.ediam_ne_top]
    exact edist_le_ediam_of_mem hx hy
  exact ⟨L * D ^ (1 - γ : ℝ), hL.holderOnWith.of_le hD hγ⟩

omit [NormedSpace ℝ E] in
/-- C¹ composition preserves a Hölder exponent on a compact image. The
outer map needs no global Lipschitz constant. -/
theorem exists_holderOnWith_comp_of_contDiff
    {s : Set E} (hs : IsCompact s) {f : E → F} (hf : ContinuousOn f s)
    {C γ : ℝ≥0} (hh : HolderOnWith C γ f s) {g : F → G}
    (hg : ContDiff ℝ 1 g) :
    ∃ K : ℝ≥0, HolderOnWith K γ (g ∘ f) s := by
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (hs.image_of_continuousOn hf) hg.locallyLipschitz.locallyLipschitzOn
  have h := hL.holderOnWith.comp hh (fun x hx ↦ mem_image_of_mem f hx)
  refine ⟨L * C, ?_⟩
  simpa only [NNReal.coe_one, NNReal.rpow_one, one_mul] using h

end PDE.Elliptic.Regularity.Schauder
