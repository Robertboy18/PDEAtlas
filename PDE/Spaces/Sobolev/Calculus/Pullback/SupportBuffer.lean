/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Support buffers for localized Sobolev pullbacks

A compact target patch pulls back to a compact subset of a chart source.
Sobolev localization needs a smooth cutoff around this set together with an
open source buffer whose closure remains controlled by a larger compact
target patch.

The construction uses two nested smooth cutoffs: the inner cutoff is one near
the original pullback patch, while the outer cutoff creates the open buffer
and the larger compact target patch.
-/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SobolevSpace.WeakChangeOfVariables

open Set

variable {n : ℕ}

/-- Construct a compact target patch, an open source buffer, and a smooth
cutoff equal to one near the pullback of the original compact patch. -/
theorem exists_pullback_support_buffer
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hEsymm : Continuous (fun y ↦ E.symm y))
    {K₀ : Set (ℝ^n)} (hK₀ : IsCompact K₀) (hK₀Target : K₀ ⊆ E.target) :
    ∃ (target source : Set (ℝ^n))
        (cutoff : 𝓓((⊤ : Opens (ℝ^n)), ℝ)),
      IsCompact target ∧
      target ⊆ E.target ∧
      IsOpen source ∧
      source ⊆ compactPullbackSource (n := n) E target ∧
      source ⊆ E.source ∧
      tsupport cutoff.toFun ⊆ source ∧
      (∀ x ∈ compactPullbackSource (n := n) E K₀,
        cutoff.toFun x = 1) ∧
      ∀ x ∈ compactPullbackSource (n := n) E K₀,
        cutoff.toFun =ᶠ[nhds x] 1 := by
  classical
  let L₀ := compactPullbackSource (n := n) E K₀
  have hL₀ : IsCompact L₀ :=
    isCompact_compactPullbackSource (n := n) hEsymm hK₀
  have hL₀Source : L₀ ⊆ E.source := by
    rintro x ⟨y, hy, rfl⟩
    exact E.map_target (hK₀Target hy)
  obtain ⟨ψ, hψSource, hψOne, hψNhds, _hψRange⟩ :=
    TestFunction.exists_eq_one_on_compact
      E.open_source hL₀ hL₀Source
  let Kψ := tsupport ψ.toFun
  have hKψ : IsCompact Kψ := by
    simpa [Kψ] using ψ.hasCompactSupport.isCompact
  have hKψSource : Kψ ⊆ E.source := by
    simpa [Kψ] using hψSource
  obtain ⟨χ, hχSource, hχOne, _hχNhds, _hχRange⟩ :=
    TestFunction.exists_eq_one_on_compact
      E.open_source hKψ hKψSource
  let K : Set (ℝ^n) := E '' tsupport χ.toFun
  let V : Set (ℝ^n) := {x | χ.toFun x ≠ 0}
  have hKCompact : IsCompact K := by
    exact χ.hasCompactSupport.image_of_continuousOn
      (E.continuousOn.mono hχSource)
  have hKTarget : K ⊆ E.target := by
    rintro y ⟨x, hx, rfl⟩
    exact E.map_source (hχSource hx)
  have hVOpen : IsOpen V :=
    isOpen_ne_fun χ.continuous continuous_const
  have hVSource : V ⊆ E.source := by
    intro x hx
    exact hχSource (subset_tsupport χ.toFun hx)
  have hVPullback : V ⊆ compactPullbackSource (n := n) E K := by
    intro x hx
    have hxSupport : x ∈ tsupport χ.toFun :=
      subset_tsupport χ.toFun hx
    have hxSource : x ∈ E.source := hχSource hxSupport
    refine ⟨E x, ?_, E.left_inv hxSource⟩
    exact ⟨x, hxSupport, rfl⟩
  have hψV : tsupport ψ.toFun ⊆ V := by
    intro x hx
    have hχ := hχOne x (by simpa [Kψ] using hx)
    change χ.toFun x ≠ 0
    rw [hχ]
    norm_num
  exact ⟨K, V, ψ, hKCompact, hKTarget, hVOpen, hVPullback,
    hVSource, hψV, by simpa [L₀] using hψOne,
    by simpa [L₀] using hψNhds⟩

end SobolevSpace.WeakChangeOfVariables
