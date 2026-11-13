/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Extension

/-!
# Sobolev extension as a bounded right inverse

The geometric extension is a bounded right inverse of restriction for any real
Banach target, in every dimension and finite derivative order, for `1 ≤ p ≤ ∞`.
Each represented weak derivative agrees almost everywhere with the original on
the domain. This follows from the restriction identity and the physical
description of Sobolev restriction; no choice of basis is needed.
-/

@[expose] public section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.Extension.VectorValued

open SobolevSpace.VectorValued

/-- A bounded open domain with Cᵏ graph boundary admits a bounded Sobolev
extension with values in any real Banach space. The extension is a right inverse
of restriction and preserves every weak derivative on the domain. -/
theorem exists_extension
    {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hbounded : Bornology.IsBounded (Ω : Set ℝ^n))
    (hgraph : Boundary.HasContDiffGraphBoundary k (Ω : Set ℝ^n)) :
    ∃ E : W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F),
      (restrictCLM (show Ω ≤ ⊤ from le_top)).comp E =
        ContinuousLinearMap.id ℝ W^{k,p}(Ω; F) ∧
      ∀ (U : W^{k,p}(Ω; F)) (a : GraphSpace.DerivIndex n k),
        ((E U).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω] U.val a := by
  obtain ⟨E, _, _, _, hE⟩ :=
    GeometricExtension.exists_extension_with_Lp_base (p := p) (F := F) hbounded hgraph
  refine ⟨E, ?_, ?_⟩
  · ext U : 1
    exact hE U
  · intro U a
    have h := restrictCLM_apply_ae (show Ω ≤ ⊤ from le_top) (E U) a
    rw [hE U] at h
    exact h.symm

end SobolevSpace.Extension.VectorValued
