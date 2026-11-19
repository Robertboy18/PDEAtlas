/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Assembly
public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.OrderZero
public import PDE.Spaces.Sobolev.Extension.VectorValued.TrivialDomains
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction

/-!
# Banach-valued Sobolev extension on bounded graph domains

A bounded open domain with `C^k` graph boundary admits a bounded extension
of Banach-valued Sobolev functions of order `k`, for every `1 ≤ p ≤ ∞`.
The geometric hypothesis supplies the atlas; weak chart transport, cutoff
localization, and weighted reflection supply its analytic extension pieces.
One bounded `Lp` companion records the physical base action.

At order zero the isometric indicator extension suffices. In dimension
zero every open domain is empty or full, so no chart is needed. These endpoint
cases use the operators without adding regularity assumptions.
-/

@[expose] public section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.GeometricExtension

open GraphSpace

/-- Geometric extension for every finite order and every Banach target, with a compatible
physical `Lp` right inverse. No extension or chain-rule hypothesis is assumed. -/
theorem exists_extension_with_Lp_base
    {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Opens ℝ^n} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hbounded : Bornology.IsBounded (Ω : Set ℝ^n))
    (hgraph : Boundary.HasContDiffGraphBoundary k (Ω : Set ℝ^n)) :
    ∃ E : W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F),
      ∃ E₀ : Lp F p (domainMeasure n Ω) →L[ℝ] Lp F p (domainMeasure n univ),
        (∀ U, coordinateCLM (baseIndex n k) (E U) =
          E₀ (coordinateCLM (baseIndex n k) U)) ∧
        (∀ u, Lp.restrictionCLMOfLE
          (Measure.restrict_mono (subset_univ (Ω : Set ℝ^n)) le_rfl) (E₀ u) = u) ∧
        (∀ U, VectorValued.restrictCLM (le_top : Ω ≤ ⊤) (E U) = U) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact exists_extension_with_lp_dimension_zero
  · let : Fact (0 < n) := ⟨hn⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨zeroExtendₗᵢ.toContinuousLinearMap, zeroOrderExtensionLp,
        zeroExtendₗᵢ_base_eq_zeroOrderExtensionLp, restrict_zeroOrderExtensionLp,
        restrictCLM_zeroExtendₗᵢ⟩
    · obtain ⟨atlas, hE, hEinv⟩ :=
        hgraph.exists_c1ExtensionAtlas (by exact_mod_cast hk) Ω.isOpen hbounded
      let := atlas
      exact ⟨extensionSobolev hk hE hEinv, extensionLp k,
        extensionSobolev_base hk hE hEinv, restrict_extensionLp k,
        restrict_extensionSobolev hk hE hEinv⟩

end SobolevSpace.VectorValued.GeometricExtension
