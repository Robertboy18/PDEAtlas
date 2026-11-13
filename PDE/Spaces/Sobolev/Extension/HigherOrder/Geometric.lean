/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Extension

/-!
# Compatible extension from ordinary Cᵏ graph boundary

The real specialization of Banach-valued geometric extension preserves the scalar
Sobolev graph norm and its derivative coordinates. Its compatible `Lᵖ` action is
bounded for every `1 ≤ p ≤ ∞`, in every dimension and at every finite order.
For positive dimension and order, the local graph condition supplies the finite
atlas used for weighted reflection and a partition of unity. Order zero uses
indicator extension; in dimension zero the domain is empty or full.
-/

@[expose] public section

open scoped Sobolev

namespace SobolevSpace.Extension.HigherOrder

open Set SobolevSpace.GraphSpace
open scoped ENNReal

/-- A bounded open `Cᵏ` domain admits compatible bounded extensions on `W^{k,p}` and
`Lᵖ`, for every finite order and `1 ≤ p ≤ ∞`, including dimension zero.
The hypothesis is a local graph condition on the
boundary; it contains no Sobolev extension or operator bound. -/
theorem exists_extension_with_Lp_base {n k : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary k Ω) :
    ∃ E : W^{k,p}(Ω) →L[ℝ] W^{k,p}((univ : Set (ℝ^n))),
      ∃ E₀ : DerivLp n p Ω →L[ℝ] DerivLp n p univ,
        (∀ U, wkpBaseCoordinateCLM (E U) = E₀ (wkpBaseCoordinateCLM U)) ∧
        (∀ u, restrictDerivLp (subset_univ Ω) (E₀ u) = u) ∧
        (∀ U, restrictCLM hopen.measurableSet (subset_univ Ω) (E U) = U) := by
  let Ωo : TopologicalSpace.Opens ℝ^n := ⟨Ω, hopen⟩
  obtain ⟨E, E₀, hbase, hLp, hrestrict⟩ :=
    VectorValued.GeometricExtension.exists_extension_with_Lp_base
      (k := k) (p := p) (Ω := Ωo) (F := ℝ) hbounded hgraph
  let E' : W^{k,p}(Ω) →L[ℝ] W^{k,p}((univ : Set ℝ^n)) :=
    (VectorValued.scalarEquiv (Ω := ⊤)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (E.comp
        (VectorValued.scalarEquiv (Ω := Ωo)).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨E', E₀, ?_, hLp, ?_⟩
  · intro U
    exact hbase (VectorValued.scalarEquiv.symm U)
  · intro U
    apply Subtype.ext
    apply PiLp.ext
    intro a
    exact congrArg (fun V ↦ V.val a) (hrestrict (VectorValued.scalarEquiv.symm U))

/-- A bounded open Cᵏ domain admits compatible bounded extensions on `Hᵏ` and `L²`.
The local graph condition allows linear coordinates, and includes rigid coordinates. -/
theorem exists_extension_with_L2_base {n k : ℕ} {Ω : Set ℝ^n}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary k Ω) :
    ∃ E : W^{k,2}(Ω) →L[ℝ] W^{k,2}((univ : Set (ℝ^n))),
      ∃ E₀ : DerivLp n 2 Ω →L[ℝ] DerivLp n 2 univ,
        (∀ U, wkpBaseCoordinateCLM (E U) = E₀ (wkpBaseCoordinateCLM U)) ∧
        (∀ u, restrictDerivLp (subset_univ Ω) (E₀ u) = u) ∧
        (∀ U, restrictCLM hopen.measurableSet (subset_univ Ω) (E U) = U) := by
  exact exists_extension_with_Lp_base hopen hbounded hgraph

end SobolevSpace.Extension.HigherOrder
