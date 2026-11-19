/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Bounded
public import PDE.Spaces.Sobolev.Extension.HigherOrder.Geometric

/-!
# Bounded extension of bounded Sobolev functions

On a bounded `C^k` graph domain, the geometric extension of a bounded `W^{k,p}`
function is both `W^{k,p}` and essentially bounded on Euclidean space.
The bound is derived for the constructed Sobolev extension itself.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.Extension.HigherOrder

open GraphSpace

/-- The Sobolev extension can be chosen essentially bounded whenever the input
is essentially bounded. No extension hypothesis or dimension-dependent Sobolev
embedding is used. -/
theorem exists_bounded_extension {n k : ℕ} [Fact (0 < n)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n}
    (hk : 0 < k) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary k Ω)
    (U : W^{k,p}(Ω)) {B : ℝ}
    (hB : ∀ᵐ x ∂domainMeasure n Ω, ‖baseRepresentative U x‖ ≤ B) :
    ∃ W : WkpSpaceOn n k p univ,
      restrictCLM hopen.measurableSet (subset_univ Ω) W = U ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume, ‖baseRepresentative W x‖ ≤ C := by
  let Ωo : TopologicalSpace.Opens ℝ^n := ⟨Ω, hopen⟩
  obtain ⟨atlas, hE, hEinv⟩ :=
    hgraph.exists_c1ExtensionAtlas (by exact_mod_cast hk) hopen hbounded
  let : Boundary.C1ExtensionAtlas n (Ωo : Set ℝ^n) := atlas
  let V : WkpSpaceOn n k p univ := VectorValued.scalarEquiv (Ω := ⊤)
    (VectorValued.GeometricExtension.extensionSobolev (Ω := Ωo) (F := ℝ) hk hE hEinv
      ((VectorValued.scalarEquiv (Ω := Ωo)).symm U))
  refine ⟨V, ?_, ?_⟩
  · apply Subtype.ext
    apply PiLp.ext
    intro a
    exact congrArg (fun W ↦ W.val a)
      (VectorValued.GeometricExtension.restrict_extensionSobolev hk hE hEinv
        ((VectorValued.scalarEquiv (Ω := Ωo)).symm U))
  · obtain ⟨C, hC, hb⟩ := VectorValued.GeometricExtension.exists_ae_bound_extensionLp
      (n := n) (Ω := Ωo) (F := ℝ) (p := p) k
      (wkpBaseCoordinateCLM U) hB
    refine ⟨C, hC, ?_⟩
    have hbase := VectorValued.GeometricExtension.extensionSobolev_base hk hE hEinv
      ((VectorValued.scalarEquiv (Ω := Ωo)).symm U)
    change (V.val (baseIndex n k)) = _ at hbase
    change ∀ᵐ x ∂volume, ‖V.val (baseIndex n k) x‖ ≤ C
    rw [hbase]
    simpa only [domainMeasure, Measure.restrict_univ, VectorValued.coordinateCLM_apply,
      VectorValued.scalarEquiv_symm_coordinate, wkpBaseCoordinateCLM_apply] using hb

end SobolevSpace.Extension.HigherOrder
