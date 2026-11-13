/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.BoundaryPiece

/-!
# Finite assembly of Banach-valued geometric extension

The interior term and the returned boundary pieces use the partition of unity
of the scalar atlas. Each boundary piece contributes exactly one
partition factor. Their sum therefore recovers the physical `Lp` function.
Compatibility with the base coordinate gives recovery of the whole Sobolev graph.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.GeometricExtension

open GraphSpace

variable {n k : ℕ} [Fact (0 < n)] {Ω : Opens ℝ^n}
  [hΩ : Boundary.C1ExtensionAtlas n (Ω : Set ℝ^n)]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The interior cutoff and finite reflected boundary sum, on physical `Lp` classes. -/
def extensionLp (k : ℕ) :
    Lp F p (domainMeasure n Ω) →L[ℝ] Lp F p (domainMeasure n univ) :=
  (interMultiplierLp (Ω := ⊤) (V := Ω) hΩ.interiorCutoff
    hΩ.interiorCutoff_support).comp
      (Lp.restrictionCLMOfLE (Measure.restrict_mono
        (show ((Ω ⊓ ⊤ : Opens ℝ^n) : Set ℝ^n) ⊆ Ω from inf_le_left) le_rfl)) +
    ∑ i : Fin hΩ.N, boundaryExtensionLp k i

/-- Bounded geometric extension on the Banach-valued Sobolev graph. -/
def extensionSobolev (hk : 0 < k)
    (hE : ∀ i, ContDiff ℝ k (hΩ.chart i))
    (hEinv : ∀ i, ContDiff ℝ k (hΩ.chart i).symm) :
    W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F) :=
  (interMultiplier (Ω := ⊤) (V := Ω) hΩ.interiorCutoff
    hΩ.interiorCutoff_support).comp (VectorValued.restrictCLM (inf_le_left : Ω ⊓ ⊤ ≤ Ω)) +
    ∑ i : Fin hΩ.N, boundaryExtensionSobolev hk hE hEinv i

/-- The assembled Sobolev operator has the same physical base action as its `Lp` companion. -/
theorem extensionSobolev_base (hk : 0 < k)
    (hE : ∀ i, ContDiff ℝ k (hΩ.chart i))
    (hEinv : ∀ i, ContDiff ℝ k (hΩ.chart i).symm) (U : W^{k,p}(Ω; F)) :
    coordinateCLM (baseIndex n k) (extensionSobolev hk hE hEinv U) =
      extensionLp k (coordinateCLM (baseIndex n k) U) := by
  simp only [extensionSobolev, extensionLp, add_apply, sum_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sum, interMultiplier_base_eq,
    boundaryExtensionSobolev_base]
  rfl

/-- The finite partition reconstructs the original physical function on the domain. -/
theorem extensionLp_apply_ae (k : ℕ) (u : Lp F p (domainMeasure n Ω)) :
    (extensionLp k u : ℝ^n → F) =ᵐ[domainMeasure n Ω] u := by
  let r := Lp.restrictionCLMOfLE (Measure.restrict_mono
    (show ((Ω ⊓ ⊤ : Opens ℝ^n) : Set ℝ^n) ⊆ Ω from inf_le_left) le_rfl) u
  let I := interMultiplierLp (Ω := ⊤) (V := Ω) hΩ.interiorCutoff
    hΩ.interiorCutoff_support r
  let B := fun i : Fin hΩ.N ↦ boundaryExtensionLp k i u
  have hI : (I : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      fun x ↦ hΩ.interiorCutoff x • u x :=
    ae_mono (Measure.restrict_mono (subset_univ (Ω : Set ℝ^n)) le_rfl)
      (interMultiplierLp_apply_ae hΩ.interiorCutoff hΩ.interiorCutoff_support r
        (Lp.restrictionCLMOfLE_apply_ae _ u))
  have hB := ae_all_iff.mpr (fun i : Fin hΩ.N ↦ boundaryExtensionLp_apply_ae k i u)
  have hsum := ae_mono
    (Measure.restrict_mono (subset_univ (Ω : Set ℝ^n)) le_rfl)
    (Lp.coeFn_finsetSum (Finset.univ : Finset (Fin hΩ.N)) B)
  have hadd := ae_mono
    (Measure.restrict_mono (subset_univ (Ω : Set ℝ^n)) le_rfl)
    (Lp.coeFn_add I (∑ i, B i))
  filter_upwards [hI, hB, hsum, hadd, ae_restrict_mem Ω.isOpen.measurableSet]
    with x hxI hxB hxsum hxadd hxΩ
  simp only [extensionLp, add_apply, sum_apply, ContinuousLinearMap.comp_apply]
  change (I + ∑ i, B i : Lp F p (domainMeasure n univ)) x = u x
  rw [hxadd, Pi.add_apply, hxI, hxsum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ ↦ hxB i), ← Finset.sum_smul, ← add_smul]
  change (hΩ.interiorCutoff.toFun x + ∑ i, (hΩ.boundaryCutoff i).toFun x) • u x = u x
  rw [hΩ.cutoff_sum_eq_one x hxΩ, one_smul]

/-- The physical extension is a right inverse of restriction. -/
theorem restrict_extensionLp (k : ℕ) (u : Lp F p (domainMeasure n Ω)) :
    Lp.restrictionCLMOfLE
      (Measure.restrict_mono (subset_univ (Ω : Set ℝ^n)) le_rfl)
      (extensionLp k u) = u :=
  Lp.ext ((Lp.restrictionCLMOfLE_apply_ae _ _).trans (extensionLp_apply_ae k u))

/-- Restriction recovers the entire Sobolev graph, not just a chosen representative. -/
theorem restrict_extensionSobolev (hk : 0 < k)
    (hE : ∀ i, ContDiff ℝ k (hΩ.chart i))
    (hEinv : ∀ i, ContDiff ℝ k (hΩ.chart i).symm) (U : W^{k,p}(Ω; F)) :
    VectorValued.restrictCLM (le_top : Ω ≤ ⊤) (extensionSobolev hk hE hEinv U) = U := by
  apply baseCoordinateCLM_injective
  change Lp.restrictionCLMOfLE _ (coordinateCLM (baseIndex n k)
    (extensionSobolev hk hE hEinv U)) = coordinateCLM (baseIndex n k) U
  rw [extensionSobolev_base, restrict_extensionLp]

end SobolevSpace.VectorValued.GeometricExtension
