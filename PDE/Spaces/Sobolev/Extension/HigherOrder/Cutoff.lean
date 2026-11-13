/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Localization.Cutoff.LpCompatibility
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Bounded cutoff extension at every Sobolev exponent

The weak Leibniz construction already supplies linear cutoff extensions at every order
and exponent. Their base coordinates agree with bounded `Lᵖ` cutoff extension. Completeness
and uniqueness of weak derivatives therefore give a closed graph, proving boundedness
without a Hilbert space restriction.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.Extension.HigherOrder

open MeasureTheory Set GraphSpace TopologicalSpace Filter
open CompactSupportLocalization CompactSupportLocalization.HigherOrderLocalizedCutoff
open scoped Distributions ENNReal Topology

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {S T : Set ℝ^n}

/-- The linear cutoff extension has the same base coordinate as `Lᵖ` cutoff extension. -/
theorem extendByCutoffLinearMap_base (hS : IsOpen S) (hT : IsOpen T) (hST : S ⊆ T)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ S)
    (U : W^{k,p}(S)) :
    wkpBaseCoordinateCLM (extendByCutoffLinearMap hS hT hST ψ hψ U) =
      cutoffExtendLp (T := T) hS.measurableSet ψ (wkpBaseCoordinateCLM U) := by
  apply Lp.ext
  exact (extendByCutoff_base_ae hS hST ψ hψ U).trans
    (cutoffExtendLp_apply_ae hS.measurableSet hT.measurableSet ψ
      (fun _ hx ↦ hψ hx.1) _).symm

/-- Extension by a compactly supported smooth cutoff is bounded on `W^{k,p}`,
including order zero and both endpoint exponents. -/
def cutoffExtensionCLM (hS : IsOpen S) (hT : IsOpen T) (hST : S ⊆ T)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ S) :
    W^{k,p}(S) →L[ℝ] W^{k,p}(T) :=
  ContinuousLinearMap.ofSeqClosedGraph
    (g := extendByCutoffLinearMap hS hT hST ψ hψ) (by
      intro s y x hs hx
      apply wkpBaseCoordinateCLM_injective hT
      have hleft := (wkpBaseCoordinateCLM.continuous.tendsto x).comp hx
      have hright := (((cutoffExtendLp (T := T) hS.measurableSet ψ).comp
        wkpBaseCoordinateCLM).continuous.tendsto y).comp hs
      simp only [Function.comp_def, extendByCutoffLinearMap_base] at hleft
      exact (tendsto_nhds_unique hleft hright).trans
        (extendByCutoffLinearMap_base hS hT hST ψ hψ y).symm)

/-- The bounded cutoff extension agrees with the bounded `Lᵖ` extension on functions. -/
theorem cutoffExtensionCLM_base (hS : IsOpen S) (hT : IsOpen T) (hST : S ⊆ T)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ S)
    (U : W^{k,p}(S)) :
    wkpBaseCoordinateCLM (cutoffExtensionCLM hS hT hST ψ hψ U) =
      cutoffExtendLp (T := T) hS.measurableSet ψ (wkpBaseCoordinateCLM U) :=
  extendByCutoffLinearMap_base hS hT hST ψ hψ U

/-- Relative cutoff extension has the same base coordinate as `Lᵖ` cutoff extension. -/
theorem interCutoffLinearMap_base (hS : IsOpen S) (hT : IsOpen T)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ S)
    (U : W^{k,p}((S ∩ T))) :
    wkpBaseCoordinateCLM (interCutoffLinearMap hS hT ψ hψ U) =
      cutoffExtendLp (T := T) (hS.inter hT).measurableSet ψ
        (wkpBaseCoordinateCLM U) := by
  apply Lp.ext
  exact (interCutoff_base_ae hS hT ψ hψ U).trans
    (cutoffExtendLp_apply_ae (hS.inter hT).measurableSet hT.measurableSet ψ
      (fun _ hx ↦ ⟨hψ hx.1, hx.2⟩) _).symm

/-- A smooth cutoff supported in `S` extends `W^{k,p}(S ∩ T)` boundedly to `W^{k,p}(T)`.
No separation of its support from the boundary of `T` is required. -/
def relativeCutoffCLM (hS : IsOpen S) (hT : IsOpen T)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ S) :
    W^{k,p}((S ∩ T)) →L[ℝ] W^{k,p}(T) :=
  ContinuousLinearMap.ofSeqClosedGraph
    (g := interCutoffLinearMap hS hT ψ hψ) (by
      intro s y x hs hx
      apply wkpBaseCoordinateCLM_injective hT
      have hleft := (wkpBaseCoordinateCLM.continuous.tendsto x).comp hx
      have hright := (((cutoffExtendLp (T := T) (hS.inter hT).measurableSet ψ).comp
        wkpBaseCoordinateCLM).continuous.tendsto y).comp hs
      simp only [Function.comp_def, interCutoffLinearMap_base] at hleft
      exact (tendsto_nhds_unique hleft hright).trans
        (interCutoffLinearMap_base hS hT ψ hψ y).symm)

/-- Relative Sobolev and `Lᵖ` cutoff extensions have the same base coordinate. -/
theorem relativeCutoffCLM_base (hS : IsOpen S) (hT : IsOpen T)
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ S)
    (U : W^{k,p}((S ∩ T))) :
    wkpBaseCoordinateCLM (relativeCutoffCLM hS hT ψ hψ U) =
      cutoffExtendLp (T := T) (hS.inter hT).measurableSet ψ
        (wkpBaseCoordinateCLM U) :=
  interCutoffLinearMap_base hS hT ψ hψ U

end SobolevSpace.Extension.HigherOrder
