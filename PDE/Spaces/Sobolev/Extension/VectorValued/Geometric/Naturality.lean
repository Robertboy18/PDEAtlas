/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Restriction.LinearMap
public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Assembly
public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.OrderZero
public import PDE.Spaces.Sobolev.Extension.VectorValued.HalfSpace.Naturality

/-!
# Codomain naturality of geometric Sobolev extension

The atlas, reflection coefficients and scalar cutoffs are independent of the
Banach codomain. Each physical operation therefore commutes with a continuous
linear map of values. The assembled `Lp` identity gives the Sobolev identity by
injectivity of the base coordinate, without another weak derivative argument.

The positive-order identities use the same fixed atlas and chart regularity as
the extension. Order zero is covered separately by the
indicator extension, in every dimension and without boundary hypotheses.
All identities include both exponent endpoints.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev Distributions

namespace SobolevSpace.VectorValued

variable {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace GeometricExtension

open GraphSpace

private theorem restriction_compLpL {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} (h : μ ≤ ν) (L : F →L[ℝ] G) (u : Lp F p ν) :
    Lp.restrictionCLMOfLE h (L.compLpL p ν u) =
      L.compLpL p μ (Lp.restrictionCLMOfLE h u) :=
  (congrArg (fun T ↦ T u) (L.compLpL_restrictionCLMOfLE (p := p) h)).symm

section OrderZero

variable {n : ℕ} {Ω : Opens ℝ^n}

/-- Indicator extension is natural under continuous linear maps, including in dimension zero. -/
theorem zeroOrderExtensionLp_compLpL (L : F →L[ℝ] G)
    (u : Lp F p (domainMeasure n Ω)) :
    zeroOrderExtensionLp (L.compLpL p (domainMeasure n Ω) u) =
      L.compLpL p (domainMeasure n univ) (zeroOrderExtensionLp u) := by
  apply Lp.ext
  have hu := (ae_restrict_iff' Ω.isOpen.measurableSet).mp (L.coeFn_compLpL u)
  have hu' := ae_mono (Measure.restrict_le_self (μ := volume) (s := (univ : Set ℝ^n))) hu
  filter_upwards [zeroOrderExtensionLp_apply_ae (L.compLpL p (domainMeasure n Ω) u),
    L.coeFn_compLpL (zeroOrderExtensionLp u), zeroOrderExtensionLp_apply_ae u, hu']
    with x hw hL hv hx
  rw [hw, hL, hv]
  by_cases hxΩ : x ∈ Ω
  · simp only [indicator_of_mem hxΩ, hx hxΩ]
  · simp only [indicator_of_notMem hxΩ, map_zero]

variable [CompleteSpace F] [CompleteSpace G]

/-- The order-zero Sobolev isometry commutes with codomain transport. -/
theorem zeroExtendₗᵢ_mapCLM (L : F →L[ℝ] G) (U : W^{0,p}(Ω; F)) :
    zeroExtendₗᵢ (mapCLM L U) = mapCLM L (zeroExtendₗᵢ U) := by
  apply baseCoordinateCLM_injective
  rw [zeroExtendₗᵢ_base_eq_zeroOrderExtensionLp]
  change zeroOrderExtensionLp (L.compLpL p (domainMeasure n Ω) (U.val (baseIndex n 0))) =
    L.compLpL p (domainMeasure n univ) (coordinateCLM (baseIndex n 0) (zeroExtendₗᵢ U))
  rw [zeroExtendₗᵢ_base_eq_zeroOrderExtensionLp, zeroOrderExtensionLp_compLpL]
  rfl

end OrderZero

variable [CompleteSpace F] [CompleteSpace G]
  {n k : ℕ} {Ω V : Opens ℝ^n}

/-- Relative scalar multiplication is natural even across the change of domain. -/
theorem interMultiplierLp_compLpL
    (ψ : 𝓓((⊤ : Opens ℝ^n), ℝ)) (hψ : tsupport ψ.toFun ⊆ V)
    (L : F →L[ℝ] G) (u : Lp F p (domainMeasure n (V ⊓ Ω))) :
    interMultiplierLp ψ hψ (L.compLpL p (domainMeasure n (V ⊓ Ω)) u) =
      L.compLpL p (domainMeasure n Ω) (interMultiplierLp ψ hψ u) := by
  apply Lp.ext
  filter_upwards [interMultiplierLp_apply_ae ψ hψ
      (L.compLpL p (domainMeasure n (V ⊓ Ω)) u) (L.coeFn_compLpL u),
    L.coeFn_compLpL (interMultiplierLp ψ hψ u),
    interMultiplierLp_apply_ae ψ hψ u Filter.EventuallyEq.rfl] with x hw hL hv
  rw [hw, hL, hv, map_smul]

variable [Fact (0 < n)] [hΩ : Boundary.C1ExtensionAtlas n (Ω : Set ℝ^n)]

/-- Flattening a patch commutes with a continuous linear map of values. -/
theorem flattenLp_compLpL (i : Fin hΩ.N) (L : F →L[ℝ] G)
    (u : Lp F p (domainMeasure n Ω)) :
    flattenLp i (L.compLpL p (domainMeasure n Ω) u) =
      L.compLpL p (domainMeasure n ℝ^n₊) (flattenLp i u) := by
  simp only [flattenLp, ContinuousLinearMap.comp_apply, restriction_compLpL,
    SobolevSpace.WeakChangeOfVariables.boundedPullbackCLM_compLpL,
    interMultiplierLp_compLpL]
  rfl

/-- Returning a flattened patch is natural under codomain transport. -/
theorem localizeLp_compLpL (i : Fin hΩ.N) (L : F →L[ℝ] G)
    (u : Lp F p (domainMeasure n univ)) :
    localizeLp i (L.compLpL p (domainMeasure n univ) u) =
      L.compLpL p (domainMeasure n univ) (localizeLp i u) := by
  simp only [localizeLp, ContinuousLinearMap.comp_apply, restriction_compLpL,
    SobolevSpace.WeakChangeOfVariables.boundedPullbackCLM_compLpL]
  exact interMultiplierLp_compLpL (Ω := ⊤)
    (V := ⟨(hΩ.chart i).source, (hΩ.chart i).open_source⟩)
    (hΩ.boundaryCutoff i) (hΩ.boundaryCutoff_support i) L _

/-- A reflected boundary piece commutes with every continuous linear codomain map. -/
theorem boundaryExtensionLp_compLpL (k : ℕ) (i : Fin hΩ.N) (L : F →L[ℝ] G)
    (u : Lp F p (domainMeasure n Ω)) :
    boundaryExtensionLp k i (L.compLpL p (domainMeasure n Ω) u) =
      L.compLpL p (domainMeasure n univ) (boundaryExtensionLp k i u) := by
  simp only [boundaryExtensionLp, ContinuousLinearMap.comp_apply, flattenLp_compLpL,
    HigherOrderReflection.weightedExtendLp_compLpL, localizeLp_compLpL]

/-- The finite-atlas physical extension is natural in its Banach codomain. -/
theorem extensionLp_compLpL (k : ℕ) (L : F →L[ℝ] G)
    (u : Lp F p (domainMeasure n Ω)) :
    extensionLp k (L.compLpL p (domainMeasure n Ω) u) =
      L.compLpL p (domainMeasure n univ) (extensionLp k u) := by
  simp only [extensionLp, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    restriction_compLpL, interMultiplierLp_compLpL, boundaryExtensionLp_compLpL,
    map_add, map_sum]
  rfl

/-- Bundled naturality of the physical extension for the same atlas and reflection order. -/
theorem compLpL_comp_extensionLp (k : ℕ) (L : F →L[ℝ] G) :
    (L.compLpL p (domainMeasure n univ)).comp (extensionLp (Ω := Ω) k) =
      (extensionLp k).comp (L.compLpL p (domainMeasure n Ω)) := by
  ext1 u
  exact (extensionLp_compLpL k L u).symm

/-- Geometric extension commutes with codomain maps on the entire Sobolev graph. -/
theorem extensionSobolev_mapCLM (hk : 0 < k)
    (hE : ∀ i, ContDiff ℝ k (hΩ.chart i))
    (hEinv : ∀ i, ContDiff ℝ k (hΩ.chart i).symm)
    (L : F →L[ℝ] G) (U : W^{k,p}(Ω; F)) :
    extensionSobolev hk hE hEinv (mapCLM L U) =
      mapCLM L (extensionSobolev hk hE hEinv U) := by
  apply baseCoordinateCLM_injective
  rw [extensionSobolev_base]
  change extensionLp k (L.compLpL p (domainMeasure n Ω) (U.val (baseIndex n k))) =
    L.compLpL p (domainMeasure n univ)
      (coordinateCLM (baseIndex n k) (extensionSobolev hk hE hEinv U))
  rw [extensionSobolev_base, extensionLp_compLpL]
  rfl

/-- Bundled naturality of the positive-order geometric extension. -/
theorem mapCLM_comp_extensionSobolev (hk : 0 < k)
    (hE : ∀ i, ContDiff ℝ k (hΩ.chart i))
    (hEinv : ∀ i, ContDiff ℝ k (hΩ.chart i).symm) (L : F →L[ℝ] G) :
    (mapCLM L).comp (extensionSobolev (p := p) hk hE hEinv) =
      (extensionSobolev hk hE hEinv).comp (mapCLM L) := by
  ext1 U
  exact (extensionSobolev_mapCLM hk hE hEinv L U).symm

end GeometricExtension
end SobolevSpace.VectorValued
