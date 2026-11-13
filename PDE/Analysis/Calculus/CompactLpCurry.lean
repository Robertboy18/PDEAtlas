/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactCurry
public import PDE.Analysis.MeasureTheory.Lp.ContinuousExtension
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuity and differentiation of compactly supported families in Lᵖ

A jointly continuous family with common compact spatial support is continuous in Lᵖ.
The parameter may range over any topological space, and only the support needs finite
measure. Joint continuity of a family and its parameter derivative also gives differentiability in
the supremum norm on a compact spatial set. The bounded zero-extension map then gives
differentiability in Lᵖ. A common compact support ensures that the zero-extended functions
are the original functions, rather than spatial truncations of them.

The Lᵖ classes and the proposed derivative operator are identified by almost-everywhere
representatives. These hypotheses specify values of classes; they do not assume
differentiability of the Lᵖ-valued family.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped BoundedContinuousFunction ENNReal

namespace MeasureTheory

/-- A jointly continuous family with common compact spatial support is continuous
in Lᵖ. Only that compact set needs finite measure, and the parameter space can be
an arbitrary topological space, such as a closed time interval. -/
theorem continuous_Lp_of_common_compact_support
    {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure Y}
    (K : Compacts Y) [SecondCountableTopologyEither K E]
    [IsFiniteMeasure (μ.restrict (K : Set Y))]
    {f : X → Y → E} (hf : Continuous f.uncurry)
    (hsupp : ∀ t x, x ∉ K → f t x = 0) {v : X → Lp E p μ}
    (hv : ∀ t, (v t : Y → E) =ᵐ[μ] f t) : Continuous v := by
  let c (t : X) : C(K, E) := ⟨fun x ↦ f t x,
    hf.comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hc : Continuous c := ContinuousMap.continuous_of_continuous_uncurry c
    (hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  let B := ContinuousMap.isometryEquivBoundedOfCompact K E
  let T : (BoundedContinuousFunction K E) →L[ℝ] Lp E p μ :=
    BoundedContinuousFunction.subtypeToLp K.isCompact.isClosed.measurableSet
  have he (t : X) : T (B (c t)) = v t := by
    apply Lp.ext
    filter_upwards [BoundedContinuousFunction.coeFn_subtypeToLp
      (p := p) (μ := μ)
      K.isCompact.isClosed.measurableSet (B (c t)), hv t] with x hx hy
    rw [hy, hx]
    by_cases hm : x ∈ K
    · exact Subtype.coe_injective.extend_apply _ _ (⟨x, hm⟩ : K)
    · rw [Function.extend_apply' _ _ x (by
        rintro ⟨y, rfl⟩
        exact hm y.property), hsupp t x hm]
  have hcont := T.continuous.comp (B.continuous.comp hc)
  simpa only [Function.comp_def, he] using hcont

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ : Measure F}

/-- A jointly continuous family with a jointly continuous parameter derivative and a
common compact spatial support differentiates in Lᵖ. The spatial measure need only be
finite on that compact set. The derivative is identified by its actual representatives. -/
theorem hasFDerivAt_Lp_of_common_compact_support
    (K : Compacts F)
    [IsFiniteMeasure (μ.restrict (K : Set F))]
    (f : E → F → G) (D : E → F → E →L[ℝ] G)
    (hf : Continuous f.uncurry) (hD : Continuous D.uncurry)
    (hderiv : ∀ x y, HasFDerivAt (fun z ↦ f z y) (D x y) x)
    (hfK : ∀ x y, y ∉ K → f x y = 0)
    (u : E → Lp G p μ) (du : E → E →L[ℝ] Lp G p μ)
    (hu : ∀ x, (u x : F → G) =ᵐ[μ] f x)
    (hdu : ∀ x h, (du x h : F → G) =ᵐ[μ] fun y ↦ D x y h)
    (x : E) : HasFDerivAt u (du x) x := by
  let T : (K →ᵇ G) →L[ℝ] Lp G p μ :=
    BoundedContinuousFunction.subtypeToLp K.isCompact.isClosed.measurableSet
  have hT (v : K →ᵇ G) :
      (T v : F → G) =ᵐ[μ] Function.extend Subtype.val v (fun _ : F ↦ (0 : G)) :=
    BoundedContinuousFunction.coeFn_subtypeToLp K.isCompact.isClosed.measurableSet v
  have hu_eq :
      (fun z ↦ T (BoundedContinuousFunction.compactCurry K f hf z)) = u := by
    funext z
    apply Lp.ext
    filter_upwards [hT (BoundedContinuousFunction.compactCurry K f hf z), hu z] with
      y hyT hyu
    rw [hyT, hyu]
    by_cases hy : y ∈ K
    · exact Subtype.coe_injective.extend_apply _ _ (⟨y, hy⟩ : K)
    · rw [Function.extend_apply' _ _ y (by
        rintro ⟨v, rfl⟩
        exact hy v.property), hfK z y hy]
  have hdu_eq :
      T.comp (BoundedContinuousFunction.compactCurryFDeriv K D hD x) = du x := by
    apply ContinuousLinearMap.ext
    intro h
    apply Lp.ext
    filter_upwards [hT (BoundedContinuousFunction.compactCurryFDeriv K D hD x h),
      hdu x h] with y hyT hydu
    rw [ContinuousLinearMap.comp_apply, hyT, hydu]
    by_cases hy : y ∈ K
    · exact Subtype.coe_injective.extend_apply _ _ (⟨y, hy⟩ : K)
    · have hzero : (fun z ↦ f z y) = fun _ : E ↦ (0 : G) :=
        funext fun z ↦ hfK z y hy
      have hd := hderiv x y
      rw [hzero] at hd
      have hDy : D x y = 0 := hd.unique (hasFDerivAt_const (0 : G) x)
      rw [Function.extend_apply' _ _ y (by
        rintro ⟨v, rfl⟩
        exact hy v.property), hDy, zero_apply]
  have h := T.hasFDerivAt.comp x
    (BoundedContinuousFunction.hasFDerivAt_compactCurry K f D hf hD hderiv x)
  change HasFDerivAt
    (fun z ↦ T (BoundedContinuousFunction.compactCurry K f hf z))
    (T.comp (BoundedContinuousFunction.compactCurryFDeriv K D hD x)) x at h
  rwa [hu_eq, hdu_eq] at h

end MeasureTheory
