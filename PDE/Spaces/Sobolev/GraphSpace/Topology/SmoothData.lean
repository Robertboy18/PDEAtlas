/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Topology.SupportedBall
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors

/-!
# Smooth compact data in the supported Sobolev iteration class

The smooth Sobolev constructor stores the classical derivatives.
Its base coordinate therefore retains the support of the original function.
Taking a norm budget larger than the norm of this graph places any smooth
compact datum in the complete L² metric class used for transport iteration.
No derivative bounds need to be supplied separately for the initial datum.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set

namespace SobolevSpace.GraphSpace

/-- The base coordinate of the smooth Sobolev graph represents the input
function almost everywhere for the domain measure. -/
theorem wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae
    {n k : ℕ} {Ω : Set (ℝ^n)} {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    (wkpBaseCoordinateCLM
      (mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := Ω) f hf hc) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] f := by
  simpa only [wkpBaseCoordinateCLM_apply, baseIndex_toList, iteratedPartialDeriv] using
    mkWkpSpaceOnOfContDiff_apply_ae (k := k) (p := 2) (Ω := Ω) f hf hc (baseIndex n k)

/-- The smooth Sobolev constructor preserves a measurable support enclosure
and belongs to any ball containing its graph norm. -/
theorem mem_supportedHkBaseBall_of_contDiff
    {n k : ℕ} {Ω K : Set (ℝ^n)} {f : ℝ^n → ℝ} {B : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hK : MeasurableSet K) (hsupport : Function.support f ⊆ K)
    (hbound : ‖mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := Ω) f hf hc‖ ≤ B) :
    wkpBaseCoordinateCLM
      (mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := Ω) f hf hc) ∈
        supportedHkBaseBall n k Ω K B := by
  apply (mem_supportedHkBaseBall_iff hK _).mpr
  refine ⟨⟨_, hbound, rfl⟩, ?_⟩
  filter_upwards [wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae
    (k := k) (Ω := Ω) hf hc] with x hx
  intro hxK
  exact hx.trans (Function.notMem_support.mp fun hxf ↦ hxK (hsupport hxf))

/-- Every smooth compact datum has a positive finite Sobolev norm budget
and a representative in the supported L² iteration class. -/
theorem exists_supportedHkBaseBall_of_contDiff
    {n k : ℕ} {Ω K : Set (ℝ^n)} {f : ℝ^n → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hK : MeasurableSet K) (hsupport : Function.support f ⊆ K) :
    ∃ (B : ℝ) (F : supportedHkBaseBall n k Ω K B), 0 < B ∧
      (F : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f := by
  let U := mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := Ω) f hf hc
  refine ⟨‖U‖ + 1, ⟨wkpBaseCoordinateCLM U, ?_⟩, ?_, ?_⟩
  · exact mem_supportedHkBaseBall_of_contDiff hf hc hK hsupport
      (le_add_of_nonneg_right zero_le_one)
  · exact add_pos_of_nonneg_of_pos (norm_nonneg U) zero_lt_one
  · exact wkpBaseCoordinateCLM_mkWkpSpaceOnOfContDiff_ae hf hc

end SobolevSpace.GraphSpace
