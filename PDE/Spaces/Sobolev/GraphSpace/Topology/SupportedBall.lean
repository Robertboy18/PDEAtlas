/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
public import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness
import PDE.Analysis.WeakCompactness
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# A complete L² metric class with a uniform Sobolev bound

A uniformly bounded family of Sobolev graphs whose base coordinates converge
in L² has a limiting Sobolev graph with the same norm bound. Weak
compactness constructs the derivative coordinates; the limit graph is not
assumed. Consequently a bounded Sobolev class with a fixed support enclosure
is closed, hence complete, for the weaker L² metric.

Support here means almost-everywhere vanishing outside the enclosure. With `n = 1`,
`k = 2` and the whole line, the class is a complete metric space for contraction
arguments in one-dimensional transport problems.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- Strong convergence of bounded Sobolev base coordinates constructs the
weak derivatives of the limit and preserves the full graph norm bound. -/
theorem exists_hk_of_tendsto_base
    {n k : ℕ} {Ω : Set (ℝ^n)} {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → W^{k,2}(Ω)) (f : DerivLp n 2 Ω) {B : ℝ}
    (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ wkpBaseCoordinateCLM (u i)) l (𝓝 f)) :
    ∃ v : W^{k,2}(Ω), ‖v‖ ≤ B ∧ wkpBaseCoordinateCLM v = f := by
  have hbounded : Bornology.IsBounded (range u) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨B, by rintro _ ⟨i, rfl⟩; exact hbound i⟩
  obtain ⟨w, U, hU, hweak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter l u hbounded
  refine ⟨(toWeakSpace ℝ (W^{k,2}(Ω))).symm w, ?_, ?_⟩
  · exact WeakCompactness.norm_le_of_tendsto_of_norm_le hweak
      (.of_forall hbound)
  · have hmap := (WeakSpace.map
        (wkpBaseCoordinateCLM : W^{k,2}(Ω) →L[ℝ] DerivLp n 2 Ω)).continuous.tendsto w
        |>.comp hweak
    have hlimit := (toWeakSpaceCLM ℝ (DerivLp n 2 Ω)).continuous.continuousAt.tendsto.comp
      (hbase.mono_left hU)
    exact congrArg (toWeakSpace ℝ (DerivLp n 2 Ω)).symm
      (tendsto_nhds_unique hmap hlimit)

/-- L² base coordinates admitting a Sobolev graph of norm at most `B`. The
metric is inherited from L², not from the stronger Sobolev norm. -/
def hkBaseBall (n k : ℕ) (Ω : Set (ℝ^n)) (B : ℝ) : Set (DerivLp n 2 Ω) :=
  {f | ∃ u : W^{k,2}(Ω), ‖u‖ ≤ B ∧ wkpBaseCoordinateCLM u = f}

/-- A bounded Sobolev class is closed in the weaker L² topology. -/
theorem isClosed_hkBaseBall (n k : ℕ) (Ω : Set (ℝ^n)) (B : ℝ) :
    IsClosed (hkBaseBall n k Ω B) := by
  apply IsSeqClosed.isClosed
  intro f v hf hv
  choose u hnorm hbase using hf
  apply exists_hk_of_tendsto_base (l := atTop) u v hnorm
  simpa only [hbase] using hv

/-- The Sobolev-bounded L² class with zero restriction outside a fixed spatial
enclosure. The restriction is a continuous linear map on L² classes. -/
def supportedHkBaseBall (n k : ℕ) (Ω K : Set (ℝ^n)) (B : ℝ) :
    Set (DerivLp n 2 Ω) :=
  hkBaseBall n k Ω B ∩
    {f | LpToLpRestrictCLM (ℝ^n) ℝ ℝ (domainMeasure n Ω) 2 Kᶜ f = 0}

/-- The fixed-support Sobolev ball is closed in L², since the exterior
restriction is continuous and the Sobolev norm bound survives an L² limit. -/
theorem isClosed_supportedHkBaseBall (n k : ℕ) (Ω K : Set (ℝ^n)) (B : ℝ) :
    IsClosed (supportedHkBaseBall n k Ω K B) :=
  (isClosed_hkBaseBall n k Ω B).inter
    (isClosed_eq (LpToLpRestrictCLM (ℝ^n) ℝ ℝ (domainMeasure n Ω) 2 Kᶜ).continuous
      continuous_const)

/-- The supported Sobolev ball is a complete metric space for the L² distance,
the metric used in a transport contraction argument. -/
theorem completeSpace_supportedHkBaseBall (n k : ℕ) (Ω K : Set (ℝ^n)) (B : ℝ) :
    CompleteSpace (supportedHkBaseBall n k Ω K B) := by
  have : IsClosed (supportedHkBaseBall n k Ω K B) :=
    isClosed_supportedHkBaseBall n k Ω K B
  exact IsClosed.completeSpace_coe

/-- Continuous time curves in the fixed-support Sobolev ball form a complete
space for the uniform L² metric on a closed time interval. -/
theorem completeSpace_supportedHkCurves
    (n k : ℕ) (Ω K : Set (ℝ^n)) (B t₀ T : ℝ) :
    CompleteSpace C(Icc t₀ T, supportedHkBaseBall n k Ω K B) := by
  have := completeSpace_supportedHkBaseBall n k Ω K B
  infer_instance

/-- The restriction condition in the iteration class means
almost-everywhere vanishing outside a measurable enclosure. -/
theorem mem_supportedHkBaseBall_iff {n k : ℕ} {Ω K : Set (ℝ^n)} {B : ℝ}
    (hK : MeasurableSet K) (f : DerivLp n 2 Ω) :
    f ∈ supportedHkBaseBall n k Ω K B ↔
      f ∈ hkBaseBall n k Ω B ∧
        ∀ᵐ x ∂domainMeasure n Ω, x ∉ K → f x = 0 := by
  change (_ ∧ _ = 0) ↔ _
  have hrestrict := LpToLpRestrictCLM_coeFn ℝ Kᶜ f
  have heq : LpToLpRestrictCLM (ℝ^n) ℝ ℝ (domainMeasure n Ω) 2 Kᶜ f = 0 ↔
      f =ᵐ[(domainMeasure n Ω).restrict Kᶜ] (0 : ℝ^n → ℝ) := by
    constructor
    · intro h
      exact hrestrict.symm.trans (h ▸ Lp.coeFn_zero _ _ _)
    · intro h
      exact Lp.ext (hrestrict.trans (h.trans (Lp.coeFn_zero _ _ _).symm))
  rw [heq]
  change (_ ∧ ∀ᵐ x ∂(domainMeasure n Ω).restrict Kᶜ, f x = 0) ↔ _
  rw [ae_restrict_iff' hK.compl]
  rfl

end SobolevSpace.GraphSpace
