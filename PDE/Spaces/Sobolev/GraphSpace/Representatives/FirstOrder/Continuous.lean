/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder.Classical
import PDE.Analysis.Calculus.CompactLpCurry
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support

/-!
# Continuous families of first-order Sobolev representatives

Joint continuity of a compactly supported family and its first spatial derivatives
makes each coordinate continuous in Lᵖ. The Sobolev graph construction then gives
one continuous W^{1,p} family whose weak derivatives are the ordinary derivatives.

The parameter space is arbitrary. The spatial dimension may be zero, the open domain
need not be bounded, and p = ∞ is allowed. The common support belongs to the ambient
Euclidean space; it need not lie inside the domain, so no zero boundary trace is asserted.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory TopologicalSpace PDE SobolevSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

/-- Jointly continuous C¹ spatial slices with a common compact support give a
continuous W^{1,p} curve with the ordinary coordinate derivatives as its weak rows. -/
theorem exists_continuous_firstOrder_of_common_compact_support
    {X : Type*} [TopologicalSpace X] {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (K : Compacts (ℝ^n)) {f : X → ℝ^n → ℝ} (hf : Continuous f.uncurry)
    (hreg : ∀ t, ContDiff ℝ 1 (f t))
    (hpartial : ∀ i : Fin n, Continuous (fun z : X × ℝ^n ↦ (∂[i] (f z.1)) z.2))
    (hsupp : ∀ t x, x ∉ K → f t x = 0) :
    ∃ q : X → W^{1,p}(Ω), Continuous q ∧ ∀ t,
      (wkpBaseCoordinateCLM (q t) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f t ∧
      ∀ i : Fin n, (wkpCoordinateCLM (singleDerivIndex n i) (q t) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] ∂[i] (f t) := by
  have : IsFiniteMeasure ((domainMeasure n Ω).restrict (K : Set (ℝ^n))) :=
    isFiniteMeasure_restrict.mpr K.isCompact.measure_ne_top
  have hsupport (t : X) : tsupport (f t) ⊆ K := by
    apply closure_minimal _ K.isCompact.isClosed
    intro x hx
    by_contra hm
    exact hx (hsupp t x hm)
  have hcompact (t : X) : HasCompactSupport (f t) :=
    HasCompactSupport.intro K.isCompact (hsupp t)
  have hrows (t : X) : ∃ q : W^{1,p}(Ω),
      (wkpBaseCoordinateCLM q : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f t ∧
      ∀ i : Fin n, (wkpCoordinateCLM (singleDerivIndex n i) q : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] ∂[i] (f t) := by
    exact (existsUnique_firstOrder_of_contDiffOn_memLp hΩ
      (hreg t).contDiffOn
      ((hreg t).continuous.memLp_of_hasCompactSupport (hcompact t))
      (fun i ↦ ((hreg t).continuous_partialDeriv i).memLp_of_hasCompactSupport
        ((hcompact t).partialDeriv i))).exists
  choose q hq using hrows
  refine ⟨q, ?_, hq⟩
  have hcoord (a : DerivIndex n 1) : Continuous (fun t ↦
      (q t : WkpAmbientOn n 1 p Ω) a) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · exact continuous_Lp_of_common_compact_support K hf hsupp (fun t ↦ (hq t).1)
    · apply continuous_Lp_of_common_compact_support K (hpartial i) _ (fun t ↦ (hq t).2 i)
      intro t x hx
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hx (hsupport t ((tsupport_partialDeriv_subset i) hm))
  apply continuous_induced_rng.mpr
  exact (PiLp.continuous_toLp p _).comp (continuous_pi hcoord)

end SobolevSpace.GraphSpace
