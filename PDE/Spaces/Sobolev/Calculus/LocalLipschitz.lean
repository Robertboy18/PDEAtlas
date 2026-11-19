/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.LipschitzCompactSupport
public import PDE.Spaces.Sobolev.GraphSpace.Local.Definitions
import PDE.Analysis.MeasureTheory.Lp.Continuous
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Locality

/-!
# Local Sobolev membership of locally Lipschitz functions

On each relatively compact subdomain a locally Lipschitz scalar function has a
Lipschitz extension. Its classical coordinate derivatives are weak derivatives
and bounded, so all first-order rows belong to every `Lᵖ`, including `L∞`.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set Filter
open scoped ENNReal NNReal Sobolev Topology

private theorem weak_partialDeriv_on {n : ℕ} {f : ℝ^n → ℝ}
    (hf : LocallyLipschitz f) {V : Set (ℝ^n)} (hV : IsOpen V)
    (hcompact : IsCompact (closure V)) (i : Fin n) :
    HasWeakDerivativeOn V [i] f (PDE.partialDeriv i f) := by
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    hcompact hf.locallyLipschitzOn
  obtain ⟨g, hg, hfg⟩ := hK.extend_real
  have hbase : g =ᵐ[domainMeasure n V] f := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    exact (hfg (subset_closure hx)).symm
  have hderiv : PDE.partialDeriv i g =ᵐ[domainMeasure n V] PDE.partialDeriv i f := by
    filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
    have hnear : f =ᶠ[𝓝 x] g :=
      Filter.mem_of_superset (hV.mem_nhds hx) (fun y hy ↦ hfg (subset_closure hy))
    exact congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
      (hnear.fderiv_eq (𝕜 := ℝ)).symm
  exact ((hasWeakDerivativeOn_partialDeriv_of_lipschitzWith hg i).mono
    hV.measurableSet (subset_univ V)).congr_ae hbase hderiv

/-- The totalized classical partial derivative of a locally Lipschitz field
represents its global weak derivative, including across its nondifferentiable points. -/
theorem hasWeakDerivativeOn_partialDeriv_of_locallyLipschitz {n : ℕ} {f : ℝ^n → ℝ}
    (hf : LocallyLipschitz f) (i : Fin n) :
    HasWeakDerivativeOn univ [i] f (PDE.partialDeriv i f) := by
  apply hasWeakDerivativeOn_single_of_open_cover (fun x : ℝ^n ↦ Metric.ball x 1)
    (fun _ ↦ Metric.isOpen_ball) (fun x _ ↦ mem_iUnion.mpr ⟨x, Metric.mem_ball_self zero_lt_one⟩)
    i
  intro x
  apply weak_partialDeriv_on hf Metric.isOpen_ball
  exact Metric.isBounded_ball.isCompact_closure

/-- On a bounded open domain a locally Lipschitz field has a Sobolev graph
whose first-order rows are its ordinary partial derivatives almost everywhere. -/
theorem exists_sobolev_rows_of_locallyLipschitz {n : ℕ} {p : ℝ≥0∞}
    {f : ℝ^n → ℝ} (hf : LocallyLipschitz f) {V : Set (ℝ^n)} (hV : IsOpen V)
    (hbounded : Bornology.IsBounded V) :
    ∃ U : W^{1,p}(V), ∀ a : DerivIndex n 1,
      (U.val a : ℝ^n → ℝ) =ᵐ[domainMeasure n V]
        firstOrderRows f (fun i ↦ PDE.partialDeriv i f) a := by
  have hcompact := hbounded.isCompact_closure
  let : IsFiniteMeasure (domainMeasure n V) := isFiniteMeasure_restrict.mpr
    ((measure_mono subset_closure).trans_lt hcompact.measure_lt_top).ne
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    hcompact hf.locallyLipschitzOn
  have hmem (a : DerivIndex n 1) :
      MemLp (firstOrderRows f (fun i ↦ PDE.partialDeriv i f) a) p (domainMeasure n V) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [firstOrderRows_baseIndex, domainMeasure] using
        hf.continuous.continuousOn.memLp_of_subset_isCompact hcompact
          hV.measurableSet subset_closure
    · rw [firstOrderRows_singleDerivIndex]
      apply MemLp.of_bound
        (measurable_fderiv_apply_const ℝ f (EuclideanSpace.single i 1)).aestronglyMeasurable K
      filter_upwards [ae_restrict_mem hV.measurableSet] with x hx
      have hnhds : closure V ∈ 𝓝 x := mem_of_superset (hV.mem_nhds hx) subset_closure
      calc
        ‖PDE.partialDeriv i f x‖ ≤ ‖fderiv ℝ f x‖ * ‖EuclideanSpace.single i (1 : ℝ)‖ :=
          (fderiv ℝ f x).le_opNorm _
        _ ≤ K := by simpa using norm_fderiv_le_of_lipschitzOn ℝ hnhds hK
  have hweak (a : DerivIndex n 1) :
      HasWeakDerivativeOn V a.toList f (firstOrderRows f (fun i ↦ PDE.partialDeriv i f) a) := by
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [firstOrderRows_baseIndex, baseIndex_toList] using
        hasWeakDerivativeOn_nil (hf.continuous.locallyIntegrable.locallyIntegrableOn V)
    · simpa only [firstOrderRows_singleDerivIndex, singleDerivIndex_toList] using
        (hasWeakDerivativeOn_partialDeriv_of_locallyLipschitz hf i).mono
          hV.measurableSet (subset_univ V)
  refine ⟨mkWkpSpaceOnOfWeakDerivatives f (firstOrderRows f (fun i ↦ PDE.partialDeriv i f))
    (firstOrderRows_baseIndex _ _) hmem hweak, ?_⟩
  exact fun a ↦ mkWkpSpaceOnOfWeakDerivatives_apply_ae f
    (firstOrderRows f (fun i ↦ PDE.partialDeriv i f)) (firstOrderRows_baseIndex _ _) hmem hweak a

/-- Every locally Lipschitz scalar field belongs locally to `W¹ᵖ`, for every exponent `p`,
including `p = ∞`. No differentiability is required at corners or isolated points. -/
theorem isLocallyWkpOn_of_locallyLipschitz {n : ℕ} {p : ℝ≥0∞}
    {f : ℝ^n → ℝ} (hf : LocallyLipschitz f) : IsLocallyWkpOn 1 p univ f := by
  intro V hV hcompact _
  obtain ⟨U, hU⟩ := exists_sobolev_rows_of_locallyLipschitz (p := p) hf hV
    (hcompact.isBounded.subset subset_closure)
  refine ⟨U, ?_⟩
  simpa only [baseRepresentative, firstOrderRows_baseIndex] using hU (baseIndex n 1)

end SobolevSpace.GraphSpace
