/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.WeakConvergence.Compact
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder.Representative

/-!
# C¹ matching from an L² limit and a uniform H² bound

The base L² limit identifies the weak H² limit. Its lower-order and derivative
graphs converge weakly in H¹, so both continuous representatives converge
uniformly on compact sets. No continuity in the strong H² topology or in a
space of classical derivatives is assumed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- The lower-order continuous representative has the original H² base class. -/
theorem realLineRepresentative_lowerOrder_ae (W : W^{2,2}(ℝ^1)) :
    (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ) =ᵐ[volume]
      realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) := by
  have hbase : realLineCoordinateCLM (baseIndex 1 1)
      (lowerOrderCLM (by decide : 1 ≤ 2) W) =
        oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) := by
    apply congrArg oneDimensionalPushforwardL2
    change (lowerOrderCLM (by decide : 1 ≤ 2) W : WkpAmbientOn 1 1 2 univ)
      (baseIndex 1 1) = (W : WkpAmbientOn 1 2 2 univ) (baseIndex 1 2)
    simp only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex]
  exact hbase ▸ realLineCoordinate_ae_representative
    (lowerOrderCLM (by decide : 1 ≤ 2) W)

/-- The continuous representative of an H² graph has the representative of its first weak
derivative as classical derivative. -/
theorem hasDerivAt_realLineRepresentative_lowerOrder (A : W^{2,2}(ℝ^1)) (x : ℝ) :
    HasDerivAt (realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) A))
      (realLineRepresentative (∂[0] A) x) x :=
  hasDerivAt_realLineRepresentative_of_h1_derivative _ _
    (realLineCoordinateCLM_partialDeriv_h2_base A) x

/-- The classical derivative of the lower-order representative is the continuous
representative of the first weak derivative graph. -/
theorem deriv_realLineRepresentative_lowerOrder (W : W^{2,2}(ℝ^1)) :
    deriv (realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W)) =
      realLineRepresentative
        (∂[0] W) := by
  funext x
  apply HasDerivAt.deriv
  apply hasDerivAt_realLineRepresentative_of_h1_derivative
  apply congrArg oneDimensionalPushforwardL2
  change (∂[0] W :
      WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
    (lowerOrderCLM (by decide : 1 ≤ 2) W : WkpAmbientOn 1 1 2 univ)
      (singleDerivIndex 1 0)
  simp only [partialDerivCLM, derivativeWordCLM_apply,
    derivativeWordIndex_singleton_baseIndex, lowerOrderCLM_apply,
    DerivIndex.castOrder_singleDerivIndex]

/-- Strong convergence of the L² base of a bounded H² family gives simultaneous
compact uniform convergence of its continuous representatives and first derivatives.
The only regularity required of the supplied representatives is spatial continuity. -/
theorem tendstoUniformlyOn_h2_representative_and_deriv
    {ι : Type*} {l : Filter ι} {u : ι → W^{2,2}(ℝ^1)}
    {U : W^{2,2}(ℝ^1)} {B : ℝ} (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ wkpBaseCoordinateCLM (u i)) l
      (𝓝 (wkpBaseCoordinateCLM U)))
    {w : ι → ℝ → ℝ} {v : ℝ → ℝ}
    (hw : ∀ i, Continuous (w i)) (hv : Continuous v)
    (hrep : ∀ i, (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM (u i)) : ℝ → ℝ)
      =ᵐ[volume] w i)
    (hvrep : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM U) : ℝ → ℝ)
      =ᵐ[volume] v)
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn w v l K ∧
      TendstoUniformlyOn (fun i ↦ deriv (w i)) (deriv v) l K := by
  have hweak := tendsto_weak_hk_of_base isOpen_univ u U
    (isBounded_iff_forall_norm_le.mpr ⟨B, by rintro _ ⟨i, rfl⟩; exact hbound i⟩)
    ((toWeakSpaceCLM ℝ _).continuous.continuousAt.tendsto.comp hbase)
  let A := lowerOrderCLM (n := 1) (p := 2) (Ω := univ) (by decide : 1 ≤ 2)
  let D : W^{2,2}(ℝ^1) →L[ℝ] W^{1,2}(ℝ^1) := partialDerivCLM 0
  have ha (i : ι) : realLineRepresentative (A (u i)) = w i :=
    (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _) (hw i)).mp
      ((realLineRepresentative_lowerOrder_ae (u i)).symm.trans (hrep i))
  have hav : realLineRepresentative (A U) = v :=
    (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _) hv).mp
      ((realLineRepresentative_lowerOrder_ae U).symm.trans hvrep)
  have hd (i : ι) : realLineRepresentative (D (u i)) = deriv (w i) := by
    rw [← ha i]
    exact (deriv_realLineRepresentative_lowerOrder (u i)).symm
  have hdv : realLineRepresentative (D U) = deriv v := by
    rw [← hav]
    exact (deriv_realLineRepresentative_lowerOrder U).symm
  have hA : TendstoUniformlyOn (fun i ↦ realLineRepresentative (A (u i)))
      (realLineRepresentative (A U)) l K :=
    tendstoUniformlyOn_realLineRepresentative_of_weak
    (fun i ↦ (norm_lowerOrderCLM_apply_le _ (u i)).trans (hbound i))
    (((WeakSpace.map A).continuous.tendsto _).comp hweak) hK
  have hD : TendstoUniformlyOn (fun i ↦ realLineRepresentative (D (u i)))
      (realLineRepresentative (D U)) l K :=
    tendstoUniformlyOn_realLineRepresentative_of_weak
    (fun i ↦ (norm_partialDeriv_le 0 (u i)).trans (hbound i))
    (((WeakSpace.map D).continuous.tendsto _).comp hweak) hK
  exact ⟨by simpa only [ha, hav] using hA, by simpa only [hd, hdv] using hD⟩

/-- A bounded H² base family with an L² limit constructs its terminal H² graph
and a C¹ representative, with compact uniform convergence of both the functions
and their first derivatives. The terminal representative is part of the conclusion. -/
theorem exists_h2_c1_limit_of_tendsto_base
    {ι : Type*} {l : Filter ι} [l.NeBot] {B : NNReal}
    {f : ι → DerivLp 1 2 univ} {g : DerivLp 1 2 univ}
    (hbound : ∀ i, f i ∈ hkBaseBall 1 2 univ B)
    (hbase : Tendsto f l (𝓝 g))
    {w : ι → ℝ → ℝ} (hw : ∀ i, Continuous (w i))
    (hrep : ∀ i, (oneDimensionalPushforwardL2 (f i) : ℝ → ℝ) =ᵐ[volume] w i) :
    ∃ (U : W^{2,2}(ℝ^1)) (v : ℝ → ℝ),
      ‖U‖ ≤ B ∧ wkpBaseCoordinateCLM U = g ∧ ContDiff ℝ 1 v ∧
      (oneDimensionalPushforwardL2 g : ℝ → ℝ) =ᵐ[volume] v ∧
      ∀ K : Set ℝ, IsCompact K →
        TendstoUniformlyOn w v l K ∧
          TendstoUniformlyOn (fun i ↦ deriv (w i)) (deriv v) l K := by
  obtain ⟨U, hU, hUg⟩ := (isClosed_hkBaseBall 1 2 univ B).mem_of_tendsto
    hbase (Eventually.of_forall hbound)
  choose u hu hubase using hbound
  let v := realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) U)
  have hv : Continuous v := continuous_realLineRepresentative _
  have hvrep := realLineRepresentative_lowerOrder_ae U
  refine ⟨U, v, hU, hUg, (contDiff_and_bounds_of_h2_representative U hv hvrep).1,
    hUg ▸ hvrep, fun K hK ↦ ?_⟩
  apply tendstoUniformlyOn_h2_representative_and_deriv hu _ hw hv _ hvrep hK
  · simpa only [hubase, hUg] using hbase
  · simpa only [hubase] using hrep

/-- A prescribed continuous representative of the limiting base is the compact
C¹ limit. Neither a choice of graph nor a derivative convergence hypothesis is
needed at the interface. -/
theorem tendstoUniformlyOn_representative_and_deriv_of_hkBaseBall
    {ι : Type*} {l : Filter ι} {B : NNReal}
    {f : ι → DerivLp 1 2 univ} {g : DerivLp 1 2 univ}
    (hbound : ∀ i, f i ∈ hkBaseBall 1 2 univ B)
    (hg : g ∈ hkBaseBall 1 2 univ B) (hbase : Tendsto f l (𝓝 g))
    {w : ι → ℝ → ℝ} {v : ℝ → ℝ}
    (hw : ∀ i, Continuous (w i)) (hv : Continuous v)
    (hrep : ∀ i, (oneDimensionalPushforwardL2 (f i) : ℝ → ℝ) =ᵐ[volume] w i)
    (hvrep : (oneDimensionalPushforwardL2 g : ℝ → ℝ) =ᵐ[volume] v)
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn w v l K ∧
      TendstoUniformlyOn (fun i ↦ deriv (w i)) (deriv v) l K := by
  choose u hu hubase using hbound
  obtain ⟨U, _, hUg⟩ := hg
  apply tendstoUniformlyOn_h2_representative_and_deriv (U := U) hu _ hw hv _ _ hK
  · simpa only [hubase, hUg] using hbase
  · simpa only [hubase] using hrep
  · simpa only [hUg] using hvrep

/-- An L²-continuous family in a bounded H² base ball has jointly continuous
spatial representatives and first derivatives. Only continuity of each spatial
representative is supplied; continuity in the parameter is derived. -/
theorem continuous_representative_and_deriv_of_hkBaseBall
    {X : Type*} [TopologicalSpace X] {B : NNReal}
    {f : X → DerivLp 1 2 univ} (hf : Continuous f)
    (hbound : ∀ t, f t ∈ hkBaseBall 1 2 univ B)
    {w : X → ℝ → ℝ} (hw : ∀ t, Continuous (w t))
    (hrep : ∀ t, (oneDimensionalPushforwardL2 (f t) : ℝ → ℝ) =ᵐ[volume] w t) :
    Continuous (fun p : ℝ × X ↦ w p.2 p.1) ∧
      Continuous (fun p : ℝ × X ↦ deriv (w p.2) p.1) := by
  have hd (t : X) : Continuous (deriv (w t)) :=
    (contDiff_one_iff_deriv.mp
      (contDiff_and_bounds_of_hkBaseBall (hbound t) (hw t) (hrep t)).1).2
  have hlim (t : X) {K : Set ℝ} (hK : IsCompact K) :=
    tendstoUniformlyOn_representative_and_deriv_of_hkBaseBall
      hbound (hbound t) (hf.tendsto t) hw (hw t) hrep (hrep t) hK
  have hwC : Continuous (fun t : X ↦ (⟨w t, hw t⟩ : C(ℝ, ℝ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
      fun _ hK ↦ (hlim t hK).1
  have hdC : Continuous (fun t : X ↦ (⟨deriv (w t), hd t⟩ : C(ℝ, ℝ))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
      fun _ hK ↦ (hlim t hK).2
  exact ⟨continuous_eval.comp ((hwC.comp continuous_snd).prodMk continuous_fst),
    continuous_eval.comp ((hdC.comp continuous_snd).prodMk continuous_fst)⟩

end SobolevSpace.GraphSpace
