/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.BochnerConsistency
public import PDE.Spaces.Sobolev.Approximation.Mollification.Reflection
public import PDE.Spaces.Sobolev.Approximation.Mollification.SobolevApproximation.CutoffRemainder
public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension
import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Mollification on higher-order Hilbert Sobolev graphs

Convolving each weak derivative with the same kernel preserves the Sobolev graph.
The resulting operator is a contraction at every positive scale and converges
strongly to the identity. A fixed bounded operator can therefore be inserted
between two mollifiers without changing its strong limit. In particular this
applies to compact smooth cutoff multiplication, with no highest weighted norm.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

variable {n k : ℕ}

/-- Coordinatewise convolution of a Sobolev graph in its finite ambient product. -/
def mollifierHkAmbientCLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    W^{k,2}(ℝ^n) →L[ℝ] WkpAmbientOn n k 2 univ :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : DerivIndex n k ↦ DerivLp n 2 univ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun a ↦ (mollifierRowCLM μ hε).comp (wkpCoordinateCLM a))

/-- Convolving all coordinates preserves the weak derivative constraints. -/
theorem mollifierHkAmbientCLM_mem (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (U : W^{k,2}(ℝ^n)) :
    mollifierHkAmbientCLM μ hε U ∈ wkpSubmoduleOn n k 2 univ := by
  have hb : MemLp (baseRepresentative U) 2 volume := by
    simpa only [baseRepresentative, domainMeasure, Measure.restrict_univ] using
      Lp.memLp ((U : WkpAmbientOn n k 2 univ) (baseIndex n k))
  have hs := mollify_contDiff_of_pos μ hε _ (hb.locallyIntegrable (by norm_num))
  have hrow (a : DerivIndex n k) :
      ((mollifierHkAmbientCLM μ hε U) a : ℝ^n → ℝ) =ᵐ[domainMeasure n univ]
        iteratedPartialDeriv a.toList (mollify μ ε (baseRepresentative U)) := by
    change (mollifierRowCLM μ hε (wkpCoordinateCLM a U) : ℝ^n → ℝ) =ᵐ[_] _
    simpa only [derivIndexOfList_toList] using
      mollifierRowCLM_coordinate_ae_iteratedPartialDeriv μ hε U a.toList
        a.toList_length_le
  intro a
  apply (hasWeakDerivativeOn_congr_ae
    (by simpa only [baseIndex_toList, iteratedPartialDeriv] using hrow (baseIndex n k))
    (hrow a)).mpr
  exact hasWeakDerivativeOn_iteratedPartialDeriv hs a.toList

/-- Convolution on Hᵏ acts on every weak derivative coordinate. -/
def mollifierHkCLM (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) :
    W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
  (mollifierHkAmbientCLM μ hε).codRestrict
    (wkpSubmoduleOn n k 2 univ) (mollifierHkAmbientCLM_mem μ hε)

/-- Each coordinate of the Hᵏ mollifier is convolution of that input coordinate. -/
@[simp]
theorem mollifierHkCLM_coordinate (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (U : W^{k,2}(ℝ^n)) (a : DerivIndex n k) :
    (mollifierHkCLM μ hε U : WkpAmbientOn n k 2 univ) a =
      mollifierRowCLM μ hε ((U : WkpAmbientOn n k 2 univ) a) :=
  rfl

/-- The base of the Hᵏ mollifier is the literal convolution almost everywhere. -/
theorem mollifierHkCLM_base_ae (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (U : W^{k,2}(ℝ^n)) :
    baseRepresentative (mollifierHkCLM μ hε U) =ᵐ[volume]
      mollify μ ε (baseRepresentative U) := by
  change (mollifierRowCLM μ hε (wkpCoordinateCLM (baseIndex n k) U) : ℝ^n → ℝ)
    =ᵐ[volume] _
  have h := mollifierRowCLM_coordinate_ae_iteratedPartialDeriv μ hε U
    (baseIndex n k).toList (baseIndex n k).toList_length_le
  rw [derivIndexOfList_toList] at h
  simpa only [baseIndex_toList, iteratedPartialDeriv,
    domainMeasure, Measure.restrict_univ] using h

/-- Positive-scale mollification does not increase the full Hᵏ graph norm. -/
theorem norm_mollifierHkCLM_apply_le (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (U : W^{k,2}(ℝ^n)) :
    ‖mollifierHkCLM μ hε U‖ ≤ ‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(mollifierHkCLM μ hε U : WkpAmbientOn n k 2 univ)‖ ^ 2 ≤
    ‖(U : WkpAmbientOn n k 2 univ)‖ ^ 2
  simp only [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum fun a _ ↦
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (norm_mollifierRowCLM_apply_le μ hε (wkpCoordinateCLM a U))

/-- The full Hᵏ graph converges strongly under any positive mollification
scales tending to zero. The input need not have compact support. -/
theorem tendsto_mollifierHkCLM (μ : Mollifier n) (ε : ℕ → ℝ)
    (hε : ∀ m, 0 < ε m) (hε0 : Tendsto ε atTop (𝓝 0))
    (U : W^{k,2}(ℝ^n)) :
    Tendsto (fun m ↦ mollifierHkCLM μ (hε m) U) atTop (𝓝 U) := by
  apply tendsto_subtype_rng.mpr
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivIndex n k ↦ DerivLp n 2 univ)
  have h := tendsto_pi_nhds.mpr fun a ↦
    tendsto_mollifierRowCLM μ ε hε hε0 (wkpCoordinateCLM a U)
  exact e.symm.continuous.continuousAt.tendsto.comp h

/-- A fixed bounded operator between two approximate identities has the
expected strong limit. The two kernels and positive scales may differ. -/
theorem tendsto_mollifierHkCLM_comp (μ ν : Mollifier n)
    (A : W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n))
    (ε η : ℕ → ℝ) (hε : ∀ m, 0 < ε m) (hη : ∀ m, 0 < η m)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hη0 : Tendsto η atTop (𝓝 0))
    (U : W^{k,2}(ℝ^n)) :
    Tendsto (fun m ↦ mollifierHkCLM ν (hη m) (A (mollifierHkCLM μ (hε m) U)))
      atTop (𝓝 (A U)) := by
  have hA := A.continuous.continuousAt.tendsto.comp (tendsto_mollifierHkCLM μ ε hε hε0 U)
  have hsmall : Tendsto
      (fun m ↦ mollifierHkCLM ν (hη m) (A (mollifierHkCLM μ (hε m) U) - A U))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun m ↦ norm_mollifierHkCLM_apply_le ν (hη m) _)
    exact (tendsto_iff_norm_sub_tendsto_zero.mp hA)
  have h := hsmall.add (tendsto_mollifierHkCLM ν η hη hη0 (A U))
  simpa only [map_sub, sub_add_cancel, zero_add] using h

/-- The graph operator with two mollifiers and a compact multiplier has the
literal double convolution as its base. -/
theorem mollifierHkCLM_cutoff_mollifier_base_ae
    (hk : 0 < k) (μ ν : Mollifier n)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{k,2}(ℝ^n))
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    baseRepresentative (mollifierHkCLM ν hη
      (higherOrderCutoffCLM hk isOpen_univ ψ (mollifierHkCLM μ hε U))) =ᵐ[volume]
        mollify ν η (fun x ↦ ψ.toFun x * mollify μ ε (baseRepresentative U) x) := by
  have hb : baseRepresentative (higherOrderCutoffCLM hk isOpen_univ ψ
      (mollifierHkCLM μ hε U)) =ᵐ[volume]
        fun x ↦ ψ.toFun x * mollify μ ε (baseRepresentative U) x := by
    have hcut := higherOrderCutoffCLM_base_ae hk isOpen_univ ψ (mollifierHkCLM μ hε U)
    simp only [domainMeasure, Measure.restrict_univ] at hcut
    exact hcut.trans ((EventuallyEq.refl _ _).fun_mul (mollifierHkCLM_base_ae μ hε U))
  rw [← mollify_congr_ae ν η hb]
  exact mollifierHkCLM_base_ae ν hη _

/-- Double mollification of a compact multiplier has the expected strong Hᵏ
limit. The smooth approximants are identified only by their bases. -/
theorem tendsto_double_mollified_testGraph
    (hk : 0 < k) (μ ν : Mollifier n)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{k,2}(ℝ^n))
    (ε η : ℕ → ℝ) (hε : ∀ m, 0 < ε m) (hη : ∀ m, 0 < η m)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hη0 : Tendsto η atTop (𝓝 0))
    (G : ℕ → W^{k,2}(ℝ^n))
    (hG : ∀ m, baseRepresentative (G m) =ᵐ[volume]
      mollify ν (η m) (fun x ↦ ψ.toFun x * mollify μ (ε m) (baseRepresentative U) x)) :
    Tendsto G atTop (𝓝 (higherOrderCutoffCLM hk isOpen_univ ψ U)) := by
  have heq (m : ℕ) : G m =
      mollifierHkCLM ν (hη m)
        (higherOrderCutoffCLM hk isOpen_univ ψ (mollifierHkCLM μ (hε m) U)) := by
    apply WkpSpaceOn.ext_of_base_ae isOpen_univ
    change baseRepresentative _ =ᵐ[domainMeasure n univ] baseRepresentative _
    simp only [domainMeasure, Measure.restrict_univ]
    exact (hG m).trans
      (mollifierHkCLM_cutoff_mollifier_base_ae hk μ ν ψ U (hε m) (hη m)).symm
  exact (tendsto_mollifierHkCLM_comp μ ν
    (higherOrderCutoffCLM hk isOpen_univ ψ) ε η hε hη hε0 hη0 U).congr fun m ↦ (heq m).symm

/-- Double mollification inside a compact test collar converges strongly to
the canonical extension of the local cutoff product. The source has only a
local Hᵏ graph; its values outside the open domain may be arbitrary. -/
theorem tendsto_local_double_mollified_testGraph
    (hk : 0 < k) {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψΩ : tsupport ψ.toFun ⊆ Ω)
    (U : W^{k,2}(Ω)) {f : ℝ^n → ℝ}
    (hf : baseRepresentative U =ᵐ[domainMeasure n Ω] f)
    (μ ν : Mollifier n) (ε η : ℕ → ℝ)
    (hε : ∀ m, 0 < ε m) (hη : ∀ m, 0 < η m)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hη0 : Tendsto η atTop (𝓝 0))
    (G : ℕ → W^{k,2}(ℝ^n))
    (hG : ∀ m, baseRepresentative (G m) =ᵐ[volume]
      mollify ν (η m) (fun x ↦ ψ.toFun x * mollify μ (ε m) f x)) :
    Tendsto G atTop (𝓝
      (CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff
        hΩ (subset_univ Ω) ψ hψΩ U)) := by
  obtain ⟨δ₁, hδ₁, hδ₁Ω⟩ := ψ.hasCompactSupport.exists_cthickening_subset_open hΩ hψΩ
  obtain ⟨δ₂, hδ₂, hδ₂K⟩ := ψ.hasCompactSupport.exists_isCompact_cthickening
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  let S := Metric.cthickening δ (tsupport ψ.toFun)
  have hS : IsCompact S := hδ₂K.of_isClosed_subset Metric.isClosed_cthickening
    (Metric.cthickening_mono (min_le_right δ₁ δ₂) _)
  have hSΩ : S ⊆ Ω := (Metric.cthickening_mono (min_le_left δ₁ δ₂) _).trans hδ₁Ω
  obtain ⟨θ, hθΩ, hθone, _, _⟩ := TestFunction.exists_eq_one_on_compact hΩ hS hSΩ
  let E := CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff
    hΩ (subset_univ Ω) θ hθΩ U
  have hE : baseRepresentative E =ᵐ[volume] fun x ↦ θ.toFun x * baseRepresentative U x := by
    simpa only [E, domainMeasure, Measure.restrict_univ] using
      CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff_base_ae
        hΩ (subset_univ Ω) θ hθΩ U
  have hEf : baseRepresentative E =ᵐ[volume.restrict S] f := by
    filter_upwards [hE.filter_mono (ae_mono Measure.restrict_le_self),
      hf.filter_mono (ae_mono (domainMeasure_le hSΩ)),
      ae_restrict_mem hS.measurableSet] with x hx hfx hxS
    rw [hx, hθone x hxS, one_mul, hfx]
  have hsmall : ∀ᶠ m in atTop,
      Function.support (scaled μ (ε m)) ⊆ Metric.ball 0 δ :=
    (tendsto_smallSets_iff.mp (tendsto_support_scaled μ ε hε hε0))
      _ (Metric.ball_mem_nhds _ hδ)
  have hinner : ∀ᶠ m in atTop,
      (fun x ↦ ψ.toFun x * mollify μ (ε m) f x) =
        fun x ↦ ψ.toFun x * mollify μ (ε m) (baseRepresentative E) x := by
    filter_upwards [hsmall] with m hm
    funext x
    by_cases hx : ψ.toFun x = 0
    · simp only [hx, zero_mul]
    · congr 1
      apply mollify_congr_ae_on_collar μ (ε m) hS.measurableSet hEf.symm
      intro y hy
      apply Metric.mem_cthickening_of_dist_le (x - y) x δ _
        (subset_tsupport _ hx)
      have hnorm : ‖y‖ < δ := by simpa using hm hy
      simpa only [dist_eq_norm, sub_sub_cancel_left, norm_neg] using hnorm.le
  let H (m : ℕ) := mollifierHkCLM ν (hη m)
    (higherOrderCutoffCLM hk isOpen_univ ψ (mollifierHkCLM μ (hε m) E))
  have heq : G =ᶠ[atTop] H := by
    filter_upwards [hinner] with m hm
    apply WkpSpaceOn.ext_of_base_ae isOpen_univ
    change baseRepresentative _ =ᵐ[domainMeasure n univ] baseRepresentative _
    simp only [domainMeasure, Measure.restrict_univ]
    have hgm := hG m
    rw [hm] at hgm
    exact hgm.trans
      (mollifierHkCLM_cutoff_mollifier_base_ae hk μ ν ψ E (hε m) (hη m)).symm
  have hlimit := tendsto_mollifierHkCLM_comp μ ν
    (higherOrderCutoffCLM hk isOpen_univ ψ) ε η hε hη hε0 hη0 E
  have htarget : higherOrderCutoffCLM hk isOpen_univ ψ E =
      CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff
        hΩ (subset_univ Ω) ψ hψΩ U := by
    apply WkpSpaceOn.ext_of_base_ae isOpen_univ
    change baseRepresentative _ =ᵐ[domainMeasure n univ] baseRepresentative _
    have hleft := higherOrderCutoffCLM_base_ae hk isOpen_univ ψ E
    have hright := CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff_base_ae
      hΩ (subset_univ Ω) ψ hψΩ U
    simp only [domainMeasure, Measure.restrict_univ] at hleft hright ⊢
    filter_upwards [hleft, hright, hE] with x hl hr he
    rw [hl, hr, he]
    by_cases hx : ψ.toFun x = 0
    · simp only [hx, zero_mul]
    · rw [hθone x (Metric.self_subset_cthickening _ (subset_tsupport _ hx)), one_mul]
  rw [← htarget]
  exact hlimit.congr' heq.symm

/-- The smooth double tests converge in the local Hᵏ graph to the
cutoff product on that same domain. Their source representative is specified
only almost everywhere locally, and no global Hᵏ extension is an assumption. -/
theorem tendsto_local_double_mollified_smoothGraph
    (hk : 0 < k) {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψΩ : tsupport ψ.toFun ⊆ Ω)
    (U : W^{k,2}(Ω)) {f : ℝ^n → ℝ}
    (hf : baseRepresentative U =ᵐ[domainMeasure n Ω] f)
    (μ ν : Mollifier n) (ε η : ℕ → ℝ)
    (hε : ∀ m, 0 < ε m) (hη : ∀ m, 0 < η m)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hη0 : Tendsto η atTop (𝓝 0))
    (g : ℕ → ℝ^n → ℝ) (hg : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (g m))
    (hgc : ∀ m, HasCompactSupport (g m))
    (hgeq : ∀ m, g m = mollify ν (η m)
      (fun x ↦ ψ.toFun x * mollify μ (ε m) f x)) :
    Tendsto (fun m ↦ mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := Ω)
      (g m) (hg m) (hgc m)) atTop (𝓝 (higherOrderCutoffCLM hk hΩ ψ U)) := by
  let G (m : ℕ) : W^{k,2}(ℝ^n) :=
    mkWkpSpaceOnOfContDiff (g m) (hg m) (hgc m)
  have hb (S : Set (ℝ^n)) (m : ℕ) :
      baseRepresentative (mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := S)
        (g m) (hg m) (hgc m)) =ᵐ[domainMeasure n S] g m := by
    simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (p := (2 : ℝ≥0∞)) (Ω := S)
        (g m) (hg m) (hgc m) (baseIndex n k)
  have hG (m : ℕ) : baseRepresentative (G m) =ᵐ[volume]
      mollify ν (η m) (fun x ↦ ψ.toFun x * mollify μ (ε m) f x) := by
    have h := hb univ m
    simpa only [G, domainMeasure, Measure.restrict_univ, hgeq m] using h
  let A := CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff
    hΩ (subset_univ Ω) ψ hψΩ U
  let T : W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(Ω) :=
    restrictCLM hΩ.measurableSet (subset_univ Ω)
  have hlimit := T.continuous.continuousAt.tendsto.comp
    (tendsto_local_double_mollified_testGraph hk hΩ ψ hψΩ U hf μ ν
      ε η hε hη hε0 hη0 G hG)
  have htarget : T A = higherOrderCutoffCLM hk hΩ ψ U := by
    apply WkpSpaceOn.ext_of_base_ae hΩ
    change baseRepresentative _ =ᵐ[domainMeasure n Ω] baseRepresentative _
    have hA := CompactSupportLocalization.HigherOrderLocalizedCutoff.extendByCutoff_base_ae
      hΩ (subset_univ Ω) ψ hψΩ U
    exact ((restrictCLM_apply_ae hΩ.measurableSet (subset_univ Ω) A (baseIndex n k)).trans
      (hA.filter_mono (ae_mono (domainMeasure_le (subset_univ Ω))))).trans
        (higherOrderCutoffCLM_base_ae hk hΩ ψ U).symm
  have heq (m : ℕ) : T (G m) =
      mkWkpSpaceOnOfContDiff (k := k) (p := 2) (Ω := Ω) (g m) (hg m) (hgc m) := by
    apply WkpSpaceOn.ext_of_base_ae hΩ
    change baseRepresentative _ =ᵐ[domainMeasure n Ω] baseRepresentative _
    exact ((restrictCLM_apply_ae hΩ.measurableSet (subset_univ Ω) (G m)
      (baseIndex n k)).trans
        ((hb univ m).filter_mono (ae_mono (domainMeasure_le (subset_univ Ω))))).trans
          (hb Ω m).symm
  rw [show higherOrderCutoffCLM hk hΩ ψ U = T A from htarget.symm]
  exact hlimit.congr heq

end SobolevSpace.Approximation
