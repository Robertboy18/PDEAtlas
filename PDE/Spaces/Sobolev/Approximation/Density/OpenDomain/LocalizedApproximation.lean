/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Global
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
public import PDE.Spaces.Sobolev.Localization.Cutoff.HigherOrderExtension
import PDE.DistributionTheory.TestFunction.CompactCutoff

/-!
# Approximation after a fixed interior cutoff

The weak Leibniz rule gives cutoff multiplication at every finite Sobolev order and every
exponent at least one. Its graph is closed: convergence of the base coordinates identifies
the product in the limit. The closed graph theorem therefore makes this a bounded operator.

To smooth a function near a compact subset of an open domain, first multiply it by an interior
cutoff equal to one there. Whole-space mollification and cutoff density then apply to that
localized function. A second, fixed multiplier keeps the approximation error on the original
compact set.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Topology Sobolev

namespace SobolevSpace.Approximation.OpenDomain

open GraphSpace CompactSupportLocalization.HigherOrderLocalizedCutoff

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A fixed test function acts continuously on the whole-space Sobolev graph of every finite
order. Membership comes from the weak Leibniz rule; boundedness follows from the closed graph
theorem and continuity of multiplication on the base `Lᵖ` coordinate. -/
def testMultiplier (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    W^{k,p}(ℝ^n) →L[ℝ] W^{k,p}(ℝ^n) :=
  let A := extendByCutoffLinearMap (k := k) (p := p) isOpen_univ isOpen_univ
    (Subset.rfl : (univ : Set (ℝ^n)) ⊆ univ) ψ (subset_univ _)
  { toLinearMap := A
    cont := by
      let B := wkpBaseCoordinateCLM (n := n) (m := k) (p := p) (Ω := univ)
      let M := mulLpLeft (p := p) (testFunctionLpTop (Ω := univ) ψ)
      have hAB (U : W^{k,p}(ℝ^n)) : B (A U) = M (B U) := by
        apply Lp.ext
        filter_upwards [extendByCutoff_base_ae isOpen_univ (Subset.rfl) ψ (subset_univ _) U,
          mulLpLeft_apply_ae (testFunctionLpTop (Ω := univ) ψ) (B U),
          testFunctionLpTop_apply_ae (Ω := univ) ψ] with x hx hy hz
        exact hx.trans (by simpa only [hz, B, M, wkpBaseCoordinateCLM_apply,
          baseRepresentative] using hy.symm)
      apply A.continuous_of_seq_closed_graph
      intro u U V hu hAu
      apply wkpBaseCoordinateCLM_injective isOpen_univ
      change B V = B (A U)
      have hleft := B.continuous.continuousAt.tendsto.comp hAu
      have hright := (M.comp B).continuous.continuousAt.tendsto.comp hu
      change Filter.Tendsto (fun j ↦ B (A (u j))) _ (𝓝 (B V)) at hleft
      change Filter.Tendsto (fun j ↦ M (B (u j))) _ (𝓝 (M (B U))) at hright
      simp_rw [hAB] at hleft ⊢
      exact tendsto_nhds_unique hleft hright }

/-- The base coordinate of the multiplier is the ordinary pointwise product. -/
theorem testMultiplier_base_ae (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (U : W^{k,p}(ℝ^n)) :
    baseRepresentative (testMultiplier ψ U) =ᵐ[domainMeasure n univ]
      fun x ↦ ψ.toFun x * baseRepresentative U x := by
  simpa only [testMultiplier, ContinuousLinearMap.coe_mk',
    extendByCutoffLinearMap_apply] using
    extendByCutoff_base_ae isOpen_univ Subset.rfl ψ (subset_univ _) U

/-- A prescribed interior cutoff times the smoothing error can be made arbitrarily small in
the full Sobolev graph norm. Only openness of the domain is required. -/
theorem exists_localized_smooth_error {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (hp : p ≠ ∞) (U : W^{k,p}(Ω))
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hψ : tsupport ψ.toFun ⊆ Ω)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : ℝ^n → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      ∃ E : W^{k,p}(Ω),
        baseRepresentative E =ᵐ[domainMeasure n Ω]
          (fun x ↦ ψ.toFun x * (v x - baseRepresentative U x)) ∧ ‖E‖ < δ := by
  obtain ⟨χ, hχ, hχone, _, _⟩ :=
    TestFunction.exists_eq_one_on_compact hΩ ψ.hasCompactSupport hψ
  let W := extendByCutoff hΩ (subset_univ Ω) χ hχ U
  obtain ⟨v, hv, hvc, ht⟩ :=
    globalApproximation_WkpSpace (standardMollifier n) hp k W
  let R := restrictCLM (n := n) (k := k) (p := p) hΩ.measurableSet (subset_univ Ω)
  let A := R.comp (testMultiplier (k := k) (p := p) ψ)
  let V (m : ℕ) := mkWkpSpaceOnOfContDiff (k := k) (p := p) (Ω := univ)
    (v m) (hv m) (hvc m)
  have hV : Filter.Tendsto (fun m ↦ V m - W) Filter.atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr ht
  have hE : Filter.Tendsto (fun m ↦ ‖A (V m - W)‖) Filter.atTop (𝓝 0) := by
    simpa only [map_zero, norm_zero, Function.comp_apply] using
      (A.continuous.continuousAt.tendsto.comp hV).norm
  obtain ⟨m, hm⟩ := (hE.eventually (gt_mem_nhds hδ)).exists
  refine ⟨v m, hv m, A (V m - W), ?_, hm⟩
  have hVbase : baseRepresentative (V m) =ᵐ[domainMeasure n univ] v m := by
    simpa only [V, baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (v m) (hv m) (hvc m) (baseIndex n k)
  have hWbase := extendByCutoff_base_ae hΩ (subset_univ Ω) χ hχ U
  have hprod := testMultiplier_base_ae ψ (V m - W)
  have hsub := baseRepresentative_sub_ae (V m) W
  have hrestrict := restrictCLM_apply_ae hΩ.measurableSet (subset_univ Ω)
    (testMultiplier ψ (V m - W)) (baseIndex n k)
  have hle : domainMeasure n Ω ≤ domainMeasure n univ := by
    simp only [domainMeasure, Measure.restrict_univ]
    exact Measure.restrict_le_self
  filter_upwards [hrestrict, hprod.filter_mono (ae_mono hle),
    hsub.filter_mono (ae_mono hle), hVbase.filter_mono (ae_mono hle),
    hWbase.filter_mono (ae_mono hle)] with x hr hp hs hvx hw
  change baseRepresentative (A (V m - W)) x =
    baseRepresentative (testMultiplier ψ (V m - W)) x at hr
  change baseRepresentative W x = χ.toFun x * baseRepresentative U x at hw
  rw [hr, hp, hs, hvx, hw]
  by_cases hx : ψ.toFun x = 0
  · simp [hx]
  · rw [hχone x (subset_tsupport ψ.toFun hx), one_mul]

end SobolevSpace.Approximation.OpenDomain
