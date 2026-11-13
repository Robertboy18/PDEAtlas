/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.BochnerConsistency
import PDE.Analysis.WeakCompactness

/-!
# Local weak derivatives from bounded mollified rows

A uniform L² bound on localized mollified derivative rows gives a weak
derivative wherever the multiplier is one. Weak compactness supplies the row;
strong convergence of the mollified base identifies its distributional derivative.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Topology

namespace SobolevSpace.Approximation

open GraphSpace PDE.Analysis

variable {n : ℕ}

private theorem lpPairing_toLpOfContCompact_eq_integral
    (u : DerivLp n 2 univ) (φ : ℝ^n → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n univ) 2 2).flip
      (toLpOfContCompact φ hφ hφc) u =
        ∫ x, u x * φ x ∂domainMeasure n univ := by
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  filter_upwards [toLpOfContCompact_coeFn (p := 2) (Ω := univ) hφ hφc] with x hx
  rw [hx]

/-- A bounded localized derivative of the mollifications produces an L²
weak derivative on the region where the multiplier equals one. The norm bound
passes to the weak limit, with no differentiability premise on the input. -/
theorem exists_L2_weakDerivativeOn_of_bounded_mollifierDerivativeRowCLM
    (μ : Mollifier n) (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) (j : Fin n)
    (u : DerivLp n 2 univ) (b : DerivLp n ∞ univ) (V : Set (ℝ^n))
    (hb : ∀ᵐ x ∂domainMeasure n univ, x ∈ V → b x = 1) (C : ℝ)
    (hbound : ∀ k, ‖b • mollifierDerivativeRowCLM μ (hε k) j u‖ ≤ C) :
    ∃ v : DerivLp n 2 univ, ‖v‖ ≤ C ∧ HasWeakDerivativeOn V [j] u v := by
  let s := fun k ↦ b • mollifierDerivativeRowCLM μ (hε k) j u
  have hsbounded : Bornology.IsBounded (range s) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * C, fun k l ↦ ?_⟩
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hbound k, hbound l])
  obtain ⟨vw, F, hF, hweak⟩ :=
    WeakCompactness.exists_ultrafilter_tendsto_of_isBounded_range_filter atTop s hsbounded
  let v : DerivLp n 2 univ := (toWeakSpace ℝ (DerivLp n 2 univ)).symm vw
  refine ⟨v, ?_, ?_⟩
  · exact WeakCompactness.norm_le_of_tendsto_of_norm_le hweak (Eventually.of_forall hbound)
  refine ⟨(memLp_locallyIntegrableOn_domain (Lp.memLp u) (by norm_num)).mono_set
    (subset_univ V), (memLp_locallyIntegrableOn_domain (Lp.memLp v)
      (by norm_num)).mono_set (subset_univ V), ?_⟩
  intro φ hφV
  let φ₀ : DerivLp n 2 univ := toLpOfContCompact φ.toFun φ.continuous φ.hasCompactSupport
  have hφ₁ : Continuous (∂[j] φ.toFun) :=
    (PDE.contDiff_top_iteratedPartialDeriv φ.contDiff [j]).continuous
  have hφ₁c : HasCompactSupport (∂[j] φ.toFun) :=
    hasCompactSupport_iteratedPartialDeriv φ.hasCompactSupport [j]
  let φ₁ : DerivLp n 2 univ := toLpOfContCompact (∂[j] φ.toFun) hφ₁ hφ₁c
  let P := (ContinuousLinearMap.mul ℝ ℝ).lpPairing (domainMeasure n univ) 2 2
  have hidentity (k : ℕ) : P.flip φ₁ (mollifierRowCLM μ (hε k) u) = -P.flip φ₀ (s k) := by
    have hw := (mollifierH1CLM μ (hε k) u).property.hasWeakDerivativeOn_list [j] (by simp)
    change HasWeakDerivativeOn univ [j]
      (wkpCoordinateCLM (baseIndex n 1) (mollifierH1CLM μ (hε k) u))
      (wkpCoordinateCLM (singleDerivIndex n j) (mollifierH1CLM μ (hε k) u)) at hw
    rw [mollifierH1CLM_base, mollifierH1CLM_derivative] at hw
    have hid := hw φ (subset_univ _)
    simp only [List.length_singleton, pow_one, neg_mul, one_mul, iteratedPartialDeriv] at hid
    dsimp only [P, φ₀, φ₁]
    rw [lpPairing_toLpOfContCompact_eq_integral, lpPairing_toLpOfContCompact_eq_integral]
    rw [hid]
    congr 1
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_lpSMul (r := 2) b (mollifierDerivativeRowCLM μ (hε k) j u), hb]
      with x hx hb
    change _ = (s k) x * φ x
    rw [hx]
    simp only [Pi.smul_apply', smul_eq_mul]
    change (mollifierDerivativeRowCLM μ (hε k) j u) x * φ.toFun x =
      (b x * (mollifierDerivativeRowCLM μ (hε k) j u) x) * φ.toFun x
    by_cases hzero : φ.toFun x = 0
    · simp only [hzero, mul_zero]
    · have hxV : x ∈ V := hφV (subset_tsupport _ hzero)
      rw [hb hxV, one_mul]
  have hstrong := (P.flip φ₁).continuous.continuousAt.tendsto.comp
    ((tendsto_mollifierRowCLM μ ε hε hε0 u).mono_left hF)
  have hlimit := WeakCompactness.tendsto_evaluation hweak (P.flip φ₀)
  have hlimit' : Tendsto (fun k ↦ P.flip φ₁ (mollifierRowCLM μ (hε k) u)) F
      (𝓝 (-P.flip φ₀ v)) := by
    have h := hlimit.neg
    simpa only [LinearEquiv.symm_apply_apply] using
      h.congr' (Eventually.of_forall fun k ↦ (hidentity k).symm)
  have heq := tendsto_nhds_unique hstrong hlimit'
  dsimp only [P, φ₀, φ₁] at heq
  rw [lpPairing_toLpOfContCompact_eq_integral, lpPairing_toLpOfContCompact_eq_integral] at heq
  have hleft : ∀ x ∉ V, u x * (∂[j] φ.toFun) x = 0 := by
    intro x hx
    have hz : (∂[j] φ.toFun) x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hx (hφV (tsupport_iteratedPartialDeriv_subset_tsupport [j] φ.toFun h)))
    rw [hz, mul_zero]
  have hright : ∀ x ∉ V, v x * φ.toFun x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφV h)), mul_zero]
  simp only [List.length_singleton, pow_one, neg_mul, one_mul, iteratedPartialDeriv,
    domainMeasure, Measure.restrict_univ] at heq ⊢
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hleft,
    setIntegral_eq_integral_of_forall_compl_eq_zero hright]
  exact heq

end SobolevSpace.Approximation
