/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.SpaceTime.TensorTesting
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
import PDE.Spaces.Sobolev.GraphSpace.Operators.WeakAverages
import PDE.Analysis.MeasureTheory.Lp.SectionReconstruction
import PDE.Analysis.MeasureTheory.Lp.Submodule

/-!
# H¹ spatial sections of raw spacetime Sobolev data

Fubini reconstructs a Bochner L² curve of ambient derivative rows. The raw
spacetime weak identities put every smooth time average in the closed
Sobolev graph. The quotient-space fundamental lemma then supplies one common
exceptional set, and the submodule lift gives an L²(H¹) curve.
Neither Sobolev membership nor strong measurability of the slices is assumed.
-/

open PDE (iteratedPartialDeriv)

@[expose] public noncomputable section

namespace SobolevSpace.Slices

open MeasureTheory Set TopologicalSpace PDE.Common GraphSpace
open scoped ENNReal Distributions Sobolev

variable {n : ℕ} {I : Set ℝ}

/-- Raw square-integrable spacetime data with square-integrable weak spatial
derivatives determine Bochner L²(H¹) slices. The spatial domain is the
whole space, with no compactness or bounded-domain assumption. -/
theorem exists_hOne_timeSlices
    (hI : IsOpen I) [IsFiniteMeasure (volume.restrict I)]
    {f : ℝ^(n + 1) → ℝ} {g : Fin n → ℝ^(n + 1) → ℝ}
    (hf : MemLp f 2 (volume.restrict {p | p 0 ∈ I}))
    (hg : ∀ i, MemLp (g i) 2 (volume.restrict {p | p 0 ∈ I}))
    (hweak : ∀ i, HasWeakDerivativeOn {p | p 0 ∈ I} [i.succ] f (g i)) :
    ∃ F : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict I),
      (∀ᵐ t ∂volume.restrict I,
        (wkpBaseCoordinateCLM (F t) : ℝ^n → ℝ) =ᵐ[volume]
          fun x ↦ f (timeSpaceCons t x)) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict I,
        (wkpCoordinateCLM (singleDerivIndex n i) (F t) : ℝ^n → ℝ) =ᵐ[volume]
          fun x ↦ g i (timeSpaceCons t x)) := by
  classical
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let μ := volume.restrict I
  let r : DerivIndex n 1 → ℝ^(n + 1) → ℝ := firstOrderRows f g
  have hr (α : DerivIndex n 1) :
      MemLp (fun p : ℝ × ℝ^n ↦ r α (timeSpaceCons p.1 p.2))
        2 (μ.prod (domainMeasure n univ)) := by
    have hraw : MemLp (r α) 2 (volume.restrict {p | p 0 ∈ I}) := by
      rcases α.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
      · simpa only [r, firstOrderRows_baseIndex] using hf
      · simpa only [r, firstOrderRows_singleDerivIndex] using hg i
    simpa only [Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply,
      domainMeasure, Measure.restrict_univ, μ] using
        hraw.comp_measurePreserving (measurePreserving_timeSpaceCons_restrict I)
  obtain ⟨v, hv⟩ := exists_L2_sections_pi hr
  have hpair (ψ : ℝ → ℝ) (α : DerivIndex n 1) (χ : ℝ^n → ℝ) :
      (∫ t, ψ t * (∫ x, (v t α) x * χ x ∂domainMeasure n univ) ∂μ) =
        ∫ t, ψ t * (∫ x, r α (timeSpaceCons t x) * χ x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv α] with t ht
    congr 1
    simp only [domainMeasure, Measure.restrict_univ] at ht ⊢
    exact integral_congr_ae (ht.symm.mono fun x hx ↦ by
      dsimp only at hx ⊢
      rw [hx])
  have hgraph : ∀ᵐ t ∂μ, IsWkpOn (v t) := by
    have h := ae_isWkpOn_of_test_integrals (Ω := (univ : Set (ℝ^n)))
      hI ((Lp.memLp v).integrable (by norm_num)) ?_
    · filter_upwards [h, ae_restrict_mem hI.measurableSet] with t ht hmem
      exact ht hmem
    · intro ψ hψ hc hs α φ
      rcases α.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
      · simp only [baseIndex_toList, iteratedPartialDeriv, List.length_nil, pow_zero,
          one_mul]
      · rw [hpair, hpair]
        let ψT : 𝓓((⊤ : Opens ℝ), ℝ) :=
          ⟨ψ, hψ, hc, subset_univ _⟩
        have hraw := (hweak i).integral_timeSpaceTensor_spatial i ψT hs φ.1
        simpa only [r, firstOrderRows_baseIndex, firstOrderRows_singleDerivIndex,
          singleDerivIndex_toList, iteratedPartialDeriv, List.length_cons,
          List.length_nil, zero_add, pow_one, neg_one_mul, μ,
          TestFunction.toFun_eq_coe, ψT, TestFunction.coe_mk] using hraw
  obtain ⟨F, hF, _hFnorm⟩ := Lp.exists_submodule (wkpSubmoduleOn n 1 2 univ) v hgraph
  have hFv : ∀ᵐ t ∂μ, (F t).val = v t := by
    have hcomp := (wkpSubmoduleOn n 1 2 univ).subtypeL.coeFn_compLpL F
    rw [hF] at hcomp
    exact hcomp.symm
  refine ⟨F, ?_, ?_⟩
  · filter_upwards [hFv, hv (baseIndex n 1)] with t ht hr
    simp only [r, firstOrderRows_baseIndex, domainMeasure, Measure.restrict_univ] at hr
    simpa only [wkpBaseCoordinateCLM_apply, ht] using hr.symm
  · intro i
    filter_upwards [hFv, hv (singleDerivIndex n i)] with t ht hr
    simp only [r, firstOrderRows_singleDerivIndex, domainMeasure,
      Measure.restrict_univ] at hr
    simpa only [wkpCoordinateCLM_apply, ht] using hr.symm

end SobolevSpace.Slices
