/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.ContinuousEmbedding
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.LebesgueEmbedding
public import PDE.Spaces.Sobolev.Approximation.Density.SmoothFields
public import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Hilbert Sobolev spaces inside `W^{k,∞}` and `W^{k,4}` in three dimensions

An element of `H³(ℝ³)` lies in every `Lᵠ`, `2 ≤ q ≤ ∞`
(`memLp_baseRepresentative_three`, from the Lebesgue embedding of the Hilbert Sobolev
spaces). Applied to the derivatives of order at most `k`, this gives the bounded inclusions
`hilbertEmbeddingCLM` of `H^{k+3}(ℝ³)` into `W^{k,q}(ℝ³)` for `q = ∞` and `q = 4`, and
their vector forms. On smooth functions the inclusion is the identity
(`hilbertEmbeddingCLM_wkpOfContDiff`).
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

set_option linter.missingDocs true

/-- An element of `H³(ℝ³)` lies in every `Lᵠ`, `2 ≤ q ≤ ∞`. -/
theorem memLp_baseRepresentative_three (U : W^{3,2}(ℝ^3)) {q : ℝ≥0∞} (hq : 2 ≤ q) :
    MemLp (baseRepresentative U) q (domainMeasure 3 univ) := by
  have h := ((exists_eLpNorm_baseRepresentative_le_of_dimension_lt (n := 3) (k := 3)
    (by norm_num)).choose_spec.2 U hq).1
  simpa only [domainMeasure, Measure.restrict_univ] using h

/-- An element of `H³(ℝ³)` is essentially bounded. -/
theorem memLp_top_baseRepresentative_three (U : W^{3,2}(ℝ^3)) :
    MemLp (baseRepresentative U) ∞ (domainMeasure 3 univ) :=
  memLp_baseRepresentative_three U le_top

/-- An element of `H³(ℝ³)` lies in `L⁴`. -/
theorem memLp_four_baseRepresentative_three (U : W^{3,2}(ℝ^3)) :
    MemLp (baseRepresentative U) 4 (domainMeasure 3 univ) :=
  memLp_baseRepresentative_three U (by norm_num)

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The base coordinate of a derivative word of order at most `k` of an element of `H^{k+3}`,
as an element of `Lᵠ`. -/
def hilbertCoordinateCLM (k : ℕ)
    (hq : ∀ U : W^{3,2}(ℝ^3), MemLp (baseRepresentative U) q (domainMeasure 3 univ))
    (a : DerivIndex 3 k) : W^{k + 3,2}(ℝ^3) →L[ℝ] DerivLp 3 q univ :=
  (SobolevSpace.Inequalities.embeddingCLMOfMemLp (n := 3) (k := 3) (p := 2) (Ω := univ) hq).comp
    (derivativeWordCLM a.toList (by have := a.toList_length_le; omega))

/-- The coordinate is the base representative of the derivative word. -/
theorem coeFn_hilbertCoordinateCLM (k : ℕ)
    (hq : ∀ U : W^{3,2}(ℝ^3), MemLp (baseRepresentative U) q (domainMeasure 3 univ))
    (a : DerivIndex 3 k) (U : W^{k + 3,2}(ℝ^3)) :
    (hilbertCoordinateCLM k hq a U : ℝ^3 → ℝ) =
      baseRepresentative (derivativeWordCLM (r := 3) a.toList
        (by have := a.toList_length_le; omega) U) :=
  rfl

/-- **The inclusion `H^{k+3}(ℝ³) ⊂ W^{k,q}(ℝ³)`** for an exponent `q` with `H³(ℝ³) ⊂ Lᵠ`. -/
def hilbertEmbeddingCLM (k : ℕ)
    (hq : ∀ U : W^{3,2}(ℝ^3), MemLp (baseRepresentative U) q (domainMeasure 3 univ)) :
    W^{k + 3,2}(ℝ^3) →L[ℝ] W^{k,q}(ℝ^3) :=
  ((PiLp.continuousLinearEquiv q ℝ
      (fun _ : DerivIndex 3 k ↦ DerivLp 3 q univ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦ hilbertCoordinateCLM k hq a)).codRestrict
    (wkpSubmoduleOn 3 k q univ) fun U a ↦ by
      have hbase : ∀ (l : List (Fin 3)) (h : l.length + 3 ≤ k + 3), l = [] →
          baseRepresentative (derivativeWordCLM (r := 3) l h U) = baseRepresentative U := by
        intro l h hl
        subst hl
        rw [derivativeWordCLM_nil_apply, baseRepresentative_lowerOrderCLM]
      have hw := U.property.hasWeakDerivativeOn_list a.toList (by
        have := a.toList_length_le; omega)
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.pi_apply, PiLp.toLp_apply]
      rw [coeFn_hilbertCoordinateCLM, coeFn_hilbertCoordinateCLM,
        hbase _ _ (by simp), baseRepresentative_derivativeWordCLM]
      exact hw

/-- The base representative of the inclusion is the base representative of the element. -/
theorem baseRepresentative_hilbertEmbeddingCLM (k : ℕ)
    (hq : ∀ U : W^{3,2}(ℝ^3), MemLp (baseRepresentative U) q (domainMeasure 3 univ))
    (U : W^{k + 3,2}(ℝ^3)) :
    baseRepresentative (hilbertEmbeddingCLM k hq U) = baseRepresentative U := by
  have hbase : ∀ (l : List (Fin 3)) (h : l.length + 3 ≤ k + 3), l = [] →
      baseRepresentative (derivativeWordCLM (r := 3) l h U) = baseRepresentative U := by
    intro l h hl
    subst hl
    rw [derivativeWordCLM_nil_apply, baseRepresentative_lowerOrderCLM]
  change ((hilbertCoordinateCLM k hq (baseIndex 3 k) U : DerivLp 3 q univ) : ℝ^3 → ℝ) = _
  rw [coeFn_hilbertCoordinateCLM, hbase _ _ (by simp)]

/-- On smooth functions the inclusion is the identity. -/
theorem hilbertEmbeddingCLM_wkpOfContDiff (k : ℕ)
    (hq : ∀ U : W^{3,2}(ℝ^3), MemLp (baseRepresentative U) q (domainMeasure 3 univ))
    {f : ℝ^3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (h₂ : ∀ m ≤ k + 3, MemLp (iteratedFDeriv ℝ m f) 2 volume)
    (h₃ : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m f) q volume) :
    hilbertEmbeddingCLM k hq (wkpOfContDiff f hf h₂) = wkpOfContDiff f hf h₃ := by
  refine WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  change baseRepresentative _ =ᵐ[domainMeasure 3 univ] baseRepresentative _
  rw [baseRepresentative_hilbertEmbeddingCLM]
  simp only [domainMeasure, Measure.restrict_univ]
  exact (baseRepresentative_wkpOfContDiff f hf h₂).trans
    (baseRepresentative_wkpOfContDiff f hf h₃).symm

/-- The inclusion of vector `H^{k+3}(ℝ³)` into `W^{k,q}(ℝ³)` component by component. -/
def vectorHilbertEmbeddingCLM (k : ℕ)
    (hq : ∀ U : W^{3,2}(ℝ^3), MemLp (baseRepresentative U) q (domainMeasure 3 univ)) :
    VectorH 3 (k + 3) →L[ℝ] (Fin 3 → W^{k,q}(ℝ^3)) :=
  ContinuousLinearMap.pi fun j ↦ (hilbertEmbeddingCLM k hq).comp (PiLp.proj 2 _ j)

/-- On smooth vector fields the vector inclusion is the identity. -/
theorem vectorHilbertEmbeddingCLM_vectorWkpOfContDiff (k : ℕ)
    (hq : ∀ U : W^{3,2}(ℝ^3), MemLp (baseRepresentative U) q (domainMeasure 3 univ))
    {X : ℝ^3 → ℝ^3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (h₂ : ∀ m ≤ k + 3, MemLp (iteratedFDeriv ℝ m X) 2 volume)
    (h₃ : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m X) q volume) :
    vectorHilbertEmbeddingCLM k hq (WithLp.toLp 2 (vectorWkpOfContDiff X hX h₂)) =
      vectorWkpOfContDiff X hX h₃ := by
  funext j
  simp only [vectorHilbertEmbeddingCLM, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  exact hilbertEmbeddingCLM_wkpOfContDiff k hq _ _ _

end SobolevSpace.GraphSpace
