/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Domain.StepEstimate
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Bounded higher-order inclusions on bounded operational C¹ domains

The map `iteratedStepCLM` realizes `W^{k+j,p}(Ω) → W^{k,np/(n-jp)}(Ω)` for
`jp < n`. Each target coordinate is obtained by applying the base
inclusion to a contractive derivative slice. The weak-derivative identities
are those of `iteratedStep`.

Only the first-order extension atlas is needed, regardless of the source
order. This atlas includes boundedness and openness of the domain. The one-step
estimate retains the GNS constant and the extension norm.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.Embedding

open MeasureTheory Inequalities
open scoped ENNReal Sobolev

variable {n j k : ℕ} {p : NNReal} {Ω : Set (ℝ^n)}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]
variable [Fact (1 ≤ (p : ℝ≥0∞))]

/-- The operational higher-order Sobolev inclusion as a bounded linear map.
It retains all derivatives of order at most `k` and consumes `j` derivatives
to reach the exact exponent `np/(n-jp)`. -/
def iteratedStepCLM (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n)
    [Fact (1 ≤ (higherOrderExponent n j p : ℝ≥0∞))] :
    W^{k + j,(p : ℝ≥0∞)}(Ω) →L[ℝ]
      W^{k,(higherOrderExponent n j p : ℝ≥0∞)}(Ω) := by
  let B := embeddingCLMOfMemLp (base_memLp_iterated (Ω := Ω) hp hsub)
  let A : W^{k + j,(p : ℝ≥0∞)}(Ω) →L[ℝ]
      WkpAmbientOn n k (higherOrderExponent n j p : ℝ≥0∞) Ω :=
    (PiLp.continuousLinearEquiv _ ℝ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun a : DerivIndex n k ↦
        B.comp (derivativeWordCLM a.toList (Nat.add_le_add_right a.toList_length_le j)))
  refine A.codRestrict (wkpSubmoduleOn n k _ Ω) fun U ↦ ?_
  have hA : A U = (iteratedStep hp hsub U).val := by
    apply PiLp.ext
    intro a
    apply Lp.ext
    change baseRepresentative (derivativeWordCLM a.toList
      (Nat.add_le_add_right a.toList_length_le j) U) =ᵐ[domainMeasure n Ω]
        ((iteratedStep hp hsub U).val a : ℝ^n → ℝ)
    simpa [baseRepresentative] using (iteratedStep_apply_ae hp hsub U a).symm
  rw [hA]
  exact (iteratedStep hp hsub U).property

/-- The bounded inclusion is the derivative bundle. -/
theorem iteratedStepCLM_apply (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n)
    [Fact (1 ≤ (higherOrderExponent n j p : ℝ≥0∞))]
    (U : W^{k + j,(p : ℝ≥0∞)}(Ω)) :
    iteratedStepCLM hp hsub U = iteratedStep hp hsub U := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  change baseRepresentative (derivativeWordCLM a.toList
    (Nat.add_le_add_right a.toList_length_le j) U) =ᵐ[domainMeasure n Ω]
      ((iteratedStep hp hsub U).val a : ℝ^n → ℝ)
  simpa [baseRepresentative] using (iteratedStep_apply_ae hp hsub U a).symm

/-- Every retained coordinate agrees almost everywhere with the original
weak derivative, even though its integrability exponent has changed. -/
theorem iteratedStepCLM_apply_ae (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n)
    [Fact (1 ≤ (higherOrderExponent n j p : ℝ≥0∞))]
    (U : W^{k + j,(p : ℝ≥0∞)}(Ω)) (a : DerivIndex n k) :
    ((iteratedStepCLM hp hsub U).val a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (U.val (a.castOrder (Nat.le_add_right k j)) : ℝ^n → ℝ) := by
  rw [iteratedStepCLM_apply]
  exact iteratedStep_apply_ae hp hsub U a

/-- The higher-order map is injective: on the open atlas domain, the base
function uniquely determines all weak derivatives. -/
theorem iteratedStepCLM_injective (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n)
    [Fact (1 ≤ (higherOrderExponent n j p : ℝ≥0∞))] :
    Function.Injective (iteratedStepCLM (k := k) (Ω := Ω) hp hsub) := by
  intro U V h
  apply wkpBaseCoordinateCLM_injective
    (Boundary.C1ExtensionAtlas.isOpen (n := n) (Ω := Ω))
  apply Lp.ext
  have hU := iteratedStepCLM_apply_ae hp hsub U (baseIndex n k)
  have hV := iteratedStepCLM_apply_ae hp hsub V (baseIndex n k)
  rw [h] at hU
  exact hU.symm.trans hV

/-- Passing from the base inclusion to the full retained derivative bundle
costs at most the number of retained coordinates. -/
theorem norm_iteratedStepCLM_le (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n)
    [Fact (1 ≤ (higherOrderExponent n j p : ℝ≥0∞))]
    (U : W^{k + j,(p : ℝ≥0∞)}(Ω)) :
    ‖iteratedStepCLM hp hsub U‖ ≤ (Fintype.card (DerivIndex n k) : ℝ) *
      ‖embeddingCLMOfMemLp (base_memLp_iterated (Ω := Ω) hp hsub)‖ * ‖U‖ := by
  let B := embeddingCLMOfMemLp (base_memLp_iterated (Ω := Ω) hp hsub)
  apply (PiLp.norm_le_sum_norm (iteratedStepCLM hp hsub U).val).trans
  have hcoord (a : DerivIndex n k) :
      ‖(iteratedStepCLM hp hsub U).val a‖ ≤ ‖B‖ * ‖U‖ := by
    change ‖B (derivativeWordCLM a.toList
      (Nat.add_le_add_right a.toList_length_le j) U)‖ ≤ _
    exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      (norm_derivativeWordCLM_apply_le _ _ U) (norm_nonneg B))
  calc
    ∑ a : DerivIndex n k, ‖(iteratedStepCLM hp hsub U).val a‖ ≤
        ∑ _a : DerivIndex n k, ‖B‖ * ‖U‖ :=
      Finset.sum_le_sum fun a _ ↦ hcoord a
    _ = _ := by simp [B, mul_assoc]

/-- For one consumed derivative the bound uses the explicit GNS constant
and the operational extension norm, for arbitrary retained order `k`. -/
theorem norm_iteratedStepCLM_one_le (hp : 1 ≤ p) (hsub : (p : ℝ) < n)
    [Fact (1 ≤ (higherOrderExponent n 1 p : ℝ≥0∞))]
    (U : W^{k + 1,(p : ℝ≥0∞)}(Ω)) :
    ‖iteratedStepCLM (j := 1) hp (by simpa using hsub) U‖ ≤
      (Fintype.card (DerivIndex n k) : ℝ) *
        firstOrderDomainConstant (p := p) (Ω := Ω) * ‖U‖ := by
  have h :
      iteratedStepCLM (j := 1) hp (by simpa using hsub) U =
        firstOrderStep hp hsub U := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    apply Lp.ext
    exact (iteratedStepCLM_apply_ae hp (by simpa using hsub) U a).trans
      (firstOrderStep_apply_ae hp hsub U a).symm
  rw [h]
  exact norm_firstOrderStep_le hp hsub U

end SobolevSpace.GraphSpace.Embedding
