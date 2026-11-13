/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Domain.CriticalIterationEstimate
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Bounded critical higher-order domain inclusions

The critical inclusion `W^{k+j,p}(Ω) → W^{k,q}(Ω)`, for `jp = n` and finite
`q ≥ 1`, preserves every retained weak derivative. Its operator norm is bounded
by the critical base constant and the number of retained coordinates.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.Embedding

open MeasureTheory Inequalities
open scoped ENNReal Sobolev

variable {n j k : ℕ} {p q : NNReal} {Ω : Set (ℝ^n)}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]
variable [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]

/-- The critical higher-order domain inclusion for every finite target exponent.
Only the operational first-order extension atlas is required. -/
def criticalIterationCLM (hp : 1 ≤ p) (hj : 0 < j)
    (hcrit : (j : ℝ) * p = n) (hq : 1 ≤ q) :
    W^{k + j,(p : ℝ≥0∞)}(Ω) →L[ℝ] W^{k,(q : ℝ≥0∞)}(Ω) := by
  have : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast Fact.out (p := 0 < n)⟩
  let B := embeddingCLMOfMemLp
    (memLp_critical_finite_of_c1ExtensionAtlas (Ω := Ω) hp hj hcrit hq)
  let A : W^{k + j,(p : ℝ≥0∞)}(Ω) →L[ℝ] WkpAmbientOn n k (q : ℝ≥0∞) Ω :=
    (PiLp.continuousLinearEquiv _ ℝ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun a : DerivIndex n k ↦
        B.comp (derivativeWordCLM a.toList (Nat.add_le_add_right a.toList_length_le j)))
  refine A.codRestrict (wkpSubmoduleOn n k _ Ω) fun U ↦ ?_
  let d (a : DerivIndex n k) : ℝ^n → ℝ :=
    U.val (a.castOrder (Nat.le_add_right k j))
  have hm (a : DerivIndex n k) : MemLp (d a) (q : ℝ≥0∞) (domainMeasure n Ω) := by
    simpa [d, baseRepresentative] using
      memLp_critical_finite_of_c1ExtensionAtlas hp hj hcrit hq
        (derivativeWordCLM a.toList (Nat.add_le_add_right a.toList_length_le j) U)
  have hw (a : DerivIndex n k) :
      HasWeakDerivativeOn Ω a.toList (d (baseIndex n k)) (d a) := by
    simpa [d] using U.property (a.castOrder (Nat.le_add_right k j))
  let J := mkWkpSpaceOnOfWeakDerivatives (d (baseIndex n k)) d rfl hm hw
  have hA : A U = J.val := by
    apply PiLp.ext
    intro a
    apply Lp.ext
    change baseRepresentative (derivativeWordCLM a.toList
      (Nat.add_le_add_right a.toList_length_le j) U) =ᵐ[domainMeasure n Ω]
        (J.val a : ℝ^n → ℝ)
    simpa [d, J, baseRepresentative] using
      (mkWkpSpaceOnOfWeakDerivatives_apply_ae (d (baseIndex n k)) d rfl hm hw a).symm
  rw [hA]
  exact J.property

/-- All derivatives through the retained order agree almost everywhere with the source. -/
theorem criticalIterationCLM_apply_ae (hp : 1 ≤ p) (hj : 0 < j)
    (hcrit : (j : ℝ) * p = n) (hq : 1 ≤ q)
    (U : W^{k + j,(p : ℝ≥0∞)}(Ω)) (a : DerivIndex n k) :
    ((criticalIterationCLM hp hj hcrit hq U).val a : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (U.val (a.castOrder (Nat.le_add_right k j)) : ℝ^n → ℝ) := by
  change baseRepresentative (derivativeWordCLM a.toList
    (Nat.add_le_add_right a.toList_length_le j) U) =ᵐ[domainMeasure n Ω] _
  simp [baseRepresentative]

/-- Quantitative critical inclusion, with no desired embedding norm among the constants. -/
theorem norm_criticalIterationCLM_le (hp : 1 ≤ p) (hj : 0 < j)
    (hcrit : (j : ℝ) * p = n) (hq : 1 ≤ q)
    (U : W^{k + j,(p : ℝ≥0∞)}(Ω)) :
    ‖criticalIterationCLM hp hj hcrit hq U‖ ≤ (Fintype.card (DerivIndex n k) : ℝ) *
      criticalDomainConstant (Ω := Ω) j p q hp hj hcrit * ‖U‖ := by
  have : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast Fact.out (p := 0 < n)⟩
  let B := embeddingCLMOfMemLp
    (memLp_critical_finite_of_c1ExtensionAtlas (Ω := Ω) hp hj hcrit hq)
  have hcoord (a : DerivIndex n k) :
      ‖(criticalIterationCLM hp hj hcrit hq U).val a‖ ≤
        criticalDomainConstant (Ω := Ω) j p q hp hj hcrit * ‖U‖ := by
    change ‖B (derivativeWordCLM a.toList
      (Nat.add_le_add_right a.toList_length_le j) U)‖ ≤ _
    exact (B.le_opNorm _).trans (mul_le_mul
      (opNorm_criticalBaseEmbedding_le hp hj hcrit hq)
      (norm_derivativeWordCLM_apply_le _ _ U) (norm_nonneg _)
      (criticalDomainConstant_nonneg hp hj hcrit))
  apply (PiLp.norm_le_sum_norm (criticalIterationCLM hp hj hcrit hq U).val).trans
  calc
    ∑ a : DerivIndex n k, ‖(criticalIterationCLM hp hj hcrit hq U).val a‖ ≤
        ∑ _a : DerivIndex n k, criticalDomainConstant (Ω := Ω) j p q hp hj hcrit * ‖U‖ :=
      Finset.sum_le_sum fun a _ ↦ hcoord a
    _ = _ := by simp [mul_assoc]

/-- Operator-norm estimate for the full critical derivative bundle. -/
theorem opNorm_criticalIterationCLM_le (hp : 1 ≤ p) (hj : 0 < j)
    (hcrit : (j : ℝ) * p = n) (hq : 1 ≤ q) :
    ‖criticalIterationCLM (k := k) (Ω := Ω) hp hj hcrit hq‖ ≤
      (Fintype.card (DerivIndex n k) : ℝ) *
        criticalDomainConstant (Ω := Ω) j p q hp hj hcrit :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg _) (criticalDomainConstant_nonneg hp hj hcrit))
    (norm_criticalIterationCLM_le hp hj hcrit hq)

/-- The critical inclusion is injective on the open atlas domain. -/
theorem criticalIterationCLM_injective (hp : 1 ≤ p) (hj : 0 < j)
    (hcrit : (j : ℝ) * p = n) (hq : 1 ≤ q) :
    Function.Injective (criticalIterationCLM (k := k) (Ω := Ω) hp hj hcrit hq) := by
  intro U V h
  apply wkpBaseCoordinateCLM_injective Boundary.C1ExtensionAtlas.isOpen
  apply Lp.ext
  have hU := criticalIterationCLM_apply_ae hp hj hcrit hq U (baseIndex n k)
  have hV := criticalIterationCLM_apply_ae hp hj hcrit hq V (baseIndex n k)
  rw [h] at hU
  exact hU.symm.trans hV

end SobolevSpace.GraphSpace.Embedding
