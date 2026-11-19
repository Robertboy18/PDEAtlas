/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Domain.CriticalStepEstimate

/-!
# Quantitative critical higher-order estimates

When `jp = n`, the first `j-1` Sobolev steps reach `W^{1,n}`. Their
constants and the finite-exponent critical estimate bound the
higher-order inclusion. Only first-order operational extensions are used.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace.Inequalities

open GraphSpace GraphSpace.Embedding

variable {n j : ℕ} {p q : NNReal} {Ω : Set (ℝ^n)}

/-- Removing the last critical derivative leaves a strictly subcritical order. -/
theorem pred_subcritical_of_critical (hp : 1 ≤ p) (hj : 0 < j)
    (hcrit : (j : ℝ) * p = n) : ((j - 1 : ℕ) : ℝ) * p < n := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  rw [Nat.cast_sub (by omega : 1 ≤ j), Nat.cast_one]
  nlinarith

variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- The critical constant is the product of the last finite-exponent estimate
and the quantitative subcritical chain reaching `W^{1,n}`. -/
def criticalDomainConstant (j : ℕ) (p q : NNReal) (hp : 1 ≤ p) (hj : 0 < j)
    (hcrit : (j : ℝ) * p = n) : ℝ :=
  criticalFirstOrderConstant (Ω := Ω) q * (Fintype.card (DerivIndex n 1) : ℝ) *
    domainIterationConstant (Ω := Ω) (j - 1) p hp (pred_subcritical_of_critical hp hj hcrit)

/-- The higher-order critical constant is nonnegative. -/
theorem criticalDomainConstant_nonneg (hp : 1 ≤ p) (hj : 0 < j)
    (hcrit : (j : ℝ) * p = n) :
    0 ≤ criticalDomainConstant (Ω := Ω) j p q hp hj hcrit :=
  mul_nonneg (mul_nonneg criticalFirstOrderConstant_nonneg (Nat.cast_nonneg _))
    (domainIterationConstant_nonneg _ _)

/-- The reduction to `W^{1,n}` satisfies the bound obtained
from the `j-1` subcritical Sobolev steps. -/
theorem norm_toCriticalFirstOrder_le
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (n : ℝ≥0∞))]
    (hp : 1 ≤ p) (hj : 0 < j) (hcrit : (j : ℝ) * p = n)
    (U : W^{j,(p : ℝ≥0∞)}(Ω)) :
    ‖toCriticalFirstOrder hp hj hcrit U‖ ≤
      (Fintype.card (DerivIndex n 1) : ℝ) *
        domainIterationConstant (Ω := Ω) (j - 1) p hp
          (pred_subcritical_of_critical hp hj hcrit) * ‖U‖ := by
  have hpred := pred_subcritical_of_critical hp hj hcrit
  have hexp : higherOrderExponent n (j - 1) p = (n : NNReal) :=
    higherOrderExponent_pred_eq_dimension hj
      (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)) hcrit
  have hexp' : (higherOrderExponent n (j - 1) p : ℝ≥0∞) = (n : ℝ≥0∞) := by
    exact_mod_cast hexp
  have : Fact (1 ≤ (higherOrderExponent n (j - 1) p : ℝ≥0∞)) :=
    ⟨by rw [hexp']; exact Fact.out⟩
  let V := lowerOrderCLM (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)
    (show 1 + (j - 1) ≤ j by omega) U
  let W := iteratedStepCLM (k := 1) hp hpred V
  let Z := WkpSpaceOn.congrExponent hexp' n 1 Ω W
  have hZU : baseRepresentative Z =ᵐ[domainMeasure n Ω] baseRepresentative U := by
    have hZW : baseRepresentative Z = baseRepresentative W :=
      WkpSpaceOn.coordinate_congrExponent hexp' W (baseIndex n 1)
    rw [hZW]
    simpa [W, V, baseRepresentative] using iteratedStepCLM_apply_ae hp hpred V (baseIndex n 1)
  have hZ : toCriticalFirstOrder hp hj hcrit U = Z := by
    apply wkpBaseCoordinateCLM_injective Boundary.C1ExtensionAtlas.isOpen
    apply Lp.ext
    exact (toCriticalFirstOrder_base_ae hp hj hcrit U).trans hZU.symm
  rw [hZ, WkpSpaceOn.norm_congrExponent]
  exact (norm_iteratedStepCLM_le_domainIterationConstant hp hpred V).trans
    (mul_le_mul_of_nonneg_left (norm_lowerOrderCLM_apply_le _ U)
      (mul_nonneg (Nat.cast_nonneg _) (domainIterationConstant_nonneg hp hpred)))

/-- The critical higher-order base function belongs to every finite `L^q`,
with constants tracked through first-order estimates. -/
theorem eLpNorm_base_le_criticalDomainConstant
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 ≤ p) (hj : 0 < j) (hcrit : (j : ℝ) * p = n) (hq : 1 ≤ q)
    (U : W^{j,(p : ℝ≥0∞)}(Ω)) :
    eLpNorm (baseRepresentative U) (q : ℝ≥0∞) (domainMeasure n Ω) ≤
      ENNReal.ofReal (criticalDomainConstant (Ω := Ω) j p q hp hj hcrit * ‖U‖) := by
  have : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast Fact.out (p := 0 < n)⟩
  have h := eLpNorm_critical_firstOrder_le hq (toCriticalFirstOrder hp hj hcrit U)
  have hVU : baseRepresentative (toCriticalFirstOrder hp hj hcrit U)
      =ᵐ[domainMeasure n Ω] baseRepresentative U :=
    toCriticalFirstOrder_base_ae hp hj hcrit U
  rw [eLpNorm_congr_ae hVU] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  simpa [criticalDomainConstant, mul_assoc] using
    mul_le_mul_of_nonneg_left (norm_toCriticalFirstOrder_le hp hj hcrit U)
      (criticalFirstOrderConstant_nonneg (Ω := Ω) (q := q))

/-- The closed-graph base inclusion has an explicit analytic bound
in the critical case; its unknown operator norm is not used as a constant. -/
theorem opNorm_criticalBaseEmbedding_le
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (q : ℝ≥0∞))]
    [Fact (1 ≤ (n : ℝ≥0∞))]
    (hp : 1 ≤ p) (hj : 0 < j) (hcrit : (j : ℝ) * p = n) (hq : 1 ≤ q) :
    ‖embeddingCLMOfMemLp
        (memLp_critical_finite_of_c1ExtensionAtlas (Ω := Ω) hp hj hcrit hq)‖ ≤
      criticalDomainConstant (Ω := Ω) j p q hp hj hcrit := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (criticalDomainConstant_nonneg hp hj hcrit) fun U ↦ ?_
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNorm_base_le_criticalDomainConstant hp hj hcrit hq U)
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (criticalDomainConstant_nonneg hp hj hcrit) (norm_nonneg U))] at h
  exact h

end SobolevSpace.Inequalities
