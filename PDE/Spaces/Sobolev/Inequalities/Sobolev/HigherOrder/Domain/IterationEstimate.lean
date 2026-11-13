/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Domain.BoundedEmbedding

/-!
# Constants for iterated domain embeddings

At each step, the Sobolev exponent changes from `p` to `np/(n-p)`. The recursive
constant below multiplies the first-order GNS and extension constants,
including the finite coordinate counts arising from the graph norms, so no
higher-order embedding constant enters.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Inequalities

open MeasureTheory GraphSpace GraphSpace.Embedding
open scoped ENNReal Sobolev

variable {n j : ℕ} {p : NNReal} {Ω : Set (ℝ^n)}

/-- A positive number of subcritical steps starts below the dimension exponent. -/
theorem lt_dimension_of_succ_subcritical
    (hsub : ((j + 1 : ℕ) : ℝ) * p < n) : (p : ℝ) < n := by
  have hp0 : 0 ≤ (p : ℝ) := p.coe_nonneg
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  push_cast at hsub
  nlinarith [mul_nonneg hj0 hp0]

/-- Consuming one derivative leaves exactly the subcritical range for the
remaining `j` derivatives at the new exponent. -/
theorem firstOrderExponent_subcritical (hn : 0 < n)
    (hsub : ((j + 1 : ℕ) : ℝ) * p < n) :
    (j : ℝ) * (higherOrderExponent n 1 p : ℝ) < n := by
  have hpLt := lt_dimension_of_succ_subcritical hsub
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - p := sub_pos.mpr hpLt
  rw [higherOrderExponent_coe (by simpa using hpLt)]
  simp only [Nat.cast_one, one_mul]
  rw [← mul_div_assoc, div_lt_iff₀ hden]
  push_cast at hsub
  nlinarith [mul_lt_mul_of_pos_right hsub hn0]

variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- Product of operational first-order domain constants along the Sobolev
exponent chain. The coordinate counts account for the intermediate graph norms. -/
def domainIterationConstant :
    (j : ℕ) → (p : NNReal) → (hp : 1 ≤ p) → (hsub : (j : ℝ) * p < n) → ℝ
  | 0, _, _, _ => 1
  | j + 1, p, hp, hsub =>
      have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
      have hpLt := lt_dimension_of_succ_subcritical hsub
      domainIterationConstant j (higherOrderExponent n 1 p)
        (one_le_higherOrderExponent hp (by simpa using hpLt))
        (firstOrderExponent_subcritical Fact.out hsub) *
        (Fintype.card (DerivIndex n j) : ℝ) *
        firstOrderDomainConstant (p := p) (Ω := Ω)

/-- All factors in the iterated constant are nonnegative. -/
theorem domainIterationConstant_nonneg (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n) :
    0 ≤ domainIterationConstant (Ω := Ω) j p hp hsub := by
  induction j generalizing p with
  | zero => exact zero_le_one
  | succ j ih =>
      have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
      dsimp only [domainIterationConstant]
      exact mul_nonneg (mul_nonneg (ih _ _) (Nat.cast_nonneg _))
        firstOrderDomainConstant_nonneg

/-- The base function satisfies the exact subcritical domain estimate with
the product of first-order analytic constants. This includes order zero and `p = 1`. -/
theorem eLpNorm_base_le_domainIterationConstant
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n)
    (U : W^{j,(p : ℝ≥0∞)}(Ω)) :
    eLpNorm (baseRepresentative U) (higherOrderExponent n j p : ℝ≥0∞)
        (domainMeasure n Ω) ≤
      ENNReal.ofReal (domainIterationConstant (Ω := Ω) j p hp hsub * ‖U‖) := by
  induction j generalizing p with
  | zero =>
      have h := ENNReal.ofReal_le_ofReal (wkpBaseCoordinateCLM_norm_le U)
      simpa [domainIterationConstant, higherOrderExponent_zero Fact.out, Lp.norm_def,
        ENNReal.ofReal_toReal, Lp.eLpNorm_ne_top, baseRepresentative] using h
  | succ j ih =>
      have hpLt := lt_dimension_of_succ_subcritical hsub
      let q := higherOrderExponent n 1 p
      have hq1 : 1 ≤ q := one_le_higherOrderExponent hp (by simpa using hpLt)
      have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq1⟩
      have hqsub := firstOrderExponent_subcritical Fact.out hsub
      let V := firstOrderStep (k := j) (Ω := Ω) hp hpLt U
      have hVU : baseRepresentative V =ᵐ[domainMeasure n Ω] baseRepresentative U := by
        simpa [V, baseRepresentative] using firstOrderStep_apply_ae hp hpLt U (baseIndex n j)
      have hcomp : higherOrderExponent n j q = higherOrderExponent n (j + 1) p := by
        simpa [q, Nat.add_comm] using higherOrderExponent_add (k := 1) (j := j)
          (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp))
          (by simpa [Nat.add_comm] using hsub)
      have hV := ih hq1 hqsub V
      rw [hcomp, eLpNorm_congr_ae hVU] at hV
      refine hV.trans (ENNReal.ofReal_le_ofReal ?_)
      have hnorm := norm_firstOrderStep_le hp hpLt U
      have hmul := mul_le_mul_of_nonneg_left hnorm
        (domainIterationConstant_nonneg (Ω := Ω) hq1 hqsub)
      simpa [domainIterationConstant, q, V, mul_assoc] using hmul

/-- The norm of the base inclusion is bounded by the iterated GNS
and extension constants, rather than used as the analytic constant itself. -/
theorem opNorm_baseEmbedding_le_domainIterationConstant
    [Fact (1 ≤ (p : ℝ≥0∞))]
    [Fact (1 ≤ (higherOrderExponent n j p : ℝ≥0∞))]
    (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n) :
    ‖embeddingCLMOfMemLp (base_memLp_iterated (Ω := Ω) hp hsub)‖ ≤
      domainIterationConstant (Ω := Ω) j p hp hsub := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (domainIterationConstant_nonneg hp hsub) fun U ↦ ?_
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNorm_base_le_domainIterationConstant hp hsub U)
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (domainIterationConstant_nonneg hp hsub) (norm_nonneg U))] at h
  change (eLpNorm (baseRepresentative U) _ _).toReal ≤ _
  exact h

end SobolevSpace.Inequalities

namespace SobolevSpace.GraphSpace.Embedding

open Inequalities
open scoped ENNReal Sobolev

variable {n j k : ℕ} {p : NNReal} {Ω : Set (ℝ^n)}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]
variable [Fact (1 ≤ (p : ℝ≥0∞))]
variable [Fact (1 ≤ (higherOrderExponent n j p : ℝ≥0∞))]

/-- Quantitative higher-order domain inclusion with the constants tracked
through all `j` first-order steps. No higher-order extension is assumed. -/
theorem norm_iteratedStepCLM_le_domainIterationConstant
    (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n)
    (U : W^{k + j,(p : ℝ≥0∞)}(Ω)) :
    ‖iteratedStepCLM hp hsub U‖ ≤ (Fintype.card (DerivIndex n k) : ℝ) *
      domainIterationConstant (Ω := Ω) j p hp hsub * ‖U‖ := by
  apply (norm_iteratedStepCLM_le hp hsub U).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (opNorm_baseEmbedding_le_domainIterationConstant hp hsub)
      (Nat.cast_nonneg _)) (norm_nonneg U)

/-- Operator-norm form of the quantitative higher-order domain inclusion. -/
theorem opNorm_iteratedStepCLM_le_domainIterationConstant
    (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n) :
    ‖iteratedStepCLM (k := k) (Ω := Ω) hp hsub‖ ≤
      (Fintype.card (DerivIndex n k) : ℝ) *
        domainIterationConstant (Ω := Ω) j p hp hsub :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Nat.cast_nonneg _) (domainIterationConstant_nonneg hp hsub))
    (norm_iteratedStepCLM_le_domainIterationConstant hp hsub)

end SobolevSpace.GraphSpace.Embedding
