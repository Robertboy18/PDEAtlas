/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Domain.CriticalEmbedding
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Domain.HolderStepEstimate

/-!
# Higher Hölder bounds through Sobolev iteration

The subcritical branch reaches the exact noninteger Hölder exponent. The critical
branch reaches every strict Hölder exponent by choosing a finite Morrey exponent.
Both bounds apply to the compatible representatives, and their constants
involve no higher-order extension or embedding norm.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Inequalities

open MeasureTheory GraphSpace GraphSpace.Embedding HolderSpace
open scoped ENNReal Sobolev

variable {n j k : ℕ} {p r : NNReal} {Ω : Set (ℝ^n)} {γ : Exponent}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- Explicit constant for the noninteger supercritical branch: subcritical
Sobolev iteration followed by first-order Morrey on every retained derivative. -/
def subcriticalHolderConstant (k j : ℕ) (p : NNReal)
    (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n) : ℝ :=
  have : Fact (1 ≤ (higherOrderExponent n j p : ℝ≥0∞)) :=
    ⟨by exact_mod_cast one_le_higherOrderExponent hp hsub⟩
  higherMorreyDomainConstant (Ω := Ω) (higherOrderExponent n j p) *
    (Fintype.card (DerivIndex n (k + 1)) : ℝ) *
      domainIterationConstant (Ω := Ω) j p hp hsub

/-- All factors in the noninteger Hölder constant are nonnegative. -/
theorem subcriticalHolderConstant_nonneg (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n) :
    0 ≤ subcriticalHolderConstant (Ω := Ω) k j p hp hsub := by
  have : Fact (1 ≤ (higherOrderExponent n j p : ℝ≥0∞)) :=
    ⟨by exact_mod_cast one_le_higherOrderExponent hp hsub⟩
  exact mul_nonneg (mul_nonneg higherMorreyDomainConstant_nonneg (Nat.cast_nonneg _))
    (domainIterationConstant_nonneg hp hsub)

/-- The noninteger branch has the exact Hölder exponent `j+1-n/p`, with the
quantitative constants from the subcritical chain and Morrey's estimate. -/
theorem norm_holderRepresentative_le_of_subcritical_iteration
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 ≤ p) (hsub : (j : ℝ) * p < n)
    (hsuper : (n : ℝ) < ((j : ℝ) + 1) * p)
    (hγ : (γ : ℝ) = (j : ℝ) + 1 - (n : ℝ) / p)
    (U : W^{k + 1 + j,(p : ℝ≥0∞)}(Ω)) (F : CKGammaOn n k Ω γ)
    (hF : F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    ‖F‖ ≤ subcriticalHolderConstant (Ω := Ω) k j p hp hsub * ‖U‖ := by
  have hn : 0 < n := Fact.out
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)
  let r := higherOrderExponent n j p
  have : Fact (1 ≤ (r : ℝ≥0∞)) :=
    ⟨by exact_mod_cast one_le_higherOrderExponent hp hsub⟩
  have hnr : (n : ℝ) < r := by
    rw [higherOrderExponent_coe hsub]
    apply (lt_div_iff₀ (sub_pos.mpr hsub)).mpr
    nlinarith [mul_pos hnR (sub_pos.mpr hsuper)]
  have hγr : (γ : ℝ) = 1 - (n : ℝ) / r := by
    rw [div_eq_mul_inv, inv_higherOrderExponent_eq hp0 hsub, hγ]
    field_simp
    ring
  let V := iteratedStepCLM (k := k + 1) hp hsub U
  have hVU : baseRepresentative V =ᵐ[domainMeasure n Ω] baseRepresentative U :=
    iteratedStepCLM_apply_ae hp hsub U (baseIndex n (k + 1))
  have h := norm_holderRepresentative_le_of_dimension_lt hnr hγr V F (hF.trans hVU.symm)
  refine h.trans ?_
  simpa [subcriticalHolderConstant, r, mul_assoc] using
    mul_le_mul_of_nonneg_left (norm_iteratedStepCLM_le_domainIterationConstant hp hsub U)
      (higherMorreyDomainConstant_nonneg (Ω := Ω) (p := r))

/-- Explicit critical-branch constant at a chosen finite Morrey exponent. -/
def criticalHolderConstant (k j : ℕ) (p r : NNReal) [Fact (1 ≤ (r : ℝ≥0∞))]
    (hp : 1 ≤ p) (hj : 0 < j) (hcrit : (j : ℝ) * p = n) : ℝ :=
  higherMorreyDomainConstant (Ω := Ω) r * (Fintype.card (DerivIndex n (k + 1)) : ℝ) *
    criticalDomainConstant (Ω := Ω) j p r hp hj hcrit

/-- The critical Hölder constant is nonnegative. -/
theorem criticalHolderConstant_nonneg [Fact (1 ≤ (r : ℝ≥0∞))]
    (hp : 1 ≤ p) (hj : 0 < j) (hcrit : (j : ℝ) * p = n) :
    0 ≤ criticalHolderConstant (Ω := Ω) k j p r hp hj hcrit :=
  mul_nonneg (mul_nonneg higherMorreyDomainConstant_nonneg (Nat.cast_nonneg _))
    (criticalDomainConstant_nonneg hp hj hcrit)

/-- The integer branch uses a finite critical target `r > n`, giving the exact
strict Hölder exponent `1-n/r` without an `L∞` critical endpoint. -/
theorem norm_holderRepresentative_le_of_critical_iteration
    [Fact (1 ≤ (p : ℝ≥0∞))] [Fact (1 ≤ (r : ℝ≥0∞))]
    (hp : 1 ≤ p) (hj : 0 < j) (hcrit : (j : ℝ) * p = n)
    (hr : (n : ℝ) < r) (hγ : (γ : ℝ) = 1 - (n : ℝ) / r)
    (U : W^{k + 1 + j,(p : ℝ≥0∞)}(Ω)) (F : CKGammaOn n k Ω γ)
    (hF : F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    ‖F‖ ≤ criticalHolderConstant (Ω := Ω) k j p r hp hj hcrit * ‖U‖ := by
  have hr1 : 1 ≤ r := by
    exact_mod_cast (show (1 : ℝ) ≤ r from
      (by exact_mod_cast Fact.out (p := 0 < n) : (1 : ℝ) ≤ n).trans hr.le)
  let V := criticalIterationCLM (k := k + 1) hp hj hcrit hr1 U
  have hVU : baseRepresentative V =ᵐ[domainMeasure n Ω] baseRepresentative U :=
    criticalIterationCLM_apply_ae hp hj hcrit hr1 U (baseIndex n (k + 1))
  have h := norm_holderRepresentative_le_of_dimension_lt hr hγ V F (hF.trans hVU.symm)
  refine h.trans ?_
  simpa [criticalHolderConstant, mul_assoc] using
    mul_le_mul_of_nonneg_left (norm_criticalIterationCLM_le hp hj hcrit hr1 U)
      (higherMorreyDomainConstant_nonneg (Ω := Ω) (p := r))

/-- Infinite source exponent is handled by quantitative finite-volume restriction,
followed by Morrey at any finite `r > n`. -/
theorem norm_holderRepresentative_le_of_infinity
    [Fact (1 ≤ (r : ℝ≥0∞))]
    (hr : (n : ℝ) < r) (hγ : (γ : ℝ) = 1 - (n : ℝ) / r)
    (U : W^{k + 1,∞}(Ω)) (F : CKGammaOn n k Ω γ)
    (hF : F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    ‖F‖ ≤ higherMorreyDomainConstant (Ω := Ω) r *
      finiteMeasureExponentRestrictionNormBound n (k + 1) ∞ (r : ℝ≥0∞) Ω * ‖U‖ := by
  let V := lowerExponentOfFiniteMeasure (show (r : ℝ≥0∞) ≤ ∞ from le_top) U
  have hVU : baseRepresentative V =ᵐ[domainMeasure n Ω] baseRepresentative U :=
    lowerExponentOfFiniteMeasure_apply_ae le_top U (baseIndex n (k + 1))
  have h := norm_holderRepresentative_le_of_dimension_lt hr hγ V F (hF.trans hVU.symm)
  refine h.trans ?_
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left (norm_lowerExponentOfFiniteMeasure_le (q := (r : ℝ≥0∞)) le_top U)
      (higherMorreyDomainConstant_nonneg (Ω := Ω) (p := r))

end SobolevSpace.Inequalities
