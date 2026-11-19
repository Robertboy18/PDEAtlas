/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.General

/-!
# Quantitative bounds for compatible higher Hölder representatives

The compatible representative is built from first-order Morrey fields.
Contractivity of derivative slices and restriction bounds its entire higher
Hölder graph norm by the explicit first-order Morrey constant and the operational
extension norm. Uniqueness transfers this estimate to any representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory HolderSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

open Inequalities

variable {n k : ℕ} {p q : ℝ} {Ω : Set (ℝ^n)}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω] [Fact (1 ≤ ENNReal.ofReal p)]

/-- Each global derivative field satisfies the first-order Morrey estimate. -/
theorem norm_higherMorreyField_le (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{k + 1,ENNReal.ofReal p}(Ω)) (a : MultiIndex n k) :
    ‖higherMorreyField hp hpq U a‖ ≤ finiteMorreyEmbeddingConstant n p q *
      ‖Extension.C1.extensionCLM (n := n) (p := ENNReal.ofReal p) (Ω := Ω)‖ * ‖U‖ := by
  let V := derivativeWordCLM (r := 1) a.derivIndex.toList
    (by rw [MultiIndex.derivIndex_length]; exact Nat.add_le_add_right a.order_le 1) U
  let E := Extension.C1.extensionCLM (n := n) (p := ENNReal.ofReal p) (Ω := Ω)
  have hV : ‖V‖ ≤ ‖U‖ := norm_derivativeWordCLM_apply_le _ _ U
  exact (norm_morreyHolderRepresentative_le Fact.out hp hpq (E V)).trans
    ((mul_le_mul_of_nonneg_left
      ((E.le_opNorm V).trans (mul_le_mul_of_nonneg_left hV (norm_nonneg E)))
      (finiteMorreyEmbeddingConstant_nonneg n p q)).trans_eq (mul_assoc _ _ _).symm)

/-- The compatible higher-order representative has the same graph-norm
bound as its derivative fields, independently of the retained classical order. -/
theorem norm_finiteHigherHolderRepresentative_le
    (hp : (n : ℝ) < p) (hpq : p.HolderConjugate q)
    (U : W^{k + 1,ENNReal.ofReal p}(Ω)) :
    ‖finiteHigherHolderRepresentative hp hpq U‖ ≤ finiteMorreyEmbeddingConstant n p q *
      ‖Extension.C1.extensionCLM (n := n) (p := ENNReal.ofReal p) (Ω := Ω)‖ * ‖U‖ := by
  have hC : 0 ≤ finiteMorreyEmbeddingConstant n p q *
      ‖Extension.C1.extensionCLM (n := n) (p := ENNReal.ofReal p) (Ω := Ω)‖ * ‖U‖ :=
    mul_nonneg (mul_nonneg (finiteMorreyEmbeddingConstant_nonneg n p q) (by positivity))
      (norm_nonneg U)
  change ‖(finiteHigherHolderRepresentative hp hpq U).val‖ ≤ _
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro a
    exact (C0GammaOn.norm_toBoundedContinuousFunction_le _).trans
      ((C0GammaOn.norm_restrict_le (closure Ω) _).trans (norm_higherMorreyField_le hp hpq U a))
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro a
    exact (C0GammaOn.norm_restrict_le (closure Ω) _).trans
      (norm_higherMorreyField_le hp hpq U a.1)

end SobolevSpace.GraphSpace

namespace SobolevSpace.Inequalities

open GraphSpace

variable {n k : ℕ} {p : NNReal} {Ω : Set (ℝ^n)} {γ : Exponent}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- The higher Morrey domain constant uses the explicit global Morrey constant
and the first-order extension at the same exponent. -/
def higherMorreyDomainConstant (p : NNReal) [Fact (1 ≤ (p : ℝ≥0∞))] : ℝ :=
  finiteMorreyEmbeddingConstant n p (Real.conjExponent p) *
    ‖Extension.C1.extensionCLM (n := n) (p := (p : ℝ≥0∞)) (Ω := Ω)‖

/-- The higher Morrey domain constant is nonnegative. -/
theorem higherMorreyDomainConstant_nonneg [Fact (1 ≤ (p : ℝ≥0∞))] :
    0 ≤ higherMorreyDomainConstant (Ω := Ω) p :=
  mul_nonneg (finiteMorreyEmbeddingConstant_nonneg _ _ _) (by positivity)

/-- Every compatible representative at the exact Morrey exponent satisfies the
explicit estimate, including representatives selected by the general theorem. -/
theorem norm_holderRepresentative_le_of_dimension_lt
    [hpFact : Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : (n : ℝ) < p) (hγ : (γ : ℝ) = 1 - (n : ℝ) / p)
    (U : W^{k + 1,(p : ℝ≥0∞)}(Ω)) (F : CKGammaOn n k Ω γ)
    (hF : F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    ‖F‖ ≤ higherMorreyDomainConstant (Ω := Ω) p * ‖U‖ := by
  have hn : 0 < n := Fact.out
  have hp1 : 1 < (p : ℝ) := (by exact_mod_cast hn : (1 : ℝ) ≤ n).trans_lt hp
  have he : finiteMorreyHolderExponent n p hn hp = γ := by
    apply Subtype.ext
    apply NNReal.eq
    rw [finiteMorreyHolderExponent_coe, Real.coe_toNNReal _
      (morreyExponent_ofReal_pos hn hp).le]
    simpa only [morreyExponent, ENNReal.toReal_ofReal (by positivity : 0 ≤ (p : ℝ))]
      using hγ.symm
  subst γ
  have : Fact (1 ≤ ENNReal.ofReal (p : ℝ)) := ⟨by simpa using hpFact.out⟩
  let V := WkpSpaceOn.congrExponent (ENNReal.ofReal_coe_nnreal (p := p)).symm n (k + 1) Ω U
  have hVU : baseRepresentative V = baseRepresentative U :=
    WkpSpaceOn.coordinate_congrExponent _ U (baseIndex n (k + 1))
  have hFeq : F = finiteHigherHolderRepresentative hp
      (Real.HolderConjugate.conjExponent hp1) V :=
    CKGammaOn.ext_of_ae_eq Boundary.C1ExtensionAtlas.isOpen
      (hF.trans ((finiteHigherHolderRepresentative_ae hp
        (Real.HolderConjugate.conjExponent hp1) V).trans
          (Filter.EventuallyEq.of_eq hVU)).symm)
  have htransport {r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)] (he : r = s) :
      ‖Extension.C1.extensionCLM (n := n) (p := r) (Ω := Ω)‖ =
        ‖Extension.C1.extensionCLM (n := n) (p := s) (Ω := Ω)‖ := by
    subst s
    rfl
  rw [hFeq]
  have h := norm_finiteHigherHolderRepresentative_le hp
    (Real.HolderConjugate.conjExponent hp1) V
  rw [htransport (ENNReal.ofReal_coe_nnreal (p := p)), WkpSpaceOn.norm_congrExponent] at h
  exact h

end SobolevSpace.Inequalities
