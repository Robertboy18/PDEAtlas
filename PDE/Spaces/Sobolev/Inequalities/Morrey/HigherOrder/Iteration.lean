/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.ExponentRestriction
public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Holder
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Iteration

/-!
# Iterated embeddings into classical higher Hölder spaces

The subcritical steps improve the integrability of the derivative graph.
At the critical exponent one further step reaches any finite exponent. Morrey's
theorem then gives a single compatible classical representative, including all
continuous derivative extensions to the closure.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory HolderSpace Inequalities
open scoped ENNReal Sobolev

variable {n m j : ℕ} {Ω : Set (ℝ^n)} {γ : Exponent}
  [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- Above the dimension, the finite-exponent Morrey construction gives the full
classical derivative graph at its exact Hölder exponent. -/
theorem exists_higherHolder_of_dimension_lt {p : NNReal}
    [hpFact : Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : (n : ℝ) < p) (hγ : (γ : ℝ) = 1 - (n : ℝ) / p)
    (U : W^{m + 1,(p : ℝ≥0∞)}(Ω)) :
    ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have hn : 0 < n := Fact.out
  have hp1 : 1 < (p : ℝ) := (by exact_mod_cast hn : (1 : ℝ) ≤ n).trans_lt hp
  have he : finiteMorreyHolderExponent n p hn hp = γ := by
    apply Subtype.ext
    apply NNReal.eq
    rw [finiteMorreyHolderExponent_coe, Real.coe_toNNReal _
      (morreyExponent_ofReal_pos hn hp).le]
    simpa only [morreyExponent, ENNReal.toReal_ofReal (le_of_lt (by linarith : 0 < (p : ℝ)))]
      using hγ.symm
  revert U hpFact
  rw [← ENNReal.ofReal_coe_nnreal (p := p)]
  intro inst V
  rw [← he]
  exact ⟨finiteHigherHolderRepresentative hp
    (Real.HolderConjugate.conjExponent hp1) V,
    finiteHigherHolderRepresentative_ae hp (Real.HolderConjugate.conjExponent hp1) V⟩

/-- Spending `j` derivatives in subcritical Sobolev steps gives the exact remaining
Hölder exponent, even when the original exponent is one. -/
theorem exists_higherHolder_of_subcritical_iteration {p : NNReal}
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (hsub : (j : ℝ) * p < n)
    (hsuper : (n : ℝ) < ((j : ℝ) + 1) * p)
    (hγ : (γ : ℝ) = (j : ℝ) + 1 - (n : ℝ) / p)
    (U : W^{m + 1 + j,(p : ℝ≥0∞)}(Ω)) :
    ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have hp : 1 ≤ p := by exact_mod_cast (Fact.out : 1 ≤ (p : ℝ≥0∞))
  have hn : 0 < n := Fact.out
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)
  let r := higherOrderExponent n j p
  have hr1 : 1 ≤ r := one_le_higherOrderExponent hp hsub
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr1⟩
  have hnr : (n : ℝ) < r := by
    rw [higherOrderExponent_coe hsub]
    apply (lt_div_iff₀ (sub_pos.mpr hsub)).mpr
    nlinarith [mul_pos hnR (sub_pos.mpr hsuper)]
  have hγr : (γ : ℝ) = 1 - (n : ℝ) / r := by
    rw [div_eq_mul_inv, inv_higherOrderExponent_eq hp0 hsub, hγ]
    field_simp
    ring
  let V := Embedding.iteratedStep (k := m + 1) hp hsub U
  obtain ⟨F, hF⟩ := exists_higherHolder_of_dimension_lt hnr hγr V
  refine ⟨F, hF.trans ?_⟩
  simpa only [baseRepresentative, DerivIndex.castOrder_baseIndex] using
    Embedding.iteratedStep_apply_ae hp hsub U (baseIndex n (m + 1))

omit [Boundary.C1ExtensionAtlas n Ω] in
/-- Every strict Hölder exponent is the exact Morrey exponent of a finite exponent. -/
theorem exists_finiteExponent_of_holder (hγ : (γ : ℝ) < 1) :
    ∃ r : NNReal, (n : ℝ) < r ∧ (γ : ℝ) = 1 - (n : ℝ) / r := by
  have hn : 0 < n := Fact.out
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ0 : (0 : ℝ) < γ := γ.pos
  let r : NNReal := ⟨(n : ℝ) / (1 - γ), by positivity⟩
  have hnr : (n : ℝ) < r := by
    change (n : ℝ) < (n : ℝ) / (1 - γ)
    apply (lt_div_iff₀ (sub_pos.mpr hγ)).mpr
    nlinarith [mul_pos hnR hγ0]
  refine ⟨r, hnr, ?_⟩
  change (γ : ℝ) = 1 - (n : ℝ) / ((n : ℝ) / (1 - γ))
  field_simp
  ring

/-- The critical first-order step followed by Morrey gives every exponent strictly
between zero and one, with one fewer classical derivative. -/
theorem exists_higherHolder_of_critical_step (hγ : (γ : ℝ) < 1)
    (U : W^{m + 1 + 1,(n : ℝ≥0∞)}(Ω)) :
    ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have hn : 0 < n := Fact.out
  obtain ⟨r, hnr, hγr⟩ := exists_finiteExponent_of_holder (n := n) hγ
  have hr1 : (1 : NNReal) ≤ r := by
    exact_mod_cast ((by exact_mod_cast hn : (1 : ℝ) ≤ n).trans hnr.le)
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr1⟩
  have : Fact (1 ≤ (n : ℝ≥0∞)) := ⟨by exact_mod_cast hn⟩
  let V := Embedding.criticalStep (k := m + 1) hr1 U
  obtain ⟨F, hF⟩ := exists_higherHolder_of_dimension_lt hnr hγr V
  refine ⟨F, hF.trans ?_⟩
  simpa only [baseRepresentative, DerivIndex.castOrder_baseIndex] using
    Embedding.criticalStep_apply_ae hr1 U (baseIndex n (m + 1))

/-- In the integer case, subcritical iteration reaches the dimension and the critical
step supplies every strict Hölder exponent. -/
theorem exists_higherHolder_of_critical_iteration {p : NNReal}
    [Fact (1 ≤ (p : ℝ≥0∞))]
    (hj : 0 < j) (hcrit : (j : ℝ) * p = n)
    (hγ : (γ : ℝ) < 1)
    (U : W^{m + 1 + j,(p : ℝ≥0∞)}(Ω)) :
    ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have hp : 1 ≤ p := by exact_mod_cast (Fact.out : 1 ≤ (p : ℝ≥0∞))
  have hn : 0 < n := Fact.out
  have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)
  have hpred : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hsub : ((j - 1 : ℕ) : ℝ) * p < n := by rw [hpred]; nlinarith
  have hexp := higherOrderExponent_pred_eq_dimension hj hp0 hcrit
  have horder : m + 1 + j = (m + 1 + 1) + (j - 1) := by omega
  revert U
  rw [horder]
  intro U
  let V := Embedding.iteratedStep (k := m + 1 + 1) hp hsub U
  have hV : ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative V := by
    generalize V = V'
    revert V'
    rw [hexp, ENNReal.coe_natCast]
    exact exists_higherHolder_of_critical_step hγ
  obtain ⟨F, hF⟩ := hV
  refine ⟨F, hF.trans ?_⟩
  simpa only [baseRepresentative, DerivIndex.castOrder_baseIndex] using
    Embedding.iteratedStep_apply_ae hp hsub U (baseIndex n (m + 1 + 1))

/-- Bounded weak derivatives give every strict Hölder exponent by finite-volume
exponent restriction, with the same order and the same weak derivative graph. -/
theorem exists_higherHolder_of_infinity (hγ : (γ : ℝ) < 1)
    (U : W^{m + 1,∞}(Ω)) :
    ∃ F : CKGammaOn n m Ω γ,
      F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U := by
  have hn : 0 < n := Fact.out
  obtain ⟨r, hnr, hγr⟩ := exists_finiteExponent_of_holder (n := n) hγ
  have hr1 : (1 : NNReal) ≤ r := by
    exact_mod_cast ((by exact_mod_cast hn : (1 : ℝ) ≤ n).trans hnr.le)
  have : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr1⟩
  let V := lowerExponentOfFiniteMeasure (q := (r : ℝ≥0∞)) le_top U
  obtain ⟨F, hF⟩ := exists_higherHolder_of_dimension_lt hnr hγr V
  exact ⟨F, hF.trans (lowerExponentOfFiniteMeasure_apply_ae le_top U (baseIndex n (m + 1)))⟩

end SobolevSpace.GraphSpace
