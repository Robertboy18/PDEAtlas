/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Domain.HolderIterationEstimate

/-!
# Quantitative operator bounds in the general Sobolev Hölder target

We bound the all-order representative and its closed-graph inclusion. For finite `p`,
the classical order is `k-floor(n/p)-1`. The noninteger case uses the exact fractional
exponent; the integer case uses any `0 < γ < 1`.
The constant consists entirely of the first-order GNS, Morrey, extension, and
finite-volume estimates. The infinite source exponent is treated separately. With the norm
(3) of Evans §5.1, this gives the estimate (32) of Evans §5.6.3, Theorem 6(ii), with an
explicit constant.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.1, the norm (3), p. 255; and §5.6.3, Theorem 6(ii), (32),
  pp. 284-286.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Inequalities

open MeasureTheory GraphSpace HolderSpace
open scoped ENNReal Sobolev

variable {n k : ℕ} {p : NNReal} {Ω : Set (ℝ^n)} {γ : Exponent}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- The operational constant for the floor-indexed finite-exponent Hölder target.
In the integer case the exponent-selection theorem chooses the finite
Morrey exponent satisfying `γ = 1-n/r`, equivalently `r = n/(1-γ)`. -/
def generalFiniteHolderConstant (k : ℕ) (p : NNReal) (γ : Exponent)
    (hp : 1 ≤ p) (hγ : (γ : ℝ) < 1) : ℝ :=
  let j := ⌊(n : ℝ) / p⌋₊
  have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)
  have hnR : (0 : ℝ) < n := by exact_mod_cast Fact.out (p := 0 < n)
  if hc : (j : ℝ) = (n : ℝ) / p then
    let r := (exists_finiteExponent_of_holder (n := n) hγ).choose
    have hr := (exists_finiteExponent_of_holder (n := n) hγ).choose_spec.1
    have : Fact (1 ≤ (r : ℝ≥0∞)) :=
      ⟨by exact_mod_cast
        ((by exact_mod_cast Fact.out (p := 0 < n) : (1 : ℝ) ≤ n).trans hr.le)⟩
    criticalHolderConstant (Ω := Ω) (k - j - 1) j p r hp
      (by have : (0 : ℝ) < j := hc ▸ div_pos hnR hp0; exact_mod_cast this)
      ((eq_div_iff hp0.ne').mp hc)
  else
    subcriticalHolderConstant (Ω := Ω) (k - j - 1) j p hp
      ((lt_div_iff₀ hp0).mp
        (lt_of_le_of_ne (Nat.floor_le (div_nonneg hnR.le hp0.le)) hc))

/-- The all-order Hölder constant is nonnegative. -/
theorem generalFiniteHolderConstant_nonneg (hp : 1 ≤ p) (hγ : (γ : ℝ) < 1) :
    0 ≤ generalFiniteHolderConstant (Ω := Ω) k p γ hp hγ := by
  let r := (exists_finiteExponent_of_holder (n := n) hγ).choose
  have hr := (exists_finiteExponent_of_holder (n := n) hγ).choose_spec.1
  have : Fact (1 ≤ (r : ℝ≥0∞)) :=
    ⟨by exact_mod_cast
      ((by exact_mod_cast Fact.out (p := 0 < n) : (1 : ℝ) ≤ n).trans hr.le)⟩
  unfold generalFiniteHolderConstant
  dsimp only
  split
  · exact criticalHolderConstant_nonneg _ _ _
  · exact subcriticalHolderConstant_nonneg _ _

/-- The all-order compatible representative satisfies the explicit analytic
bound at the exact classical order, for every finite `p ≥ 1`. -/
theorem norm_generalHolderRepresentative_le [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 ≤ p) (hsuper : (n : ℝ) / p < k) (hγ : (γ : ℝ) < 1)
    (hγfrac : (⌊(n : ℝ) / p⌋₊ : ℝ) ≠ (n : ℝ) / p →
      (γ : ℝ) = (⌊(n : ℝ) / p⌋₊ : ℝ) + 1 - (n : ℝ) / p)
    (U : W^{k,(p : ℝ≥0∞)}(Ω))
    (F : CKGammaOn n (k - ⌊(n : ℝ) / p⌋₊ - 1) Ω γ)
    (hF : F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    ‖F‖ ≤ generalFiniteHolderConstant (Ω := Ω) k p γ hp hγ * ‖U‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Fact.out (p := 0 < n)
  have hp0 : 0 < (p : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)
  let j := ⌊(n : ℝ) / p⌋₊
  have hjk : j < k := (Nat.floor_lt (div_nonneg hnR.le hp0.le)).mpr hsuper
  have horder : k = (k - j - 1) + 1 + j := by omega
  by_cases hc : (j : ℝ) = (n : ℝ) / p
  · let r := (exists_finiteExponent_of_holder (n := n) hγ).choose
    have hr := (exists_finiteExponent_of_holder (n := n) hγ).choose_spec.1
    have hγr := (exists_finiteExponent_of_holder (n := n) hγ).choose_spec.2
    have : Fact (1 ≤ (r : ℝ≥0∞)) :=
      ⟨by exact_mod_cast
        ((by exact_mod_cast Fact.out (p := 0 < n) : (1 : ℝ) ≤ n).trans hr.le)⟩
    have hj : 0 < j := by
      have : (0 : ℝ) < j := hc ▸ div_pos hnR hp0
      exact_mod_cast this
    have hcrit : (j : ℝ) * p = n := (eq_div_iff hp0.ne').mp hc
    have hbound := norm_holderRepresentative_le_of_critical_iteration
      (Ω := Ω) (k := k - j - 1) hp hj hcrit hr hγr
    rw [← horder] at hbound
    have hc' : (⌊(n : ℝ) / p⌋₊ : ℝ) = (n : ℝ) / p := hc
    simpa only [generalFiniteHolderConstant, dite_eq_left hc', j] using hbound U F hF
  · have hsub : (j : ℝ) * p < n :=
      (lt_div_iff₀ hp0).mp
        (lt_of_le_of_ne (Nat.floor_le (div_nonneg hnR.le hp0.le)) hc)
    have hsup : (n : ℝ) < ((j : ℝ) + 1) * p :=
      (div_lt_iff₀ hp0).mp (Nat.lt_floor_add_one ((n : ℝ) / p))
    have hbound := norm_holderRepresentative_le_of_subcritical_iteration
      (Ω := Ω) (k := k - j - 1) hp hsub hsup (hγfrac hc)
    rw [← horder] at hbound
    have hc' : (⌊(n : ℝ) / p⌋₊ : ℝ) ≠ (n : ℝ) / p := hc
    simpa only [generalFiniteHolderConstant, dite_eq_right hc', j] using hbound U F hF

/-- Quantitative operator bound for the general finite-exponent inclusion.
The representative and its continuity are reused from `HigherOrder.General`. -/
theorem opNorm_generalHolderEmbedding_finite_le [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 ≤ p) (hsuper : (n : ℝ) / p < k) (hγ : (γ : ℝ) < 1)
    (hγfrac : (⌊(n : ℝ) / p⌋₊ : ℝ) ≠ (n : ℝ) / p →
      (γ : ℝ) = (⌊(n : ℝ) / p⌋₊ : ℝ) + 1 - (n : ℝ) / p) :
    ‖holderEmbeddingCLMOfExists Boundary.C1ExtensionAtlas.isOpen
        (exists_higherHolder_representative_finite (Ω := Ω) hp hsuper (fun _ ↦ hγ) hγfrac)‖ ≤
      generalFiniteHolderConstant (Ω := Ω) k p γ hp hγ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (generalFiniteHolderConstant_nonneg hp hγ) fun U ↦ ?_
  exact norm_generalHolderRepresentative_le hp hsuper hγ hγfrac U _
    (holderRepresentativeOfExists_ae _ U)

/-- The estimate (32) of Evans §5.6.3, Theorem 6(ii), with an explicit constant: if `1 ≤ p`,
`n / p < k`, `γ < 1` and `γ = ⌊n/p⌋ + 1 - n/p` when `n / p` is not an integer, then every
representative `F ∈ C^{k-⌊n/p⌋-1,γ}(Ω̄)` of `U ∈ W^{k,p}(Ω)` satisfies
`F.evansNorm ≤ (N + N') * generalFiniteHolderConstant k p γ * ‖U‖`, where `N` and `N'` count
the multi-indices of order at most `k - ⌊n/p⌋ - 1` and of order exactly `k - ⌊n/p⌋ - 1`. -/
theorem evansNorm_generalHolderRepresentative_le [Fact (1 ≤ (p : ℝ≥0∞))]
    (hp : 1 ≤ p) (hsuper : (n : ℝ) / p < k) (hγ : (γ : ℝ) < 1)
    (hγfrac : (⌊(n : ℝ) / p⌋₊ : ℝ) ≠ (n : ℝ) / p →
      (γ : ℝ) = (⌊(n : ℝ) / p⌋₊ : ℝ) + 1 - (n : ℝ) / p)
    (U : W^{k,(p : ℝ≥0∞)}(Ω))
    (F : CKGammaOn n (k - ⌊(n : ℝ) / p⌋₊ - 1) Ω γ)
    (hF : F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    F.evansNorm ≤
      (Fintype.card (MultiIndex n (k - ⌊(n : ℝ) / p⌋₊ - 1)) +
        Fintype.card (MultiIndex.Top n (k - ⌊(n : ℝ) / p⌋₊ - 1)) : ℝ) *
          generalFiniteHolderConstant (Ω := Ω) k p γ hp hγ * ‖U‖ := by
  exact F.evansNorm_le.trans
    ((mul_le_mul_of_nonneg_left
      (norm_generalHolderRepresentative_le hp hsuper hγ hγfrac U F hF)
      (by positivity)).trans_eq (mul_assoc _ _ _).symm)

/-- Quantitative operator bound at infinite source exponent, using a finite
auxiliary Morrey exponent `r = n/(1-γ)`. -/
theorem opNorm_holderEmbedding_infinity_le {r : NNReal} [Fact (1 ≤ (r : ℝ≥0∞))]
    (hr : (n : ℝ) < r) (hγ : (γ : ℝ) < 1)
    (hγr : (γ : ℝ) = 1 - (n : ℝ) / r) :
    ‖holderEmbeddingCLMOfExists Boundary.C1ExtensionAtlas.isOpen
        (exists_higherHolder_of_infinity (m := k) (Ω := Ω) hγ)‖ ≤
      higherMorreyDomainConstant (Ω := Ω) r *
        finiteMeasureExponentRestrictionNormBound n (k + 1) ∞ (r : ℝ≥0∞) Ω := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg higherMorreyDomainConstant_nonneg
      finiteMeasureExponentRestrictionNormBound_nonneg) fun U ↦ ?_
  exact norm_holderRepresentative_le_of_infinity hr hγr U _
    (holderRepresentativeOfExists_ae _ U)

end SobolevSpace.Inequalities
