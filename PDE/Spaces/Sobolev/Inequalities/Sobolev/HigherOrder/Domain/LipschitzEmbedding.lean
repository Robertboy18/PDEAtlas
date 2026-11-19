/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.ContinuousEmbedding
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Domain.LipschitzFields

/-!
# The higher-order Lipschitz endpoint on bounded C¹ domains

The inclusion `W^{k+1,∞}(Ω) → C^{k,1}(closure Ω)` takes values in the
compatible classical derivative graph. Its compatibility follows from the
finite-exponent representative after identifying the fields on the closure.
Its quantitative bound comes directly from first-order Lipschitz estimates and
extension, independently of the auxiliary finite exponent and the retained order.

Evans §5.6.3, Theorem 6(ii), read with `p = ∞` (so that `n/p = 0` is an integer), gives
`C^{k,γ}(Ω̄)` for every `γ < 1`; the endpoint `γ = 1` rests on the case `p = ∞` of
§5.6.2, Theorem 5.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.1, the norm (3), p. 255; §5.6.2, Theorem 5, pp. 283-284;
  and §5.6.3, Theorem 6(ii), pp. 284-286.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory HolderSpace Inequalities Set
open scoped ENNReal Sobolev

variable {n k : ℕ} {Ω : Set (ℝ^n)}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- The compatible classical representative at the true Lipschitz endpoint.
The finite-exponent graph supplies compatibility; its fields agree with the
bounded Lipschitz representatives on the closure. -/
def higherLipschitzRepresentative (U : W^{k + 1,∞}(Ω)) :
    CKGammaOn n k Ω 1 := by
  let p : ℝ := (n : ℝ) + 1
  have hp : (n : ℝ) < p := lt_add_one _
  have hp1 : 1 < p := by
    have hn : (0 : ℝ) < n := by exact_mod_cast Fact.out (p := 0 < n)
    dsimp only [p]
    linarith
  have : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp1.le⟩
  let V := lowerExponentOfFiniteMeasure (show ENNReal.ofReal p ≤ ∞ from le_top) U
  let F := finiteHigherHolderRepresentative hp (Real.HolderConjugate.conjExponent hp1) V
  let G (a : MultiIndex n k) : C0GammaOn (closure Ω) 1 :=
    C0GammaOn.restrict (closure Ω)
      (lipschitzDerivativeField a.derivIndex.toList
        (Nat.add_le_add_right a.derivIndex.toList_length_le 1) U)
  have hGF (a : MultiIndex n k) : (G a).toBoundedContinuousFunction = F.derivative a := by
    apply BoundedContinuousFunction.ext
    intro x
    exact lipschitzDerivativeField_eqOn_finiteMorrey hp
      (Real.HolderConjugate.conjExponent hp1) a.derivIndex.toList
      (Nat.add_le_add_right a.derivIndex.toList_length_le 1) U x.2
  refine ⟨(fun a ↦ (G a).toBoundedContinuousFunction, fun a ↦ G a.1), ?_, ?_⟩
  · intro a
    rfl
  · intro a ha x hx
    rw [JetData.gradientCLM_apply]
    simpa only [hGF, CKGammaOn.interiorDerivative] using F.hasFDerivAt_derivative a ha hx

/-- Every classical derivative is the restriction of its bounded Lipschitz field. -/
theorem higherLipschitzRepresentative_derivative (U : W^{k + 1,∞}(Ω))
    (a : MultiIndex n k) :
    (higherLipschitzRepresentative U).derivative a =
      (C0GammaOn.restrict (closure Ω)
        (lipschitzDerivativeField a.derivIndex.toList
          (Nat.add_le_add_right a.derivIndex.toList_length_le 1) U)).toBoundedContinuousFunction :=
  rfl

/-- Every retained classical derivative represents the corresponding weak derivative. -/
theorem higherLipschitzRepresentative_derivative_ae (U : W^{k + 1,∞}(Ω))
    (a : MultiIndex n k) :
    (higherLipschitzRepresentative U).interiorDerivative a =ᵐ[domainMeasure n Ω]
      (U.val (a.derivIndex.castOrder (Nat.le_add_right k 1)) : ℝ^n → ℝ) := by
  have h := lipschitzDerivativeField_ae a.derivIndex.toList
    (Nat.add_le_add_right a.derivIndex.toList_length_le 1) U
  rw [derivativeWordIndex_toList_baseIndex] at h
  filter_upwards [h, ae_restrict_mem Boundary.C1ExtensionAtlas.isOpen.measurableSet]
    with x hx hΩ
  rw [CKGammaOn.interiorDerivative_apply _ _ (subset_closure hΩ),
    higherLipschitzRepresentative_derivative]
  exact hx

/-- The endpoint representative agrees almost everywhere with the Sobolev function. -/
theorem higherLipschitzRepresentative_ae (U : W^{k + 1,∞}(Ω)) :
    (higherLipschitzRepresentative U).interiorDerivative 0 =ᵐ[domainMeasure n Ω]
      baseRepresentative U := by
  simpa [baseRepresentative] using higherLipschitzRepresentative_derivative_ae U 0

/-- The full compatible graph norm is controlled by the first-order endpoint
constant, with no factor depending on the number of retained derivatives. -/
theorem norm_higherLipschitzRepresentative_le (U : W^{k + 1,∞}(Ω)) :
    ‖higherLipschitzRepresentative U‖ ≤
      higherLipschitzDomainConstant (n := n) (Ω := Ω) * ‖U‖ := by
  have hC : 0 ≤ higherLipschitzDomainConstant (n := n) (Ω := Ω) * ‖U‖ :=
    mul_nonneg higherLipschitzDomainConstant_nonneg (norm_nonneg U)
  change ‖(higherLipschitzRepresentative U).val‖ ≤ _
  apply norm_prod_le_iff.mpr
  constructor
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro a
    exact (C0GammaOn.norm_toBoundedContinuousFunction_le _).trans
      ((C0GammaOn.norm_restrict_le (closure Ω) _).trans
        (norm_lipschitzDerivativeField_le _ _ U))
  · apply (pi_norm_le_iff_of_nonneg hC).mpr
    intro a
    exact (C0GammaOn.norm_restrict_le (closure Ω) _).trans
      (norm_lipschitzDerivativeField_le _ _ U)

end SobolevSpace.GraphSpace

namespace SobolevSpace.Inequalities

open MeasureTheory GraphSpace HolderSpace
open scoped ENNReal Sobolev

variable {n k : ℕ} {Ω : Set (ℝ^n)}
variable [Fact (0 < n)] [Boundary.C1ExtensionAtlas n Ω]

/-- The true higher-order endpoint inclusion, using the closed-graph
construction on the compatible Lipschitz representative. -/
def higherLipschitzEmbedding :
    W^{k + 1,∞}(Ω) →L[ℝ] CKGammaOn n k Ω 1 :=
  holderEmbeddingCLMOfExists Boundary.C1ExtensionAtlas.isOpen
    (fun U ↦ ⟨higherLipschitzRepresentative U, higherLipschitzRepresentative_ae U⟩)

/-- The bounded inclusion selects the same unique compatible endpoint representative. -/
theorem higherLipschitzEmbedding_apply (U : W^{k + 1,∞}(Ω)) :
    higherLipschitzEmbedding U = higherLipschitzRepresentative U := by
  apply CKGammaOn.ext_of_ae_eq Boundary.C1ExtensionAtlas.isOpen
  exact (holderRepresentativeOfExists_ae _ U).trans (higherLipschitzRepresentative_ae U).symm

/-- The bounded inclusion preserves every retained derivative almost everywhere. -/
theorem higherLipschitzEmbedding_derivative_ae (U : W^{k + 1,∞}(Ω))
    (a : MultiIndex n k) :
    (higherLipschitzEmbedding U).interiorDerivative a =ᵐ[domainMeasure n Ω]
      (U.val (a.derivIndex.castOrder (Nat.le_add_right k 1)) : ℝ^n → ℝ) := by
  rw [higherLipschitzEmbedding_apply]
  exact higherLipschitzRepresentative_derivative_ae U a

/-- The endpoint inclusion represents the original Sobolev function. -/
theorem higherLipschitzEmbedding_ae (U : W^{k + 1,∞}(Ω)) :
    (higherLipschitzEmbedding U).interiorDerivative 0 =ᵐ[domainMeasure n Ω]
      baseRepresentative U := by
  rw [higherLipschitzEmbedding_apply]
  exact higherLipschitzRepresentative_ae U

/-- The operational first-order extension norm controls the entire endpoint operator. -/
theorem opNorm_higherLipschitzEmbedding_le :
    ‖higherLipschitzEmbedding (n := n) (k := k) (Ω := Ω)‖ ≤
      higherLipschitzDomainConstant (n := n) (Ω := Ω) := by
  refine ContinuousLinearMap.opNorm_le_bound _ higherLipschitzDomainConstant_nonneg fun U ↦ ?_
  rw [higherLipschitzEmbedding_apply]
  exact norm_higherLipschitzRepresentative_le U

/-- The endpoint inclusion is injective on the open atlas domain. -/
theorem higherLipschitzEmbedding_injective :
    Function.Injective (higherLipschitzEmbedding (n := n) (k := k) (Ω := Ω)) := by
  intro U V h
  apply wkpBaseCoordinateCLM_injective Boundary.C1ExtensionAtlas.isOpen
  apply Lp.ext
  have hU := higherLipschitzEmbedding_ae U
  have hV := higherLipschitzEmbedding_ae V
  rw [h] at hU
  exact hU.symm.trans hV

/-- Every compatible endpoint representative satisfies the same quantitative bound. -/
theorem norm_holderRepresentative_one_le (U : W^{k + 1,∞}(Ω))
    (F : CKGammaOn n k Ω 1)
    (hF : F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    ‖F‖ ≤ higherLipschitzDomainConstant (n := n) (Ω := Ω) * ‖U‖ := by
  have h : F = higherLipschitzRepresentative U :=
    CKGammaOn.ext_of_ae_eq Boundary.C1ExtensionAtlas.isOpen
      (hF.trans (higherLipschitzRepresentative_ae U).symm)
  rw [h]
  exact norm_higherLipschitzRepresentative_le U

/-- For `U ∈ W^{k+1,∞}(Ω)` and every representative `F ∈ C^{k,1}(Ω̄)` of `U`,
`F.evansNorm ≤ (N + N') * higherLipschitzDomainConstant * ‖U‖`, where `evansNorm` is the norm
(3) of Evans §5.1 and `N` and `N'` count the multi-indices of order at most `k` and of order
exactly `k`. -/
theorem evansNorm_holderRepresentative_one_le (U : W^{k + 1,∞}(Ω))
    (F : CKGammaOn n k Ω 1)
    (hF : F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    F.evansNorm ≤ (Fintype.card (MultiIndex n k) + Fintype.card (MultiIndex.Top n k) : ℝ) *
      higherLipschitzDomainConstant (n := n) (Ω := Ω) * ‖U‖ := by
  exact F.evansNorm_le.trans
    ((mul_le_mul_of_nonneg_left (norm_holderRepresentative_one_le U F hF)
      (by positivity)).trans_eq (mul_assoc _ _ _).symm)

/-- The endpoint and any strict Hölder representative are the same
function on the closure. Only the normed target has changed. -/
theorem higherLipschitzEmbedding_toBoundedContinuousFunction_eq
    {γ : Exponent} (U : W^{k + 1,∞}(Ω)) (F : CKGammaOn n k Ω γ)
    (hF : F.interiorDerivative 0 =ᵐ[domainMeasure n Ω] baseRepresentative U) :
    (higherLipschitzEmbedding U).toBoundedContinuousFunction = F.toBoundedContinuousFunction :=
  CKGammaOn.toBoundedContinuousFunction_eq_of_ae_eq Boundary.C1ExtensionAtlas.isOpen
    ((higherLipschitzEmbedding_ae U).trans hF.symm)

end SobolevSpace.Inequalities
