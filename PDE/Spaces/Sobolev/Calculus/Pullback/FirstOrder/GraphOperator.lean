/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.BoundedOperator
public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.Integrability

/-!
# Bounded pullback of first-order Sobolev jets

The full-chart `Lᵖ` pullback and bounded multiplication by the chart derivatives
give continuous operators for every coordinate of a first-order jet. The weak
chain rule places their tuple in the Sobolev graph. This construction
uses the derivative of the chart and applies to every exponent
`1 ≤ p ≤ ∞`, including dimension zero.
-/

@[expose] public noncomputable section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory Set GraphSpace
open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E : OpenPartialHomeomorph (ℝ^n) (ℝ^n)}

/-- A globally continuous inverse maps a bounded chart target into a bounded source. -/
theorem isBounded_source_of_isBounded_target
    (hSymm : Continuous (fun y ↦ E.symm y)) (hTarget : Bornology.IsBounded E.target) :
    Bornology.IsBounded E.source := by
  apply ((hTarget.isCompact_closure.image hSymm).isBounded).subset
  intro x hx
  exact ⟨E x, subset_closure (E.map_source hx), E.left_inv hx⟩

/-- The chart derivative coefficients are essentially bounded on the source. -/
theorem memLp_chartDerivative
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (i j : Fin n) :
    MemLp (fun x ↦ (∂[i] (fun z ↦ E z)) x j)
      ∞ (domainMeasure n E.source) := by
  apply memLp_top_on_bounded_of_continuous
    (isBounded_source_of_isBounded_target hSymm.continuous hTarget)
  exact (EuclideanSpace.proj j).continuous.comp
    ((hE.continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- A chart derivative coefficient as an essentially bounded multiplier on its source. -/
def derivativeCoefficient
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (i j : Fin n) : DerivLp n ∞ E.source :=
  (memLp_chartDerivative hE hSymm hTarget i j).toLp _

private theorem derivativeCoefficient_ae
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (i j : Fin n) :
    ⇑(derivativeCoefficient hE hSymm hTarget i j) =ᵐ[domainMeasure n E.source]
      fun x ↦ (∂[i] (fun z ↦ E z)) x j :=
  MemLp.coeFn_toLp _

/-- One chain-rule row of the bounded pullback, as a continuous linear operator. -/
def derivativePullbackCLM
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (i : Fin n) :
    W^{1,p}(E.target) →L[ℝ] DerivLp n p E.source :=
  ∑ j : Fin n, (mulLpLeft (derivativeCoefficient hE hSymm hTarget i j)).comp
    ((boundedPullbackCLM hE hSymm hTarget).comp
      (wkpCoordinateCLM (singleDerivIndex n j)))

private theorem derivativePullbackCLM_ae
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target)
    (U : W^{1,p}(E.target)) (i : Fin n) :
    ⇑(derivativePullbackCLM hE hSymm hTarget i U) =ᵐ[domainMeasure n E.source]
      fun x ↦ ∑ j : Fin n, U.val (singleDerivIndex n j) (E x) *
        (∂[i] (fun z ↦ E z)) x j := by
  let v (j : Fin n) : DerivLp n p E.source :=
    mulLpLeft (derivativeCoefficient hE hSymm hTarget i j)
      (boundedPullbackCLM hE hSymm hTarget (U.val (singleDerivIndex n j)))
  have hv (j : Fin n) : ⇑(v j) =ᵐ[domainMeasure n E.source]
      fun x ↦ U.val (singleDerivIndex n j) (E x) *
        (∂[i] (fun z ↦ E z)) x j := by
    filter_upwards [mulLpLeft_apply_ae (derivativeCoefficient hE hSymm hTarget i j)
      (boundedPullbackCLM hE hSymm hTarget (U.val (singleDerivIndex n j))),
      derivativeCoefficient_ae hE hSymm hTarget i j,
      boundedPullbackLp_apply_ae hE hSymm hTarget
        (U.val (singleDerivIndex n j))] with x hm hc hu
    exact hm.trans (by rw [hc, boundedPullbackCLM_apply, hu, mul_comm])
  have heq : derivativePullbackCLM hE hSymm hTarget i U = ∑ j : Fin n, v j := by
    simp only [derivativePullbackCLM, sum_apply, ContinuousLinearMap.comp_apply,
      wkpCoordinateCLM_apply, v]
  rw [heq]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ v, ae_all_iff.mpr hv] with x hs hx
  exact hs.trans (Finset.sum_congr rfl fun j _ ↦ hx j)

/-- The full first-order pullback tuple, before restricting to the weak-derivative graph. -/
def jetPullbackCLM
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) :
    W^{1,p}(E.target) →L[ℝ] WkpAmbientOn n 1 p E.source :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n 1 ↦ DerivLp n p E.source)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (firstOrderRows
        ((boundedPullbackCLM hE hSymm hTarget).comp wkpBaseCoordinateCLM)
        (derivativePullbackCLM hE hSymm hTarget)))

private theorem jetPullbackCLM_base
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (U : W^{1,p}(E.target)) :
    jetPullbackCLM hE hSymm hTarget U (baseIndex n 1) =
      boundedPullbackCLM hE hSymm hTarget (U.val (baseIndex n 1)) := by
  change firstOrderRows
    ((boundedPullbackCLM hE hSymm hTarget).comp wkpBaseCoordinateCLM)
    (derivativePullbackCLM hE hSymm hTarget) (baseIndex n 1) U = _
  rw [firstOrderRows_baseIndex]
  rfl

private theorem jetPullbackCLM_derivative
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (U : W^{1,p}(E.target)) (i : Fin n) :
    jetPullbackCLM hE hSymm hTarget U (singleDerivIndex n i) =
      derivativePullbackCLM hE hSymm hTarget i U := by
  change firstOrderRows
    ((boundedPullbackCLM hE hSymm hTarget).comp wkpBaseCoordinateCLM)
    (derivativePullbackCLM hE hSymm hTarget) (singleDerivIndex n i) U = _
  rw [firstOrderRows_singleDerivIndex]

/-- The coordinate pullback operators preserve the defining weak-derivative relations. -/
theorem jetPullbackCLM_mem
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (U : W^{1,p}(E.target)) :
    jetPullbackCLM hE hSymm hTarget U ∈ wkpSubmoduleOn n 1 p E.source := by
  intro a
  rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
  · simpa only [baseIndex_toList] using hasWeakDerivativeOn_nil
      (memLp_locallyIntegrableOn_domain
        (Lp.memLp (jetPullbackCLM hE hSymm hTarget U (baseIndex n 1))) Fact.out)
  · rw [singleDerivIndex_toList, jetPullbackCLM_base, jetPullbackCLM_derivative]
    have hw (j : Fin n) : HasWeakDerivativeOn E.target [j] (baseRepresentative U)
        (U.val (singleDerivIndex n j) : ℝ^n → ℝ) := by
      simpa only [singleDerivIndex_toList, baseRepresentative] using
        U.property (singleDerivIndex n j)
    have hchain := hasWeakDerivativeOn_comp_partialHomeomorph_W1_of_memLp
      (Approximation.standardMollifier n) hE hSymm hTarget.measure_lt_top.ne
      (Lp.memLp (U.val (baseIndex n 1)))
      (fun j ↦ Lp.memLp (U.val (singleDerivIndex n j))) hw i
    exact hchain.congr_ae
      (boundedPullbackLp_apply_ae hE hSymm hTarget (U.val (baseIndex n 1))).symm
      (derivativePullbackCLM_ae hE hSymm hTarget U i).symm

/-- Pullback through a bounded `C¹` chart as a continuous linear map of
first-order Sobolev spaces. The chart and inverse are globally `C¹`; the
partial-homeomorphism identities are used only on their domains. -/
def boundedW1pPullbackCLM
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) :
    W^{1,p}(E.target) →L[ℝ] W^{1,p}(E.source) :=
  (jetPullbackCLM hE hSymm hTarget).codRestrict (wkpSubmoduleOn n 1 p E.source)
    (jetPullbackCLM_mem hE hSymm hTarget)

/-- The base representative of the pullback is composition almost everywhere. -/
theorem boundedW1pPullbackCLM_base_ae
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (U : W^{1,p}(E.target)) :
    baseRepresentative (boundedW1pPullbackCLM hE hSymm hTarget U)
      =ᵐ[domainMeasure n E.source] fun x ↦ baseRepresentative U (E x) := by
  change ⇑(jetPullbackCLM hE hSymm hTarget U (baseIndex n 1))
    =ᵐ[domainMeasure n E.source] _
  rw [jetPullbackCLM_base]
  exact boundedPullbackLp_apply_ae hE hSymm hTarget _

/-- Every derivative coordinate satisfies the weak chain rule. -/
theorem boundedW1pPullbackCLM_derivative_ae
    (hE : ContDiff ℝ 1 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 1 (fun y ↦ E.symm y))
    (hTarget : Bornology.IsBounded E.target) (U : W^{1,p}(E.target)) (i : Fin n) :
    ⇑((boundedW1pPullbackCLM hE hSymm hTarget U).val (singleDerivIndex n i))
      =ᵐ[domainMeasure n E.source] fun x ↦ ∑ j : Fin n,
        U.val (singleDerivIndex n j) (E x) *
          (∂[i] (fun z ↦ E z)) x j := by
  change ⇑(jetPullbackCLM hE hSymm hTarget U (singleDerivIndex n i))
    =ᵐ[domainMeasure n E.source] _
  rw [jetPullbackCLM_derivative]
  exact derivativePullbackCLM_ae hE hSymm hTarget U i

end SobolevSpace.WeakChangeOfVariables
