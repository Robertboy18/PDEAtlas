/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.HalfSpace.Reflection.HigherOrder.DilationLp
public import PDE.DistributionTheory.TestFunction.ProperPrecomposition

/-!
# Weak derivatives under reflected normal dilation

Change of variables transfers a weak derivative of any finite order from the upper
to the lower half-space. Each occurrence of the normal direction contributes the
normal scale. This is an interior weak chain rule: neither trace regularity nor a
global extension operator is assumed.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open Set MeasureTheory TopologicalSpace
open scoped ENNReal Distributions

variable (n : ℕ) [Fact (0 < n)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Change of variables for a pulled-back coordinate paired with a scalar function. -/
theorem integral_dilationPullbackLp_mul (a : ℝ) (ha : a < 0)
    (u : DerivLp n p ℝ^n₊) (ψ : ℝ^n → ℝ) :
    (∫ x, dilationPullbackLp n p a ha u x * ψ x ∂domainMeasure n ℝ^n₋) =
      |a⁻¹| * ∫ y, u y *
        ψ (normalDilation (PDE.Common.lastIndex (n := n)) a⁻¹ y)
          ∂domainMeasure n ℝ^n₊ := by
  let e := normalDilationEquiv (PDE.Common.lastIndex (n := n)) a ha.ne
  have hm := integral_map_equiv e.toHomeomorph.toMeasurableEquiv
    (μ := domainMeasure n ℝ^n₋) (fun y ↦ u y * ψ (e.symm y))
  have he : (e.symm : ℝ^n → ℝ^n) = normalDilation
      (PDE.Common.lastIndex (n := n)) a⁻¹ := rfl
  change (∫ y, u y * ψ (e.symm y) ∂Measure.map
      (normalDilation (PDE.Common.lastIndex (n := n)) a) (domainMeasure n ℝ^n₋)) =
    ∫ x, u (e x) * ψ (e.symm (e x)) ∂domainMeasure n ℝ^n₋ at hm
  rw [map_lower_normalDilation n a ha, integral_smul_measure] at hm
  simp only [ContinuousLinearEquiv.symm_apply_apply, ENNReal.toReal_ofReal (abs_nonneg _),
    smul_eq_mul, he] at hm
  refine (integral_congr_ae ?_).trans hm.symm
  filter_upwards [dilationPullbackLp_apply_ae n p a ha u] with x hx
  exact congrArg (fun t ↦ t * ψ x) hx

/-- Every mixed weak derivative transforms with the corresponding normal power.
This theorem concerns the two open half-spaces, so it imposes no boundary condition. -/
theorem hasWeakDerivativeOn_dilationPullbackLp (a : ℝ) (ha : a < 0)
    (u du : DerivLp n p ℝ^n₊) (α : List (Fin n))
    (hweak : HasWeakDerivativeOn ℝ^n₊ α (u : ℝ^n → ℝ) (du : ℝ^n → ℝ)) :
    HasWeakDerivativeOn ℝ^n₋ α (dilationPullbackLp n p a ha u : ℝ^n → ℝ)
      ((a ^ α.count (PDE.Common.lastIndex (n := n)) •
        dilationPullbackLp n p a ha du : DerivLp n p ℝ^n₋) : ℝ^n → ℝ) := by
  refine ⟨memLp_locallyIntegrableOn_domain (Lp.memLp _) Fact.out,
    memLp_locallyIntegrableOn_domain (Lp.memLp _) Fact.out, ?_⟩
  intro φ hφ
  let i := PDE.Common.lastIndex (n := n)
  let e := normalDilationEquiv i a ha.ne
  let θ := TestFunction.precompProper (e.symm : ℝ^n → ℝ^n)
    e.symm.contDiff e.symm.toHomeomorph.isProperMap φ
  have hθ : tsupport θ.toFun ⊆ ℝ^n₊ := by
    intro x hx
    have hxlower : e.symm x ∈ ℝ^n₋ :=
      hφ (tsupport_comp_subset_preimage φ e.symm.continuous hx)
    rw [← preimage_upper_normalDilation n a ha] at hxlower
    change e (e.symm x) ∈ ℝ^n₊ at hxlower
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hxlower
  have hcomp : (fun x ↦ θ (normalDilation i a x)) = (φ : ℝ^n → ℝ) := by
    funext x
    exact congrArg φ (e.symm_apply_apply x)
  have hder : ∀ y, iteratedPartialDeriv α φ.toFun (e.symm y) =
      a ^ α.count i * iteratedPartialDeriv α θ.toFun y := by
    have hc := iteratedPartialDeriv_comp_normalDilation i a
      (k := α.length) (θ.contDiff.of_le (by simp)) α le_rfl
    rw [hcomp] at hc
    intro y
    have hc' := congrFun hc (e.symm y)
    change iteratedPartialDeriv α φ.toFun (e.symm y) =
      a ^ α.count i * iteratedPartialDeriv α θ.toFun (e (e.symm y)) at hc'
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hc'
  have hw := hweak θ hθ
  have hsmul :
      (∫ x, ((a ^ α.count (PDE.Common.lastIndex (n := n)) •
          dilationPullbackLp n p a ha du :
          DerivLp n p ℝ^n₋) : ℝ^n → ℝ) x * φ.toFun x ∂domainMeasure n ℝ^n₋) =
        a ^ α.count i * ∫ x, dilationPullbackLp n p a ha du x * φ.toFun x
          ∂domainMeasure n ℝ^n₋ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul (a ^ α.count i) (dilationPullbackLp n p a ha du)]
      with x hx
    change ((a ^ α.count i • dilationPullbackLp n p a ha du :
        DerivLp n p ℝ^n₋) : ℝ^n → ℝ) x * φ.toFun x =
      a ^ α.count i * (dilationPullbackLp n p a ha du x * φ.toFun x)
    simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [hsmul, integral_dilationPullbackLp_mul, integral_dilationPullbackLp_mul]
  change |a⁻¹| * (∫ y, u y * iteratedPartialDeriv α φ.toFun (e.symm y)
      ∂domainMeasure n ℝ^n₊) =
    (-1) ^ α.length * (a ^ α.count i *
      (|a⁻¹| * ∫ y, du y * θ.toFun y ∂domainMeasure n ℝ^n₊))
  simp_rw [hder]
  have hi : (∫ y, u y * (a ^ α.count i * iteratedPartialDeriv α θ.toFun y)
      ∂domainMeasure n ℝ^n₊) =
      a ^ α.count i * ∫ y, u y * iteratedPartialDeriv α θ.toFun y
        ∂domainMeasure n ℝ^n₊ := by
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  rw [hi, hw]
  ring

end SobolevSpace.GraphSpace.HigherOrderReflection
