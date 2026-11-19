/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Supersolution.ClassicalTruncation
public import PDE.Spaces.Sobolev.Calculus.Composition.C1DomainTruncation
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.Approximation.NonnegativeTests
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates

/-!
# Weak supersolutions from Sobolev truncation

The interval clamp has the original weak gradient strictly between its
two levels and zero gradient elsewhere. For a positive interior classical
representative, the compact-test truncation inequality therefore gives a weak
supersolution in `H¹`. Sign-preserving Sobolev density extends the inequality to
every nonnegative `H¹₀` test, as required by weak boundary comparison.
-/

@[expose] public noncomputable section

open PDE (partialDeriv laplacian iteratedPartialDeriv)

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
    [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The upper truncation of a positive `H¹` function is a weak supersolution
when its interior classical Laplacian is nonpositive below the truncation level. -/
theorem intervalTruncationOn_dirichlet_nonneg
    (U : W^{1,2}(Ω)) {b : ℝ^n → ℝ}
    (hbase : (U.val (baseIndex n 1) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] b)
    (hderiv : ∀ i : Fin n, (U.val (singleDerivIndex n i) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] ∂[i] b)
    (hb : ∀ x ∈ Ω, ContDiffAt ℝ 2 b x)
    (hb0 : ∀ x ∈ Ω, 0 < b x) {c : ℝ} (hc : 0 ≤ c)
    (hΔ : ∀ x ∈ Ω, b x < c → laplacian b x ≤ 0)
    (t : H¹₀(Ω))
    (ht : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM t x) :
    0 ≤ ∑ i : Fin n,
      inner ℝ (wkpCoordinateCLM (singleDerivIndex n i)
        (intervalTruncationOn (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hc U))
        (derivCoordCLM i t) := by
  let B := intervalTruncationOn (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hc U
  let ℓ : W^{1,2}(Ω) →L[ℝ] ℝ :=
    ∑ i : Fin n, (innerSL ℝ (wkpCoordinateCLM (singleDerivIndex n i) B)).comp
      (wkpCoordinateCLM (singleDerivIndex n i))
  have hB (i : Fin n) :
      (wkpCoordinateCLM (singleDerivIndex n i) B : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] fun x ↦ if b x < c then (∂[i] b) x else 0 := by
    filter_upwards
      [intervalTruncationOn_derivative_indicator_ae
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hc U i,
       hbase, hderiv i, self_mem_ae_restrict hΩ.isOpen.measurableSet]
      with x hx hbv hd hxΩ
    simpa only [wkpCoordinateCLM_apply, B, hbv, hd, hb0 x hxΩ, true_and] using hx
  have htest (φ : TestFunctionOn n Ω) (hφ0 : ∀ x, 0 ≤ φ.1.toFun x) :
      0 ≤ ℓ (testFunctionToWkp (k := 1) (p := 2) φ) := by
    have heq :
        ℓ (testFunctionToWkp (k := 1) (p := 2) φ) =
          ∑ i : Fin n, ∫ x,
            (if b x < c then (∂[i] b) x else 0) * (∂[i] φ.1.toFun) x := by
      simp only [ℓ, sum_apply, ContinuousLinearMap.comp_apply,
        innerSL_apply_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [MeasureTheory.L2.inner_def]
      calc
        _ = ∫ x, (if b x < c then (∂[i] b) x else 0) *
            (∂[i] φ.1.toFun) x ∂domainMeasure n Ω := by
          apply integral_congr_ae
          filter_upwards
            [hB i, testFunctionToWkp_coordinate_ae (k := 1) (p := 2) φ (singleDerivIndex n i)]
            with x hx hφ
          simp only [singleDerivIndex_toList, iteratedPartialDeriv] at hφ
          simp only [wkpCoordinateCLM_apply] at hx
          simp only [RCLike.inner_apply, conj_trivial, wkpCoordinateCLM_apply,
            hx, hφ, mul_comm]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
          have hxs : x ∉ tsupport φ.1.toFun := fun hs ↦ hx (φ.2 hs)
          simp only [partialDeriv, fderiv_of_notMem_tsupport ℝ hxs,
            zero_apply, mul_zero]
    rw [heq]
    exact PDE.Elliptic.integral_sublevel_gradient_nonneg
      (φ.1.contDiff.of_le (by simp)) φ.1.hasCompactSupport hφ0
      (fun x hx ↦ hb x (φ.2 hx)) c (fun x hx ↦ hΔ x (φ.2 hx))
  have h := nonneg_on_wkp0_of_nonneg_testFunctions hΩ.isOpen
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ℓ htest t ht
  simpa only [ℓ, sum_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, wkpCoordinateCLM_apply, derivCoordCLM_apply, B] using h

end SobolevSpace.GraphSpace
