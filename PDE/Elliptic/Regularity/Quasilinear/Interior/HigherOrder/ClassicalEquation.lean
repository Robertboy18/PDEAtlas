/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.ClassicalSolution
public import PDE.Elliptic.Regularity.Interior.Schauder.Reconstruction.FluxEquation
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalToWeak
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Classical Euler–Lagrange equation for the regular representative

The C² representative obtained from the nonlinear De Giorgi–Schauder
argument solves the pointwise equation `-div(∇L(Du)) = 0`.
Weak derivative uniqueness identifies its classical gradient with the
input H¹ gradient. The C¹ nonlinear flux then recovers the pointwise
equation from the original test-function identity.

This is the homogeneous autonomous C² stage of the interior regularity
argument in Evans, §8.3.2, in dimension greater than two.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis
open scoped ENNReal NNReal RealInnerProductSpace Sobolev Gradient

namespace PDE.Elliptic.Regularity.Quasilinear

variable {n : ℕ} {Ω : Set ℝ^n}

/-- Any C² representative of a nonlinear weak solution has the same
gradient almost everywhere and solves its pointwise equation. This
identification itself requires no ellipticity. -/
theorem neg_divergence_gradientDensity_eq_zero_of_representative
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ 2 L) {Λ : ℝ≥0}
    (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    (u : H¹(Ω))
    (hu : ∀ v : H¹₀(Ω),
      (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0)
    {v : ℝ^n → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (hva : v =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM u) :
    (∇ v : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] ∇ u ∧
      ∀ x ∈ Ω, -(PDE.divergence (fun y ↦ ∇ L (∇ v y)) x) = 0 := by
  have hdu (i : Fin n) :
      (wkpCoordinateCLM (singleDerivIndex n i) u : ℝ^n → ℝ) =ᵐ[
        domainMeasure n Ω] ∂[i] v := by
    have hw : HasWeakDerivativeOn Ω [i] (wkpBaseCoordinateCLM u)
        (wkpCoordinateCLM (singleDerivIndex n i) u) := by
      simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply]
        using u.property.hasWeakDerivativeOn_first (by norm_num) i
    exact (hw.congr_ae hva.symm Filter.EventuallyEq.rfl).unique_ae hΩ
      (hasWeakDerivativeOn_of_contDiffAt_one hΩ
        (fun x hx ↦ (hv.contDiffAt (hΩ.mem_nhds hx)).of_le (by norm_num)) i)
  have hgrad : (∇ v : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] ∇ u := by
    filter_upwards [ae_all_iff.mpr hdu, wkpGradientCLM_apply_ae u] with x hx hu
    exact PiLp.ext fun i ↦ (gradient_apply_eq_partialDeriv v x i).trans
      ((hx i).symm.trans (hu i).symm)
  have hvg : ContDiffOn ℝ 1 (∇ v) Ω := by
    apply contDiffOn_piLp' 2
    intro i x hx
    simpa only [gradient_apply_eq_partialDeriv, Nat.cast_one] using
      (contDiffAt_partialDeriv 1 (hv.contDiffAt (hΩ.mem_nhds hx)) i).contDiffWithinAt
  obtain ⟨q, hq, hpair⟩ := exists_L2_flux_pairing_of_lipschitz hb
    (lipschitzWith_gradient_of_hessian_bound hL hbound) u
  refine ⟨hgrad, neg_divergence_eq_of_flux_pairing hΩ q 0 ?_
    ((contDiff_gradient_of_contDiff_two hL).comp_contDiffOn hvg) ?_
    continuousOn_const ?_⟩
  · intro w
    rw [← (hpair w).2, hu w, inner_zero_left]
  · intro i
    filter_upwards [hq, Lp.euclideanTuple_apply_ae q, hgrad] with x hqx htx hgx
    exact (htx i).symm.trans
      (congrArg (fun p : ℝ^n ↦ p i) (hqx.symm.trans (congrArg (∇ L) hgx.symm)))
  · exact Lp.coeFn_zero _ _ _

/-- Raw H¹ homogeneous Euler–Lagrange solutions have C² representatives
which solve the classical equation at every interior point. No regularity
of the input gradient or the boundary is assumed. -/
theorem exists_classical_solution_of_gradientDensity
    [Fact (0 < n)] {q : ℝ≥0∞} (hq2 : 2 < q)
    (hq : q ≤ (if 2 < n then Inequalities.pStar n 2 else 4 : ℝ≥0))
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    {L : ℝ^n → ℝ} (hL : ContDiff ℝ 3 L) {Λ : ℝ≥0}
    (hbound : ∀ p, ‖fderiv ℝ (fderiv ℝ L) p‖ ≤ Λ)
    {θ : ℝ} (hθ : 0 < θ)
    (hpos : ∀ p z, θ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) p z z)
    (u : H¹(Ω))
    (hu : ∀ v : H¹₀(Ω),
      (∫ x, ⟪∇ L (∇ u x), ∇ (v : H¹(Ω)) x⟫ ∂domainMeasure n Ω) = 0) :
    ∃ v : ℝ^n → ℝ, ContDiffOn ℝ 2 v Ω ∧
      v =ᵐ[domainMeasure n Ω] wkpBaseCoordinateCLM u ∧
      (∇ v : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] ∇ u ∧
      ∀ x ∈ Ω, -(PDE.divergence (fun y ↦ ∇ L (∇ v y)) x) = 0 := by
  obtain ⟨v, hv, hva⟩ := exists_contDiffOn_two_representative_of_gradientDensity
    hq2 hq hΩ hb hL hbound hθ hpos u hu
  exact ⟨v, hv, hva, neg_divergence_gradientDensity_eq_zero_of_representative
    hΩ hb (hL.of_le (by norm_num)) hbound u hu hv hva⟩

end PDE.Elliptic.Regularity.Quasilinear
