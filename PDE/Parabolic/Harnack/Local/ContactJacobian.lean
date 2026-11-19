/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.WeightedHessian
public import PDE.Analysis.Calculus.Contact.Parabolic.Jacobian
public import PDE.Analysis.LinearAlgebra.PositiveDeterminant
public import PDE.Parabolic.MaximumPrinciple.MatrixOperator
import CAS.ExactTactic

/-!
# Parabolic contact Jacobians controlled by the parabolic residual

At an earlier-time lower contact, the spatial contact Jacobian is positive and
the scalar time factor is nonnegative. The supersolution inequality
bounds their weighted trace sum by `τ + B R + κ⁻¹ f + 1`. The determinant
bound therefore uses only ellipticity, trace and drift bounds, the aperture,
and the forcing. No derivative of a coefficient enters the estimate.
-/

open scoped Gradient

@[expose] public noncomputable section

namespace ParabolicHarnack

open PDE.Analysis Set
open scoped Topology RealInnerProductSpace

variable {n : ℕ}

/-- The weighted spatial trace and the time factor are bounded together.
The time derivative cancels, so the bound does not depend on `uₜ`. -/
theorem weighted_trace_contact_add_time_le
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ → ℝ^n)
    {u : ℝ^n → ℝ → ℝ} {p v : ℝ^n × ℝ} {S : Set (ℝ^n)}
    {κ α τ B R f t₀ : ℝ}
    (hu : ContDiffAt ℝ 2 (fun x ↦ u x p.2) p.1) (hκ : 0 < κ)
    (hell : ∀ z : ℝ^n, α * ‖z‖ ^ 2 ≤ ⟪z, (a p.1 p.2).toEuclideanLin z⟫)
    (htrace : (a p.1 p.2).trace ≤ τ) (hdrift : ‖b p.1 p.2‖ ≤ B)
    (hdist : ‖v.1 - p.1‖ ≤ R)
    (hsuper : -f ≤ ParabolicMaximum.matrixParabolicOperator a b (fun _ _ ↦ 0) u p.1 p.2)
    (ht : t₀ ≤ p.2) (hS : S ∈ 𝓝 p.1)
    (hzero : parabolicQuadraticTilt u κ v p = 0)
    (hsupport : ∀ q ∈ S ×ˢ Icc t₀ p.2, 0 ≤ parabolicQuadraticTilt u κ v q) :
    α * LinearMap.trace ℝ (ℝ^n)
        (fderiv ℝ (quadraticContactMap (fun x ↦ u x p.2) κ) p.1).toLinearMap +
      (1 - κ⁻¹ * deriv (u p.1) p.2) ≤ τ + B * R + κ⁻¹ * f + 1 := by
  have hres : LinearMap.trace ℝ (ℝ^n)
      ((a p.1 p.2).toEuclideanLin.comp
        (fderiv ℝ (∇ (fun x ↦ u x p.2)) p.1).toLinearMap) ≤
      fderiv ℝ (fun x ↦ u x p.2) p.1 (b p.1 p.2) + (f + deriv (u p.1) p.2) := by
    unfold ParabolicMaximum.matrixParabolicOperator at hsuper
    rw [EllipticMaximum.matrixOperator_eq_neg_trace _ _ _ hu] at hsuper
    simp only [zero_mul, add_zero] at hsuper
    linarith
  have h := mul_trace_fderiv_quadraticContactMap_le
    (a p.1 p.2).toEuclideanLin (b p.1 p.2) hu hκ hell
    (by simpa only [trace_toEuclideanLin] using htrace) hdrift hdist hres
    (isLocalMin_spatialTilt_of_parabolic_support ht hS hzero hsupport)
  rw [mul_add] at h
  linarith

/-- Earlier support gives an upper bound on the parabolic residual at a
contact. A strictly larger residual therefore excludes the point from any
contact set. This statement only uses two spatial and one time derivative. -/
theorem matrixParabolicOperator_le_of_parabolic_support
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ → ℝ^n)
    {u : ℝ^n → ℝ → ℝ} {p v : ℝ^n × ℝ} {S : Set (ℝ^n)}
    {κ α τ B R t₀ : ℝ}
    (hus : ContDiffAt ℝ 2 (fun x ↦ u x p.2) p.1)
    (hut : DifferentiableAt ℝ (u p.1) p.2) (hκ : 0 < κ) (hα : 0 ≤ α)
    (hell : ∀ z : ℝ^n, α * ‖z‖ ^ 2 ≤ ⟪z, (a p.1 p.2).toEuclideanLin z⟫)
    (htrace : (a p.1 p.2).trace ≤ τ) (hdrift : ‖b p.1 p.2‖ ≤ B)
    (hdist : ‖v.1 - p.1‖ ≤ R) (ht : t₀ < p.2) (hS : S ∈ 𝓝 p.1)
    (hzero : parabolicQuadraticTilt u κ v p = 0)
    (hsupport : ∀ q ∈ S ×ˢ Icc t₀ p.2, 0 ≤ parabolicQuadraticTilt u κ v q) :
    ParabolicMaximum.matrixParabolicOperator a b (fun _ _ ↦ 0) u p.1 p.2 ≤
      κ * (τ + B * R + 1) := by
  have hpositive := isPositive_spatialContact_of_parabolic_support hκ ht.le hS hus hzero hsupport
  have htime := deriv_time_le_of_parabolic_support ht (mem_of_mem_nhds hS) hut hzero hsupport
  have hfactor : 0 ≤ 1 - κ⁻¹ * deriv (u p.1) p.2 := by
    have h := mul_le_mul_of_nonneg_left htime (inv_nonneg.mpr hκ.le)
    rw [inv_mul_cancel₀ hκ.ne'] at h
    exact sub_nonneg.mpr h
  let f := -ParabolicMaximum.matrixParabolicOperator a b (fun _ _ ↦ 0) u p.1 p.2
  have hbound := weighted_trace_contact_add_time_le a b hus hκ hell htrace hdrift hdist
    (show -f ≤ ParabolicMaximum.matrixParabolicOperator a b (fun _ _ ↦ 0) u p.1 p.2 by
      simp only [f, neg_neg, le_refl]) ht.le hS hzero hsupport
  have hnonneg : 0 ≤ τ + B * R + κ⁻¹ * f + 1 :=
    (add_nonneg (mul_nonneg hα hpositive.trace_nonneg) hfactor).trans hbound
  have hscaled := mul_nonneg hκ.le hnonneg
  have hcancel : κ * (τ + B * R + κ⁻¹ * f + 1) = κ * (τ + B * R + 1) + f := by
    cas
  rw [hcancel] at hscaled
  dsimp [f] at hscaled
  linarith

/-- The smooth parabolic contact map has a uniformly bounded absolute
Jacobian. Positivity of both determinant factors is derived from support,
and the spatial dimension may be zero. -/
theorem abs_det_fderiv_parabolicQuadraticContactMap_le
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ → ℝ^n)
    {u : ℝ^n → ℝ → ℝ} {p v : ℝ^n × ℝ} {S : Set (ℝ^n)}
    {κ α τ B R f t₀ : ℝ}
    (hu : DifferentiableAt ℝ (Function.uncurry u) p)
    (hg : DifferentiableAt ℝ
      (fun q : ℝ^n × ℝ ↦ ∇ (fun x ↦ u x q.2) q.1) p)
    (hus : ContDiffAt ℝ 2 (fun x ↦ u x p.2) p.1)
    (hκ : 0 < κ) (hα : 0 < α)
    (hell : ∀ z : ℝ^n, α * ‖z‖ ^ 2 ≤ ⟪z, (a p.1 p.2).toEuclideanLin z⟫)
    (htrace : (a p.1 p.2).trace ≤ τ) (hdrift : ‖b p.1 p.2‖ ≤ B)
    (hdist : ‖v.1 - p.1‖ ≤ R)
    (hsuper : -f ≤ ParabolicMaximum.matrixParabolicOperator a b (fun _ _ ↦ 0) u p.1 p.2)
    (ht : t₀ < p.2) (hS : S ∈ 𝓝 p.1)
    (hzero : parabolicQuadraticTilt u κ v p = 0)
    (hsupport : ∀ q ∈ S ×ˢ Icc t₀ p.2, 0 ≤ parabolicQuadraticTilt u κ v q) :
    |(fderiv ℝ (parabolicQuadraticContactMap u κ) p).det| ≤
      ((τ + B * R + κ⁻¹ * f + 1) / α) ^ n * (τ + B * R + κ⁻¹ * f + 1) := by
  have hpositive := isPositive_spatialContact_of_parabolic_support hκ ht.le hS hus hzero hsupport
  have hut : DifferentiableAt ℝ (u p.1) p.2 := by
    have h := (hu.hasFDerivAt.comp p.2
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).differentiableAt
    simpa only [Function.comp_def, Function.uncurry] using h
  have htime := deriv_time_le_of_parabolic_support ht (mem_of_mem_nhds hS) hut hzero hsupport
  have hfactor : 0 ≤ 1 - κ⁻¹ * deriv (u p.1) p.2 := by
    have h := mul_le_mul_of_nonneg_left htime (inv_nonneg.mpr hκ.le)
    rw [inv_mul_cancel₀ hκ.ne'] at h
    exact sub_nonneg.mpr h
  have hbound := weighted_trace_contact_add_time_le a b hus hκ hell htrace hdrift hdist
    hsuper ht.le hS hzero hsupport
  rw [det_fderiv_parabolicQuadraticContactMap hu hg κ]
  simpa only [finrank_euclideanSpace_fin] using
    abs_det_mul_le_of_trace_add_le hpositive hα hfactor hbound

end ParabolicHarnack
