/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Inverse.Monotone
public import PDE.Analysis.Calculus.StrongConvex
public import PDE.Analysis.Calculus.Taylor.Local
public import PDE.Analysis.Convex.Differentiation.StrongConvexity
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax.Legendre.Derivative
import CAS.ExactTactic

/-!
# Quantitative bounds for the scalar Legendre transform

A lower bound on the second derivative of the original function gives
quadratic control of the maximizing state.
-/

@[expose] public noncomputable section

open Set PDE.Analysis

namespace HopfLax1D

/-- Uniform convexity of the original function bounds the maximizing state
quadratically in terms of the conjugate. The constant term is retained. -/
theorem quadratic_le_legendreTransform_deriv {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) {θ : ℝ} (hθ : 0 < θ)
    (hlower : ∀ r, θ ≤ deriv (deriv F) r) (u : ℝ) :
    θ / 2 * u ^ 2 ≤ legendreTransform F (deriv F u) + F 0 := by
  have hf := hF.differentiable (by norm_num)
  have hconv : ConvexOn ℝ univ F := convexOn_univ_of_deriv2_nonneg hf hF.differentiable_deriv_two
      (fun r ↦ hθ.le.trans (hlower r))
  have hFin : LegendreFinite F := legendreFinite_of_surjective_deriv hconv hf
    (surjective_of_deriv_lower_bound hF.differentiable_deriv_two hθ hlower)
  have hstrong : StrongConvexOn univ θ F := by
    have hdf : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    refine strongConvexOn_univ_of_hessian_lower_bound hf hdf.differentiable_one fun x v ↦ ?_
    have hD : fderiv ℝ F = fun r ↦ deriv F r • ContinuousLinearMap.id ℝ ℝ := by
      funext r
      refine ContinuousLinearMap.ext fun w ↦ ?_
      simp [mul_comm]
    have hDD := (hF.differentiable_deriv_two x).hasDerivAt.smul_const (ContinuousLinearMap.id ℝ ℝ)
    rw [hD, hDD.hasFDerivAt.fderiv]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, Real.norm_eq_abs, sq_abs]
    nlinarith [mul_le_mul_of_nonneg_right (hlower x) (sq_nonneg v)]
  have hsupport := Convex.fderiv_add_quadratic_le_sub_of_strongConvex
    hstrong (hf u).hasDerivAt.hasFDerivAt 0
  rw [legendreTransform_eq_of_convex_differentiable hFin hconv (hf u)]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
    zero_sub, norm_neg, Real.norm_eq_abs, sq_abs] at hsupport
  nlinarith only [hsupport]

/-- The conjugate has a cubic error relative to the quadratic approximation
at the zero state. The bound is local in the maximizing state, and follows
from C³ regularity of the original function, with no global upper Hessian
bound and no differentiability assumption on a supplied inverse. -/
theorem exists_abs_legendreTransform_deriv_sub_quadratic_le_cube {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    {θ : ℝ} (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : ℝ, |u| ≤ 1 → |legendreTransform F (deriv F u) + F 0 - (deriv F u - deriv F 0) ^ 2 / (2 *
        deriv (deriv F) 0)| ≤ C * |u| ^ 3 := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hf := hF2.differentiable (by norm_num)
  have hconv : ConvexOn ℝ univ F := convexOn_univ_of_deriv2_nonneg hf hF2.differentiable_deriv_two
      (fun r ↦ hθ.le.trans (hlower r))
  have hFin : LegendreFinite F := legendreFinite_of_surjective_deriv hconv hf
    (surjective_of_deriv_lower_bound hF2.differentiable_deriv_two hθ hlower)
  obtain ⟨A, hA, hlinear⟩ := exists_abs_sub_linear_le_sq (f := deriv F) hF.deriv'
  obtain ⟨B, hB, hquadratic⟩ := exists_abs_sub_quadratic_le_cube hF
  let d := deriv (deriv F) 0
  have hd : 0 < d := hθ.trans_le (hlower 0)
  refine ⟨B + A ^ 2 / (2 * d), by positivity, fun u hu ↦ ?_⟩
  let E := deriv F u - deriv F 0 - d * u
  let R := F u - F 0 - deriv F 0 * u - d / 2 * u ^ 2
  have hE : |E| ≤ A * u ^ 2 := hlinear u hu
  have hR : |R| ≤ B * |u| ^ 3 := hquadratic u hu
  have hE2 : E ^ 2 ≤ A ^ 2 * |u| ^ 4 := by
    calc
      E ^ 2 = |E| ^ 2 := (sq_abs E).symm
      _ ≤ (A * u ^ 2) ^ 2 := (sq_le_sq₀ (abs_nonneg E) (mul_nonneg hA (sq_nonneg u))).2 hE
      _ = A ^ 2 * |u| ^ 4 := by
        rw [show |u| ^ 4 = (u ^ 2) ^ 2 by rw [← sq_abs u]; cas]
        cas
  have hpow : |u| ^ 4 ≤ |u| ^ 3 := by
    simpa only [← pow_succ, mul_one] using
      mul_le_mul_of_nonneg_left hu (pow_nonneg (abs_nonneg u) 3)
  have hE3 : E ^ 2 ≤ A ^ 2 * |u| ^ 3 := hE2.trans (mul_le_mul_of_nonneg_left hpow (sq_nonneg A))
  have heq : legendreTransform F (deriv F u) + F 0 -
      (deriv F u - deriv F 0) ^ 2 / (2 * d) = -R - E ^ 2 / (2 * d) := by
    rw [legendreTransform_eq_of_convex_differentiable hFin hconv (hf u)]
    dsimp [E, R]
    field_simp
    cas
  change |legendreTransform F (deriv F u) + F 0 - (deriv F u - deriv F 0) ^ 2 / (2 * d)| ≤ _
  rw [heq]
  calc
    |-R - E ^ 2 / (2 * d)| ≤ |R| + E ^ 2 / (2 * d) := by
      have hnonneg : 0 ≤ E ^ 2 / (2 * d) := by positivity
      exact (abs_sub (-R) (E ^ 2 / (2 * d))).trans_eq
        (congrArg₂ (· + ·) (abs_neg R) (abs_of_nonneg hnonneg))
    _ ≤ B * |u| ^ 3 + A ^ 2 * |u| ^ 3 / (2 * d) :=
      add_le_add hR (div_le_div_of_nonneg_right hE3 (by positivity))
    _ = (B + A ^ 2 / (2 * d)) * |u| ^ 3 := by cas

/-- The conjugate has a cubic remainder near the zero-state velocity. The constructed
inverse is Lipschitz by uniform convexity of the original function; its differentiability
and a global upper bound on the original Hessian are unnecessary. -/
theorem exists_abs_legendreTransform_sub_quadratic_le_cube {F : ℝ → ℝ} (hF : ContDiff ℝ 3 F) {θ : ℝ}
    (hθ : 0 < θ) (hlower : ∀ r, θ ≤ deriv (deriv F) r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, |v - deriv F 0| ≤ θ → |legendreTransform F v + F 0 - (v - deriv F 0) ^
      2 / (2 * deriv (deriv F) 0)| ≤ C * |v - deriv F 0| ^ 3 := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  let e := orderIsoOfDerivLowerBound hF2.differentiable_deriv_two hθ hlower
  have hLip := lipschitzWith_orderIsoOfDerivLowerBound_symm hF2.differentiable_deriv_two hθ hlower
  have hinv (v : ℝ) : |e.symm v| ≤ |v - deriv F 0| / θ := by
    have h := hLip.dist_le_mul v (e 0)
    change dist (e.symm v) (e.symm (e 0)) ≤ θ⁻¹ * dist v (e 0) at h
    rw [e.symm_apply_apply, Real.dist_eq, sub_zero, Real.dist_eq] at h
    change |e.symm v| ≤ θ⁻¹ * |v - deriv F 0| at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  obtain ⟨C, hC, hbound⟩ := exists_abs_legendreTransform_deriv_sub_quadratic_le_cube hF hθ hlower
  refine ⟨C / θ ^ 3, by positivity, fun v hv ↦ ?_⟩
  have hsmall : |e.symm v| ≤ 1 := (hinv v).trans ((div_le_one hθ).2 hv)
  have hu : deriv F (e.symm v) = v := e.apply_symm_apply v
  have hb := hbound (e.symm v) hsmall
  rw [hu] at hb
  calc
    |legendreTransform F v + F 0 - (v - deriv F 0) ^ 2 / (2 * deriv (deriv F) 0)|
        ≤ C * |e.symm v| ^ 3 := hb
    _ ≤ C * (|v - deriv F 0| / θ) ^ 3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (hinv v) 3) hC
    _ = C / θ ^ 3 * |v - deriv F 0| ^ 3 := by cas

end HopfLax1D
