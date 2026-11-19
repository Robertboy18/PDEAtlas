/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.TransportCone

/-!
# Dilation identities on Euclidean balls

The vector field `u²(x-c)` converts a radial derivative moment into the square
trace on the boundary sphere. Its coefficients are smooth even at the centre,
so the identity needs no puncture or singular-weight limit argument.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set
open scoped RealInnerProductSpace

namespace PDE.Analysis

variable {n : ℕ} [Fact (0 < n)]

/-- Integrating the divergence of `u²(x-c)` gives the exact square-trace identity.
Only C¹ regularity is needed, and local integrability follows from continuity. -/
theorem ballIntegral_dilation_sq {u : ℝ^n → ℝ} (hu : ContDiff ℝ 1 u)
    (c : ℝ^n) {r : ℝ} (hr : 0 < r) :
    (n : ℝ) * ballIntegral n (fun y ↦ u y ^ 2) c r +
      2 * ballIntegral n (fun y ↦ u y * fderiv ℝ u y (y - c)) c r =
        r * sphereIntegral n (fun y ↦ u y ^ 2) c r := by
  let F : ℝ^n → ℝ^n := fun y ↦ u y ^ 2 • (y - c)
  have hF : ContDiff ℝ 1 F := (hu.pow 2).smul (contDiff_id.sub contDiff_const)
  have hradDeriv (y : ℝ^n) : HasFDerivAt (fun z : ℝ^n ↦ z - c)
      (ContinuousLinearMap.id ℝ (ℝ^n)) y := by
    simpa only [id_eq] using (hasFDerivAt_id y).sub_const c
  have hrad (y : ℝ^n) : ∇· (fun z : ℝ^n ↦ z - c) y = n := by
    rw [divergence_eq_trace_fderiv (hradDeriv y).differentiableAt, (hradDeriv y).fderiv]
    simp
  have hdiv (y : ℝ^n) : ∇· F y =
      2 * u y * fderiv ℝ u y (y - c) + u y ^ 2 * n := by
    have hs := ((hu.differentiable one_ne_zero y).hasFDerivAt.pow 2)
    rw [show F = (fun y ↦ u y ^ 2 • (y - c)) from rfl,
      divergence_smul hs.differentiableAt (hradDeriv y).differentiableAt,
      hs.fderiv, hrad]
    simp
  have hflux : sphereIntegral n (fun y ↦ ⟪F y, NormedSpace.normalize (y - c)⟫) c r =
      r * sphereIntegral n (fun y ↦ u y ^ 2) c r := by
    rw [← sphereIntegral_const_mul]
    apply sphereIntegral_congr_on_sphere hr
    intro y hy
    have hn : ‖y - c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hy
    simp only [F, real_inner_smul_left, NormedSpace.normalize, inner_smul_right,
      real_inner_self_eq_norm_sq, hn]
    field_simp
  have hint {v : ℝ^n → ℝ} (hv : Continuous v) : IntegrableOn v (ball c r) :=
    (hv.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
      ball_subset_closedBall
  have hiu : IntegrableOn (fun y ↦ u y ^ 2) (ball c r) :=
    hint (hu.continuous.pow 2)
  have him : IntegrableOn (fun y ↦ u y * fderiv ℝ u y (y - c)) (ball c r) :=
    hint (hu.continuous.mul
    ((hu.continuous_fderiv one_ne_zero).clm_apply (continuous_id.sub continuous_const)))
  have hid := ballIntegral_divergence_eq_sphereIntegral_inner_normal hF c hr
  rw [hflux] at hid
  have hf : (∇· F) = fun y ↦
      2 * (u y * fderiv ℝ u y (y - c)) + u y ^ 2 * (n : ℝ) := by
    funext y
    rw [hdiv]
    simp only [mul_assoc]
  rw [hf] at hid
  change (∫ y in ball c r,
    2 * (u y * fderiv ℝ u y (y - c)) + u y ^ 2 * (n : ℝ)) = _ at hid
  rw [integral_add (him.const_mul 2) (hiu.mul_const (n : ℝ)),
    integral_const_mul, integral_mul_const] at hid
  change _ * (∫ y in ball c r, u y ^ 2) +
    2 * (∫ y in ball c r, u y * fderiv ℝ u y (y - c)) = _
  simpa only [add_comm, mul_comm] using hid

end PDE.Analysis
