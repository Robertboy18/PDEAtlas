/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.UnitBall
public import PDE.Analysis.MeasureTheory.Contact.Image
public import PDE.Elliptic.Classical.Harnack.Local.ContactJacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Low-level measure from quadratic contacts

A nonnegative supersolution with a small value in the half ball has a definite
amount of low-level mass in the unit ball. The contact set is compact, its image
covers a ball of vertices, and the differential inequality bounds its Jacobian.
All three facts are derived here from the solution and coefficient bounds.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis Set Metric MeasureTheory
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- A small value in the half ball forces low-level mass in the unit ball.
The coefficient bounds are pointwise, and no derivative of a coefficient occurs. -/
theorem measure_vertexBall_le_mul_measure_sublevel
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
    {u : ℝ^n → ℝ} {α τ B : ℝ} (hα : 0 < α)
    (hu : ContinuousOn u (closedBall 0 1))
    (hreg : ∀ x ∈ ball (0 : ℝ^n) 1, ContDiffAt ℝ 2 u x)
    (hnonneg : ∀ x ∈ closedBall (0 : ℝ^n) 1, 0 ≤ u x)
    (hell : ∀ x ∈ ball (0 : ℝ^n) 1, ∀ v : ℝ^n,
      α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫)
    (htrace : ∀ x ∈ ball (0 : ℝ^n) 1, (a x).trace ≤ τ)
    (hdrift : ∀ x ∈ ball (0 : ℝ^n) 1, ‖b x‖ ≤ B)
    (hsuper : ∀ x ∈ ball (0 : ℝ^n) 1,
      0 ≤ EllipticMaximum.matrixOperator a b (fun _ ↦ 0) u x)
    {x₀ : ℝ^n} (hx₀ : x₀ ∈ closedBall (0 : ℝ^n) (1 / 2)) (hsmall : u x₀ ≤ 1) :
    volume (closedBall x₀ (1 / 8)) ≤
      ENNReal.ofReal (((τ + B * 2) / α) ^ n) *
        volume (ball (0 : ℝ^n) 1 ∩ {x | u x ≤ 5 / 4}) := by
  let S := quadraticContactSet u 32 (closedBall 0 1) (closedBall 0 (15 / 16))
    (closedBall x₀ (1 / 8))
  have hinside {x : ℝ^n} (hx : x ∈ closedBall (0 : ℝ^n) (15 / 16)) :
      x ∈ ball (0 : ℝ^n) 1 :=
    closedBall_subset_ball (by norm_num) hx
  have hcompact : IsCompact S :=
    isCompact_quadraticContactSet (isCompact_closedBall _ _) isClosed_closedBall
      (hu.mono (closedBall_subset_closedBall (by norm_num)))
      (fun x hx ↦
        (contDiffAt_gradient (m := 1) (hreg x (hinside hx))).continuousAt.continuousWithinAt)
  have hcover : closedBall x₀ (1 / 8) ⊆ quadraticContactMap u 32 '' S :=
    closedBall_subset_image_quadraticContactMap hu
      (fun x hx ↦ ((hreg x hx).differentiableAt (by norm_num)).differentiableWithinAt)
      hnonneg hx₀ hsmall
  have hderiv : ∀ x ∈ S, HasFDerivWithinAt (quadraticContactMap u 32)
      (fderiv ℝ (quadraticContactMap u 32) x) S x := by
    intro x hx
    have hd := (hasFDerivAt_quadraticContactMap (hreg x (hinside hx.1)) 32).differentiableAt
    exact hd.hasFDerivAt.hasFDerivWithinAt
  have hdet : ∀ x ∈ S, |(fderiv ℝ (quadraticContactMap u 32) x).det| ≤
      ((τ + B * 2) / α) ^ n := by
    intro x hx
    have hxunit := hinside hx.1
    have hxnorm : ‖x‖ ≤ 15 / 16 := by simpa using hx.1
    have hx₀norm : ‖x₀‖ ≤ 1 / 2 := by simpa using hx₀
    have hynear : ‖quadraticContactMap u 32 x - x₀‖ ≤ 1 / 8 := by
      simpa only [mem_closedBall, dist_eq_norm] using hx.2.1
    have hynorm : ‖quadraticContactMap u 32 x‖ ≤ 5 / 8 := by
      have ht := norm_add_le (quadraticContactMap u 32 x - x₀) x₀
      rw [sub_add_cancel] at ht
      linarith
    have hdist : ‖quadraticContactMap u 32 x - x‖ ≤ 2 := by
      have ht := norm_sub_le (quadraticContactMap u 32 x) x
      linarith
    simpa only [mul_zero, add_zero] using
      abs_det_fderiv_quadraticContactMap_le a b (f := 0) (hreg x hxunit)
      (by norm_num : (0 : ℝ) < 32) hα (hell x hxunit) (htrace x hxunit)
      (hdrift x hxunit) hdist (by simpa only [neg_zero] using hsuper x hxunit)
      (isLocalMin_quadraticTilt_of_mem_contactSet hx (closedBall_mem_nhds_of_mem hxunit))
  apply (measure_le_mul_measure_of_subset_differentiable_image volume
    hcompact.measurableSet hderiv hcover hdet).trans
  gcongr
  exact quadraticContactSet_unitBall_subset_sublevel hx₀ hsmall

end EllipticHarnack
