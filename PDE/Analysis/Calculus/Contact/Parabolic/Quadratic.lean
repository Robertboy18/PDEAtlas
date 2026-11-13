/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.Hessian
public import PDE.Analysis.Calculus.LocalExtrema
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Quadratic contacts supported over earlier times

A rising paraboloid has the form `κ (t - s) - κ / 2 * ‖x - y‖²`.
At a contact supported over earlier times, the spatial derivative determines
`y`, the value determines `s`, and the time derivative is at most `κ`.
The spatial Hessian of the tilted function is positive semidefinite.

The differential conclusions require two spatial derivatives and one time
derivative, without a mixed derivative or a second time derivative.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The gap between a function and a rising paraboloid with vertex `(y,s)`. -/
def parabolicQuadraticTilt (u : E → ℝ → ℝ) (κ : ℝ) (v p : E × ℝ) : ℝ :=
  quadraticTilt (fun x ↦ u x p.2) κ v.1 p.1 - κ * (p.2 - v.2)

/-- The spatial contact map and the height equation recover the paraboloid's
space and time vertex. -/
def parabolicQuadraticContactMap (u : E → ℝ → ℝ) (κ : ℝ) (p : E × ℝ) : E × ℝ :=
  let y := quadraticContactMap (fun x ↦ u x p.2) κ p.1
  (y, p.2 - κ⁻¹ * quadraticTilt (fun x ↦ u x p.2) κ y p.1)

/-- Contacts in `K` whose vertices lie in `Y`, supported on all spatial points
of `S` and times between `a` and the contact time. -/
def parabolicQuadraticContactSet (u : E → ℝ → ℝ) (κ a : ℝ)
    (S : Set E) (K Y : Set (E × ℝ)) : Set (E × ℝ) :=
  {p | p ∈ K ∧ parabolicQuadraticContactMap u κ p ∈ Y ∧
    ∀ q ∈ S ×ˢ Icc a p.2,
      0 ≤ parabolicQuadraticTilt u κ (parabolicQuadraticContactMap u κ p) q}

/-- A contact vertex makes the gap vanish at the contact point. -/
theorem parabolicQuadraticTilt_contactMap (u : E → ℝ → ℝ) {κ : ℝ} (hκ : κ ≠ 0)
    (p : E × ℝ) :
    parabolicQuadraticTilt u κ (parabolicQuadraticContactMap u κ p) p = 0 := by
  dsimp [parabolicQuadraticTilt, parabolicQuadraticContactMap]
  rw [sub_sub_cancel, ← mul_assoc, mul_inv_cancel₀ hκ, one_mul, sub_self]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A spatially interior lower contact is a local minimum of the spatial tilt. -/
theorem isLocalMin_spatialTilt_of_parabolic_support
    {u : E → ℝ → ℝ} {κ a : ℝ} {S : Set E} {p v : E × ℝ}
    (ha : a ≤ p.2) (hS : S ∈ 𝓝 p.1)
    (hzero : parabolicQuadraticTilt u κ v p = 0)
    (hsupport : ∀ q ∈ S ×ˢ Icc a p.2, 0 ≤ parabolicQuadraticTilt u κ v q) :
    IsLocalMin (quadraticTilt (fun x ↦ u x p.2) κ v.1) p.1 := by
  refine (show IsMinOn (quadraticTilt (fun x ↦ u x p.2) κ v.1) S p.1 from ?_).isLocalMin hS
  intro x hx
  change quadraticTilt (fun x ↦ u x p.2) κ v.1 p.1 ≤
    quadraticTilt (fun x ↦ u x p.2) κ v.1 x
  have h := hsupport (x, p.2) ⟨hx, ha, le_rfl⟩
  dsimp [parabolicQuadraticTilt] at h hzero
  linarith

/-- A first contact recovers its full vertex from the spatial gradient and
the value equation. -/
theorem parabolicQuadraticContactMap_eq_of_support
    {u : E → ℝ → ℝ} {κ a : ℝ} {S : Set E} {p v : E × ℝ}
    (hκ : κ ≠ 0) (ha : a ≤ p.2) (hS : S ∈ 𝓝 p.1)
    (hu : DifferentiableAt ℝ (fun x ↦ u x p.2) p.1)
    (hzero : parabolicQuadraticTilt u κ v p = 0)
    (hsupport : ∀ q ∈ S ×ˢ Icc a p.2, 0 ≤ parabolicQuadraticTilt u κ v q) :
    parabolicQuadraticContactMap u κ p = v := by
  have hy := quadraticContactMap_eq_of_isLocalMin hκ hu
    (isLocalMin_spatialTilt_of_parabolic_support ha hS hzero hsupport)
  apply Prod.ext
  · exact hy
  · dsimp [parabolicQuadraticContactMap]
    rw [hy]
    have heq : quadraticTilt (fun x ↦ u x p.2) κ v.1 p.1 = κ * (p.2 - v.2) :=
      sub_eq_zero.mp hzero
    rw [heq, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul, sub_sub_cancel]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Earlier support gives the time derivative bound at a contact. Only a
first time derivative is used, including when the contact is at the top face. -/
theorem deriv_time_le_of_parabolic_support
    {u : E → ℝ → ℝ} {κ a : ℝ} {S : Set E} {p v : E × ℝ}
    (ha : a < p.2) (hx : p.1 ∈ S) (hu : DifferentiableAt ℝ (u p.1) p.2)
    (hzero : parabolicQuadraticTilt u κ v p = 0)
    (hsupport : ∀ q ∈ S ×ˢ Icc a p.2, 0 ≤ parabolicQuadraticTilt u κ v q) :
    deriv (u p.1) p.2 ≤ κ := by
  let f := fun t ↦ parabolicQuadraticTilt u κ v (p.1, t)
  have hf : HasDerivAt f (deriv (u p.1) p.2 - κ) p.2 := by
    have h := (hu.hasDerivAt.add_const (κ / 2 * ‖p.1 - v.1‖ ^ 2)).fun_sub
      (((hasDerivAt_id p.2).sub_const v.2).const_mul κ)
    simpa only [f, parabolicQuadraticTilt, quadraticTilt, id_eq, mul_one] using h
  have hmin : IsMinOn f (Icc a p.2) p.2 := by
    intro t ht
    change parabolicQuadraticTilt u κ v p ≤ _
    rw [hzero]
    exact hsupport (p.1, t) ⟨hx, ht⟩
  have h := hmin.deriv_nonpos_of_left_lt ha le_rfl hf.differentiableAt
  rw [hf.deriv] at h
  exact sub_nonpos.mp h

/-- The spatial contact Jacobian is positive at a spatially interior parabolic
contact. No spacetime Hessian is required. -/
theorem isPositive_spatialContact_of_parabolic_support
    {u : E → ℝ → ℝ} {κ a : ℝ} {S : Set E} {p v : E × ℝ}
    (hκ : 0 < κ) (ha : a ≤ p.2) (hS : S ∈ 𝓝 p.1)
    (hu : ContDiffAt ℝ 2 (fun x ↦ u x p.2) p.1)
    (hzero : parabolicQuadraticTilt u κ v p = 0)
    (hsupport : ∀ q ∈ S ×ˢ Icc a p.2, 0 ≤ parabolicQuadraticTilt u κ v q) :
    (fderiv ℝ (quadraticContactMap (fun x ↦ u x p.2) κ) p.1).toLinearMap.IsPositive :=
  isPositive_fderiv_quadraticContactMap hu hκ
    (isLocalMin_spatialTilt_of_parabolic_support ha hS hzero hsupport)

end PDE.Analysis
