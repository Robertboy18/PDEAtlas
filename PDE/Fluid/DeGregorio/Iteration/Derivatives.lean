/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTimeScalar
import CAS.ExactTactic

/-!
# Differentiating a frozen De Gregorio transport equation

For `w_t + u w_x = u_x w`, the slope satisfies
`(w_x)_t + u w_xx = u_xx w`. Differentiating again gives
`(w_xx)_t + u w_xxx = u_xxx w + u_xx w_x - u_x w_xx`.
The mixed derivatives follow from joint regularity and the original PDE.

These identities expose the cancellation needed for an H² transport estimate:
the highest velocity derivative multiplies the undifferentiated output.
-/

@[expose] public section

noncomputable section

open PDE.Analysis

namespace DeGregorio

/-- The frozen equation at one time determines the time derivative of
the slope. The two terms containing `u_x w_x` cancel at parameter `a = 1`. -/
theorem hasDerivAt_slope_of_frozen_transport {w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : ContDiff ℝ 2 (Function.uncurry w))
    (hu : ContDiff ℝ 2 (fun y ↦ u y t))
    (htransport : ∀ y, deriv (w y) t + u y t * deriv (fun z ↦ w z t) y =
      deriv (fun z ↦ u z t) y * w y t) :
    HasDerivAt (fun s ↦ deriv (fun y ↦ w y s) x)
      (deriv (deriv (fun y ↦ u y t)) x * w x t -
        u x t * deriv (deriv (fun y ↦ w y t)) x) t := by
  have heq : (fun y ↦ deriv (w y) t) =
      fun y ↦ deriv (fun z ↦ u z t) y * w y t -
        u y t * deriv (fun z ↦ w z t) y := by
    funext y
    exact eq_sub_of_add_eq (htransport y)
  have hwspace : ContDiff ℝ 2 (fun y ↦ w y t) :=
    hw.comp (contDiff_id.prodMk contDiff_const)
  have huD := (hu.differentiable (by norm_num) x).hasDerivAt
  have huDD := ((hu.deriv' (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have hwD := (hwspace.differentiable (by norm_num) x).hasDerivAt
  have hwDD := ((hwspace.deriv' (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have hres := (huDD.mul hwD).sub (huD.mul hwDD)
  simp only [Pi.mul_def, Pi.sub_def] at hres
  have hmixed := Calculus.hasDerivAt_spatial_deriv (x := x) (t := t) hw.contDiffAt
  rw [heq, hres.deriv] at hmixed
  convert hmixed using 1
  cas

/-- Twice differentiating the frozen transport equation determines the
curvature evolution. Joint `C³` regularity gives the second mixed derivative. -/
theorem hasDerivAt_curvature_of_frozen_transport {w u : ℝ → ℝ → ℝ} {t x : ℝ}
    (hw : ContDiff ℝ 3 (Function.uncurry w))
    (hu : ContDiff ℝ 3 (fun y ↦ u y t))
    (htransport : ∀ y, deriv (w y) t + u y t * deriv (fun z ↦ w z t) y =
      deriv (fun z ↦ u z t) y * w y t) :
    HasDerivAt (fun s ↦ deriv (deriv (fun y ↦ w y s)) x)
      (deriv (deriv (deriv (fun y ↦ u y t))) x * w x t +
        deriv (deriv (fun y ↦ u y t)) x * deriv (fun y ↦ w y t) x -
        deriv (fun y ↦ u y t) x * deriv (deriv (fun y ↦ w y t)) x -
        u x t * deriv (deriv (deriv (fun y ↦ w y t))) x) t := by
  let q := fun y s ↦ deriv (fun z ↦ w z s) y
  have hq : ContDiff ℝ 2 (Function.uncurry q) := Calculus.contDiff_spatial_deriv hw
  have heq : (fun y ↦ deriv (q y) t) =
      fun y ↦ deriv (deriv (fun z ↦ u z t)) y * w y t -
        u y t * deriv (deriv (fun z ↦ w z t)) y := by
    funext y
    exact (hasDerivAt_slope_of_frozen_transport (x := y)
      (hw.of_le (by norm_num)) (hu.of_le (by norm_num)) htransport).deriv
  have hwspace : ContDiff ℝ 3 (fun y ↦ w y t) :=
    hw.comp (contDiff_id.prodMk contDiff_const)
  have huD := (hu.differentiable (by norm_num) x).hasDerivAt
  have huDDD := (((hu.deriv' (n := 2)).deriv' (n := 1)).differentiable
    (by norm_num) x).hasDerivAt
  have hwD := (hwspace.differentiable (by norm_num) x).hasDerivAt
  have hwDDD := (((hwspace.deriv' (n := 2)).deriv' (n := 1)).differentiable
    (by norm_num) x).hasDerivAt
  have hres := (huDDD.mul hwD).sub (huD.mul hwDDD)
  simp only [Pi.mul_def, Pi.sub_def] at hres
  have hmixed := Calculus.hasDerivAt_spatial_deriv (x := x) (t := t) hq.contDiffAt
  rw [heq, hres.deriv] at hmixed
  convert hmixed using 1
  cas

end DeGregorio
