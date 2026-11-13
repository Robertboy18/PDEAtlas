/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.Exponential.Flux
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Shifted global coordinates for the exponential flux

The affine diffeomorphism `(a,b) ↦ (b+1,a-b-2)`, which does not fix zero, gives
global Riemann invariants for the exponential flux (`coordinate_covectors`). In these
coordinates the transport speeds are `exp(z₀ - 1)` and `-exp(-(z₁ + 2))`, each
strictly increasing in its own coordinate (`positive_speed_derivative`).
-/

@[expose] public noncomputable section

open PDE.Hyperbolic.ConservationLaw.System
open scoped ContDiff Manifold

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.Exponential

/-- Global Riemann coordinates with a nonzero image of the zero state. -/
def coordinates : ℝ^2 ≃ₘ[ℝ] (Fin 2 → ℝ) where
  toEquiv :=
    { toFun := fun q ↦ ![q 1 + 1, q 0 - q 1 - 2]
      invFun := fun z ↦ !₂[z 0 + z 1 + 1, z 0 - 1]
      left_inv := by
        intro q
        ext i
        fin_cases i
        · change q 1 + 1 + (q 0 - q 1 - 2) + 1 = q 0
          cas
        · change q 1 + 1 - 1 = q 1
          cas
      right_inv := by
        intro z
        ext i
        fin_cases i
        · change z 0 - 1 + 1 = z 0
          cas
        · change z 0 + z 1 + 1 - (z 0 - 1) - 2 = z 1
          cas }
  contMDiff_toFun := by
    apply contMDiff_iff_contDiff.mpr
    rw [contDiff_pi]
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun q : ℝ^2 ↦ q 1 + 1)
      cas
    · change ContDiff ℝ ∞ (fun q : ℝ^2 ↦ q 0 - q 1 - 2)
      cas
  contMDiff_invFun := by
    apply contMDiff_iff_contDiff.mpr
    rw [contDiff_piLp]
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun z : Fin 2 → ℝ ↦ z 0 + z 1 + 1)
      fun_prop
    · change ContDiff ℝ ∞ (fun z : Fin 2 → ℝ ↦ z 0 - 1)
      fun_prop

/-- The zero state has coordinates `(1, -2)`. -/
theorem coordinates_zero : coordinates 0 = ![1, -2] := by
  ext i
  fin_cases i
  · change (0 : ℝ) + 1 = 1
    norm_num
  · change (0 : ℝ) - 0 - 2 = -2
    norm_num

/-- The differentials of the coordinates are `v ↦ v₁` and `v ↦ v₀ - v₁`. -/
theorem fderiv_coordinates (i : Fin 2) (q v : ℝ^2) :
    fderiv ℝ (fun z ↦ coordinates z i) q v = if i = 0 then v 1 else v 0 - v 1 := by
  rw [fderiv_apply_eq_sum_partialDeriv_mul, Fin.sum_univ_two]
  fin_cases i
  · change (∂[0] (fun z : ℝ^2 ↦ z 1 + 1)) q * v 0 +
      (∂[1] (fun z : ℝ^2 ↦ z 1 + 1)) q * v 1 = v 1
    have h₀ : (∂[0] (fun z : ℝ^2 ↦ z 1 + 1)) q = 0 := by cas
    have h₁ : (∂[1] (fun z : ℝ^2 ↦ z 1 + 1)) q = 1 := by cas
    simp only [h₀, h₁, zero_mul, one_mul, zero_add]
  · change (∂[0] (fun z : ℝ^2 ↦ z 0 - z 1 - 2)) q * v 0 +
      (∂[1] (fun z : ℝ^2 ↦ z 0 - z 1 - 2)) q * v 1 = v 0 - v 1
    have h₀ : (∂[0] (fun z : ℝ^2 ↦ z 0 - z 1 - 2)) q = 1 := by cas
    have h₁ : (∂[1] (fun z : ℝ^2 ↦ z 0 - z 1 - 2)) q = -1 := by cas
    rw [h₀, h₁]
    simp only [one_mul, neg_one_mul, sub_eq_add_neg]

/-- Each coordinate differential is a left eigenvector of the flux Jacobian, with the
speed of the other family. -/
theorem coordinate_covectors (i : Fin 2) (q v : ℝ^2) :
    fderiv ℝ (fun z ↦ coordinates z i) q (fderiv ℝ flux q v) =
      characteristicSpeed flux i.rev q * fderiv ℝ (fun z ↦ coordinates z i) q v := by
  rw [fderiv_coordinates, fderiv_coordinates, fderiv_flux, characteristicSpeed_flux]
  fin_cases i
  · rfl
  · change -Real.exp (-(q 0 - q 1)) * v 0 +
        (Real.exp (-(q 0 - q 1)) + Real.exp (q 1)) * v 1 - Real.exp (q 1) * v 1 =
      -Real.exp (-(q 0 - q 1)) * (v 0 - v 1)
    cas

/-- The first transport speed in the shifted coordinates. -/
theorem invariantSpeed_zero :
    invariantSpeed flux coordinates 0 = fun z ↦ Real.exp (z 0 - 1) := by
  funext z
  rw [invariantSpeed, characteristicSpeed_flux]
  rfl

/-- The second transport speed in the shifted coordinates. -/
theorem invariantSpeed_one :
    invariantSpeed flux coordinates 1 = fun z ↦ -Real.exp (-(z 1 + 2)) := by
  funext z
  rw [invariantSpeed, characteristicSpeed_flux]
  change -Real.exp (-(z 0 + z 1 + 1 - (z 0 - 1))) = -Real.exp (-(z 1 + 2))
  cas

/-- Each transport speed is strictly increasing in its own coordinate. -/
theorem positive_speed_derivative (i : Fin 2) (z : Fin 2 → ℝ) :
    0 < fderiv ℝ (invariantSpeed flux coordinates i) z (Pi.single i 1) := by
  fin_cases i
  · change 0 < fderiv ℝ (invariantSpeed flux coordinates 0) z (Pi.single 0 1)
    rw [invariantSpeed_zero]
    have hd : HasDerivAt (fun x : ℝ ↦ Real.exp (x - 1)) (Real.exp (z 0 - 1)) (z 0) := by
      cas
    have hcomp := hd.comp_hasFDerivAt (𝕜 := ℝ) (f := fun w : Fin 2 → ℝ ↦ w 0) z
      (hasFDerivAt_apply 0 z)
    dsimp only [Function.comp_def] at hcomp
    rw [hcomp.fderiv]
    simpa using Real.exp_pos (z 0 - 1)
  · change 0 < fderiv ℝ (invariantSpeed flux coordinates 1) z (Pi.single 1 1)
    rw [invariantSpeed_one]
    have hd : HasDerivAt (fun x : ℝ ↦ -Real.exp (-(x + 2)))
        (Real.exp (-(z 1 + 2))) (z 1) := by cas
    have hcomp := hd.comp_hasFDerivAt (𝕜 := ℝ) (f := fun w : Fin 2 → ℝ ↦ w 1) z
      (hasFDerivAt_apply 1 z)
    dsimp only [Function.comp_def] at hcomp
    rw [hcomp.fderiv]
    simpa using Real.exp_pos (-(z 1 + 2))

end PDE.Examples.Hyperbolic.ConservationLaw.System.GradientBlowup.Exponential
