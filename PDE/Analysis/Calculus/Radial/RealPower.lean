/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Euclidean.Laplacian
public import PDE.FDeriv.Euclidean.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivatives of real powers of the radius

Away from the origin, every real power of the Euclidean radius is smooth. The formulas here
allow negative exponents and exponents below one, as needed for boundary barriers. The Laplacian
is the iterated-coordinate operator `laplacian`, whose radial reduction is
`EuclideanLaplacian.laplacian_radial`.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Radial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of a real power of the radius, with no restriction on the exponent. -/
theorem hasFDerivAt_norm_rpow_of_ne_zero (a : ℝ) {x : E} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖ ^ a) ((a * ‖x‖ ^ (a - 2)) • innerSL ℝ x) x := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  convert (EuclideanNorm.hasFDerivAt_norm_of_ne_zero hx).rpow_const
    (p := a) (Or.inl hr) using 1
  rw [map_smul, smul_smul]
  congr 1
  rw [show a - 2 = (a - 1) - 1 by ring, Real.rpow_sub_one hr]
  simp [div_eq_mul_inv, mul_assoc]

/-- Real powers of the radius are smooth at every nonzero point. -/
theorem contDiffAt_norm_rpow (a : ℝ) {x : E} (hx : x ≠ 0) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (fun y : E ↦ ‖y‖ ^ a) x :=
  (Real.contDiffAt_rpow_const_of_ne (norm_ne_zero_iff.mpr hx)).comp x
    (contDiffAt_norm ℝ hx)

/-- Coordinate derivative of a real radial power. -/
theorem partialDeriv_norm_rpow {n : ℕ} (a : ℝ) (i : Fin n) {x : ℝ^n} (hx : x ≠ 0) :
    (∂[i] (fun y : ℝ^n ↦ ‖y‖ ^ a)) x = a * ‖x‖ ^ (a - 2) * x i := by
  unfold partialDeriv
  rw [(hasFDerivAt_norm_rpow_of_ne_zero a hx).fderiv]
  simp [innerSL_apply_apply, EuclideanSpace.inner_single_right]

/-- The radial power formula for the coordinate Euclidean Laplacian, off the origin. -/
theorem laplacian_norm_rpow {n : ℕ} (a : ℝ) {x : ℝ^n} (hx : x ≠ 0) :
    laplacian (fun y : ℝ^n ↦ ‖y‖ ^ a) x =
      a * (a + (n : ℝ) - 2) * ‖x‖ ^ (a - 2) := by
  exact (EuclideanLaplacian.laplacian_radial (fun r ↦ r ^ a) x hx
    (Real.contDiffAt_rpow_const_of_ne (norm_ne_zero_iff.mpr hx))).trans
      (PDE.CoordinateSystems.radialLaplacian_rpow n ‖x‖ (norm_pos_iff.mpr hx) a)

end PDE.Analysis.Radial
