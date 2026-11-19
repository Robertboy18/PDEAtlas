/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.PotentialFlow
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A nonstationary harmonic Euler flow

The potential `(1+t)(x²-y²)` generates the incompressible velocity
`(2(1+t)x,-2(1+t)y)`. Its pressure contains `-(x²-y²)` from the time derivative,
as well as the negative kinetic energy. The CAS checks the polynomial identities;
the potential-flow construction gives a global smooth Euler solution and its initial trace.
The velocity grows linearly in space, so its kinetic energy on the whole plane is infinite.
-/

@[expose] public section

open PDE EuclideanSpace

namespace PDE.Examples.PotentialFlow

open IncompressibleFlow

set_option linter.missingDocs true

noncomputable section

/-- A time-dependent harmonic potential in two spatial dimensions. -/
def polynomial (x : ℝ^3) : ℝ := (1 + x 0) * (x 1 ^ 2 - x 2 ^ 2)

/-- The harmonic polynomial is smooth, checked by the CAS. -/
theorem contDiff_polynomial : ContDiff ℝ (⊤ : ℕ∞) polynomial := by
  cas

/-- The two components of the polynomial velocity field. -/
theorem spatialGradient_polynomial (x : ℝ^3) :
    spatialGradient polynomial x =
      WithLp.toLp 2 ![2 * (1 + x 0) * x 1, -2 * (1 + x 0) * x 2] := by
  ext i
  simp only [spatialGradient_apply]
  fin_cases i <;> cas

/-- The spatial Laplacian vanishes at every spacetime point. -/
theorem harmonic_polynomial (x : ℝ^3) : spatialLaplacian 2 polynomial x = 0 := by
  have hx : (∂[1] (fun y ↦ (∂[1] polynomial) y)) x = 2 * (1 + x 0) := by
    unfold polynomial
    cas
  have hy : (∂[2] (fun y ↦ (∂[2] polynomial) y)) x = -2 * (1 + x 0) := by
    unfold polynomial
    cas
  simp only [spatialLaplacian_apply, Fin.sum_univ_two]
  change (∂[1] (∂[1] polynomial)) x + (∂[2] (∂[2] polynomial)) x = 0
  rw [hx, hy]
  cas

/-- Bernoulli pressure includes the nonzero time derivative of the potential. -/
theorem potentialPressure_polynomial (x : ℝ^3) :
    potentialPressure polynomial (fun _ ↦ 0) x =
      -(x 1 ^ 2 - x 2 ^ 2) - 2 * (1 + x 0) ^ 2 * (x 1 ^ 2 + x 2 ^ 2) := by
  have ht : (∂[0] polynomial) x = x 1 ^ 2 - x 2 ^ 2 := by cas
  rw [potentialPressure, ht, specificKineticEnergy_eq_sum_sq, Fin.sum_univ_two]
  simp only [spatialGradient_polynomial, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  cas

/-- The initial potential velocity and zero force, with incompressibility derived. -/
def polynomialData : InitialValueData 2 :=
  Euler.potentialInitialValueData polynomial (fun _ ↦ 0)
    (contDiff_polynomial.of_le (by norm_num))
    (fun x ↦ harmonic_polynomial (PDE.Common.timeSpaceCons 0 x))

/-- The harmonic polynomial gives an actual global smooth Euler solution. -/
def polynomialSolution : Euler.GlobalSmoothSolution polynomialData :=
  Euler.potentialGlobalSmoothSolution polynomialData polynomial (fun _ ↦ 0)
    contDiff_polynomial contDiff_const (fun x _hx ↦ harmonic_polynomial x)
    rfl (fun _ ↦ rfl)

/-- The solution attains the initial velocity at time zero. -/
example (x : ℝ^2) :
    Filter.Tendsto polynomialSolution.u
      (nhdsWithin (PDE.Common.timeSpaceCons 0 x) (globalDomain 2))
      (nhds (polynomialData.initialVelocity x)) :=
  polynomialSolution.tendsto_initial x

/-- The Bernoulli pressure makes the Euler momentum residual vanish at every point. -/
example (x : ℝ^3) :
    eulerMomentumResidual 2 (spatialGradient polynomial)
      (potentialPressure polynomial (fun _ ↦ 0)) (fun _ ↦ 0) x = 0 := by
  have hzero : spatialGradient (fun _ : ℝ^3 ↦ (0 : ℝ)) = fun _ ↦ 0 := by
    funext y
    ext i
    simp [partialDeriv]
  simpa only [hzero] using
    eulerMomentumResidual_potentialPressure
      (contDiff_polynomial.of_le (by norm_num)).contDiffAt (differentiableAt_const 0)

end
end PDE.Examples.PotentialFlow
