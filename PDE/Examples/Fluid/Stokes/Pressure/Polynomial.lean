/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Fluid.Stokes.Pressure.Domain
public import PDE.Fluid.Stokes.Variational.GradientForce
public import PDE.Spaces.Sobolev.Calculus.Differentiation.LocalSobolev
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A nonconstant force on a union of balls

The polynomial `x₀² - x₁²` has gradient `(2x₀,-2x₁,0)`, and its weak derivatives on
the union of balls are in `L²`. As a force, this gradient pairs to zero with every
divergence-free `H¹₀` field, so zero velocity minimizes the Stokes energy. No pressure
equation is assumed.
-/

@[expose] public noncomputable section

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace PDE.Examples.StokesPressure

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open IncompressibleFlow.Stokes
open scoped ENNReal

/-- A quadratic with a nonconstant gradient in two coordinate directions. -/
def polynomial (x : ℝ^3) : ℝ := x 0 ^ 2 - x 1 ^ 2

/-- The polynomial is `C¹`, checked by the computer algebra system. -/
theorem contDiff_polynomial : ContDiff ℝ 1 polynomial := by
  cas

/-- The classical partial derivatives, coordinate by coordinate. -/
theorem partialDeriv_polynomial (i : Fin 3) (x : ℝ^3) :
    (∂[i] polynomial) x = ![2 * x 0, -2 * x 1, 0] i := by
  fin_cases i <;> cas

/-- The polynomial is `C¹` up to the boundary of the bounded domain. -/
theorem polynomial_up_to_boundary :
    ContDiffUpToBoundary 1 polynomial (domain : Set (ℝ^3)) :=
  contDiffUpToBoundary_of_contDiffOn isOpen_univ contDiff_polynomial.contDiffOn
    isBounded_domain.isCompact_closure (subset_univ _)

/-- The polynomial as an element of `H¹`. -/
def polynomialSobolev : H¹(domain) :=
  polynomial_up_to_boundary.toWkpSpaceOn domain.isOpen isBounded_domain 2

/-- The polynomial as an element of `L²`, used for integration by parts against
zero-trace fields. -/
def scalarPotential : DerivLp 3 2 domain :=
  polynomialSobolev.val (baseIndex 3 1)

/-- The stored weak derivatives of the polynomial. -/
def forceCoordinate (i : Fin 3) : DerivLp 3 2 domain :=
  polynomialSobolev.val (singleDerivIndex 3 i)

/-- The gradient force as an element of vector-valued `L²`. -/
def force : Lp (ℝ^3) 2 (domainMeasure 3 domain) :=
  Lp.euclideanTuple forceCoordinate

/-- The stored gradient is the weak derivative of the polynomial. -/
theorem hasWeakDerivative_scalarPotential (i : Fin 3) :
    HasWeakDerivativeOn (domain : Set (ℝ^3)) [i]
      (scalarPotential : ℝ^3 → ℝ) (forceCoordinate i : ℝ^3 → ℝ) := by
  simpa only [scalarPotential, forceCoordinate, singleDerivIndex_toList] using
    polynomialSobolev.property (singleDerivIndex 3 i)

/-- Each stored coordinate equals the classical derivative almost everywhere. -/
theorem forceCoordinate_apply_ae (i : Fin 3) :
    (forceCoordinate i : ℝ^3 → ℝ) =ᵐ[domainMeasure 3 domain]
      fun x ↦ ![2 * x 0, -2 * x 1, 0] i := by
  have h := polynomial_up_to_boundary.toWkpSpaceOn_apply_ae
    domain.isOpen isBounded_domain 2 (singleDerivIndex 3 i)
  simpa only [forceCoordinate, polynomialSobolev, singleDerivIndex_toList,
    iteratedPartialDeriv, partialDeriv_polynomial] using h

/-- The force is the nonconstant polynomial gradient almost everywhere. -/
theorem force_apply_ae :
    (force : ℝ^3 → ℝ^3) =ᵐ[domainMeasure 3 domain]
      fun x ↦ WithLp.toLp 2 ![2 * x 0, -2 * x 1, 0] := by
  have hcoords := ae_all_iff.mpr forceCoordinate_apply_ae
  filter_upwards [Lp.euclideanTuple_apply_ae forceCoordinate, hcoords] with x hx hd
  exact PiLp.ext fun i ↦ (hx i).trans (hd i)

/-- Zero velocity minimizes the signed Stokes energy for this force. -/
theorem zero_minimizes_energy (v : H¹₀(domain; ℝ^3))
    (hv : ∇· v = 0) :
    energy force 0 ≤ energy force v :=
  energy_zero_le_of_gradient_force scalarPotential forceCoordinate
    hasWeakDerivative_scalarPotential v hv

end PDE.Examples.StokesPressure
