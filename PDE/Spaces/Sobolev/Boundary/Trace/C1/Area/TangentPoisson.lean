/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.Rescaling
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.PoissonKernel.TangentMass

/-!
# Poisson mass for the actual tangent map of a C¹ chart

The surface-area factor is the chart Jacobian, and the vector direction is the
intrinsic outward unit normal. The identity is valid before any curved-surface limit.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set PDE.Analysis
open scoped InnerProductSpace

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The tangent-plane paired kernel of the actual boundary chart has mass equal to the
intrinsic outward normal, with the exact chart area factor. -/
theorem integral_chartBoundary_tangent_poisson_smul_normal
    (i : Fin hΩ.N) {a : ℝ^m} (ha : a ∈ chartBoundaryParameterDomain (Ω := Ω) i)
    (x : frontier Ω) (hx : chartBoundaryParametrization (Ω := Ω) i a = (x : ℝ^(m + 1)))
    {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ^m, (chartBoundaryJacobian (Ω := Ω) i a *
      (2 * t / (((m + 1 : ℕ) : ℝ) * unitBallVolume (m + 1) *
        ‖t • outwardUnitNormal (Ω := Ω) x -
          chartBoundaryTangentialDerivative (Ω := Ω) i a v‖ ^ (m + 1)))) •
      outwardUnitNormal (Ω := Ω) x) = outwardUnitNormal (Ω := Ω) x :=
  GreenFunction.integral_tangent_poisson_smul_normal (n := m + 1)
    (chartBoundaryTangentialDerivative (Ω := Ω) i a).toLinearMap
    (chartBoundaryTangentialDerivative_injective i ha) _ (norm_outwardUnitNormal x)
    (inner_outwardUnitNormal_chartBoundaryTangentialDerivative i ha x hx) ht

/-- The actual tangent-plane paired density is Bochner integrable. -/
theorem integrable_chartBoundary_tangent_poisson_smul_normal
    (i : Fin hΩ.N) {a : ℝ^m} (ha : a ∈ chartBoundaryParameterDomain (Ω := Ω) i)
    (x : frontier Ω) (hx : chartBoundaryParametrization (Ω := Ω) i a = (x : ℝ^(m + 1)))
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun v : ℝ^m ↦ (chartBoundaryJacobian (Ω := Ω) i a *
      (2 * t / (((m + 1 : ℕ) : ℝ) * unitBallVolume (m + 1) *
        ‖t • outwardUnitNormal (Ω := Ω) x -
          chartBoundaryTangentialDerivative (Ω := Ω) i a v‖ ^ (m + 1)))) •
      outwardUnitNormal (Ω := Ω) x) :=
  GreenFunction.integrable_tangent_poisson_smul_normal (n := m + 1)
    (chartBoundaryTangentialDerivative (Ω := Ω) i a).toLinearMap
    (chartBoundaryTangentialDerivative_injective i ha) _ (norm_outwardUnitNormal x)
    (inner_outwardUnitNormal_chartBoundaryTangentialDerivative i ha x hx) ht

end SobolevSpace.Trace.C1
