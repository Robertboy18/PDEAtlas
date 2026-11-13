/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.TensorProduct
public import PDE.Fluid.Axisymmetric.ReducedNavierStokes.RescaledSystem
public import CAS.Certificate.Relations

/-!
# Tensor-spline profiles and residual certificates for the reduced axisymmetric system

Three independent ingredients are combined:

* finite tensor-product normalized bases for profile representation;
* the steady rescaled reduced Euler/Navier–Stokes residuals;
* residual certificates for exact or validated computation.

The profile representation is exact: its three components are finite tensor-product expansions.
A residual certificate stores an ordinary Lean proof that the corresponding differential residual
is uniformly bounded on the stated domain, in the `ResidualBound` form of SymLean, our computer
algebra system for Lean. Zero error therefore proves the three steady residual equations.
Classical profile regularity is a separate question.

## Main definitions and results

* `TensorBasisReducedProfile`, `clampedTensorSplineReducedProfile`,
  `finiteCoxDeBoorTensorReducedProfile`: reduced profiles given by tensor-product coefficients,
  with pointwise enclosures from coefficient bounds (`swirl_mem_Icc`, `abs_swirl_le`, ...).
* `ReducedProfileResidualCertificate`, `SteadyReducedProfileResidualCertificate`,
  `SteadyAxisExtendedReducedProfileResidualCertificate`: uniform residual bounds for the three
  steady equations.
* `SteadyReducedProfileResidualCertificate.isSteady`,
  `SteadyAxisExtendedReducedProfileResidualCertificate.isSteady`: zero-error certificates give
  the steady profile equations on the certified domain.

## References

* C. de Boor, *A Practical Guide to Splines*, revised edition, Applied Mathematical Sciences,
  Springer, 2001, Chapter IX, The Representation of PP Functions by B-Splines, pp. 87-107, and
  Chapter XVII, Surface Approximation by Tensor Products, pp. 291-312.
  <https://doi.org/10.1007/978-1-4612-6333-3>
* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v1, Section 2.4, (29)-(30), pp. 9-10,
  for spline profiles and their certified residuals.
  <https://arxiv.org/abs/2609.10860v1>
* M. T. Nakao, M. Plum and Y. Watanabe, *Numerical Verification Methods and Computer-Assisted Proofs
  for Partial Differential Equations*, Springer Series in Computational Mathematics, Springer, 2019.
  <https://doi.org/10.1007/978-981-13-7669-6>
-/

@[expose] public section

namespace AxisymmetricFlow

open Set
open CAS.Splines
open CAS.Certificate

set_option linter.missingDocs true

noncomputable section

/-- Three reduced profile components represented in one radial–axial
tensor-product normalized basis. -/
structure TensorBasisReducedProfile
  (ι κ : Type*) [Fintype ι] [Fintype κ] where
  /-- Normalized positive radial basis. -/
  radialBasis : NormalizedPositiveBasis ℝ ι
  /-- Normalized positive axial basis. -/
  axialBasis : NormalizedPositiveBasis ℝ κ
  /-- Tensor coefficients of the desingularized swirl profile. -/
  swirlCoefficient : ι × κ → ℝ
  /-- Tensor coefficients of the desingularized vorticity profile. -/
  vorticityCoefficient : ι × κ → ℝ
  /-- Tensor coefficients of the desingularized streamfunction profile. -/
  streamFunctionCoefficient : ι × κ → ℝ

namespace TensorBasisReducedProfile

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The normalized tensor basis underlying a reduced profile. -/
def basis (profile : TensorBasisReducedProfile ι κ) :
    NormalizedPositiveBasis (ℝ^2) (ι × κ) :=
  meridianTensorProduct profile.radialBasis profile.axialBasis

/-- Rectangular carrier on which the tensor basis is normalized. -/
def domain (profile : TensorBasisReducedProfile ι κ) : Set (ℝ^2) :=
  profile.basis.carrier

/-- Exact reduced profile represented by the three tensor expansions. -/
def toReducedProfile
    (profile : TensorBasisReducedProfile ι κ) : ReducedProfile where
  swirl := profile.basis.expansion profile.swirlCoefficient
  vorticity := profile.basis.expansion profile.vorticityCoefficient
  streamFunction :=
    profile.basis.expansion profile.streamFunctionCoefficient

/-- The tensor carrier is the product of the one-dimensional carriers. -/
@[simp]
theorem mem_domain (profile : TensorBasisReducedProfile ι κ) (x : ℝ^2) :
    x ∈ profile.domain ↔
      x (0 : Fin 2) ∈ profile.radialBasis.carrier ∧
        x (1 : Fin 2) ∈ profile.axialBasis.carrier :=
  Iff.rfl

/-- Coefficient intervals enclose the represented swirl profile pointwise. -/
theorem swirl_mem_Icc
    (profile : TensorBasisReducedProfile ι κ)
    {lower upper : ℝ} {x : ℝ^2}
    (hlower : ∀ index, lower ≤ profile.swirlCoefficient index)
    (hupper : ∀ index, profile.swirlCoefficient index ≤ upper)
    (hx : x ∈ profile.domain) :
    profile.toReducedProfile.swirl x ∈ Icc lower upper :=
  profile.basis.expansion_mem_Icc hlower hupper hx

/-- Coefficient intervals enclose the represented vorticity profile
pointwise. -/
theorem vorticity_mem_Icc
    (profile : TensorBasisReducedProfile ι κ)
    {lower upper : ℝ} {x : ℝ^2}
    (hlower : ∀ index, lower ≤ profile.vorticityCoefficient index)
    (hupper : ∀ index, profile.vorticityCoefficient index ≤ upper)
    (hx : x ∈ profile.domain) :
    profile.toReducedProfile.vorticity x ∈ Icc lower upper :=
  profile.basis.expansion_mem_Icc hlower hupper hx

/-- Coefficient intervals enclose the represented streamfunction profile
pointwise. -/
theorem streamFunction_mem_Icc
    (profile : TensorBasisReducedProfile ι κ)
    {lower upper : ℝ} {x : ℝ^2}
    (hlower :
      ∀ index, lower ≤ profile.streamFunctionCoefficient index)
    (hupper :
      ∀ index, profile.streamFunctionCoefficient index ≤ upper)
    (hx : x ∈ profile.domain) :
    profile.toReducedProfile.streamFunction x ∈ Icc lower upper :=
  profile.basis.expansion_mem_Icc hlower hupper hx

/-- Uniform absolute coefficient bounds control the represented swirl. -/
theorem abs_swirl_le
    (profile : TensorBasisReducedProfile ι κ)
    {bound : ℝ} {x : ℝ^2}
    (hcoefficient :
      ∀ index, |profile.swirlCoefficient index| ≤ bound)
    (hx : x ∈ profile.domain) :
    |profile.toReducedProfile.swirl x| ≤ bound :=
  profile.basis.abs_expansion_le hcoefficient hx

/-- Uniform absolute coefficient bounds control the represented vorticity. -/
theorem abs_vorticity_le
    (profile : TensorBasisReducedProfile ι κ)
    {bound : ℝ} {x : ℝ^2}
    (hcoefficient :
      ∀ index, |profile.vorticityCoefficient index| ≤ bound)
    (hx : x ∈ profile.domain) :
    |profile.toReducedProfile.vorticity x| ≤ bound :=
  profile.basis.abs_expansion_le hcoefficient hx

/-- Uniform absolute coefficient bounds control the represented
streamfunction. -/
theorem abs_streamFunction_le
    (profile : TensorBasisReducedProfile ι κ)
    {bound : ℝ} {x : ℝ^2}
    (hcoefficient :
      ∀ index, |profile.streamFunctionCoefficient index| ≤ bound)
    (hx : x ∈ profile.domain) :
    |profile.toReducedProfile.streamFunction x| ≤ bound :=
  profile.basis.abs_expansion_le hcoefficient hx

end TensorBasisReducedProfile

/-- A reduced profile in the clamped one-panel tensor-product B-spline basis on a rectangle.

The basis functions are zero-extended outside the closed rectangle and need not be smooth at its
boundary.  Differential residual certificates should therefore use the rectangle interior unless
the coefficients are separately shown to satisfy the required endpoint compatibility. -/
def clampedTensorSplineReducedProfile
    (radialLeft radialRight axialLeft axialRight : ℝ)
    (radialDegree axialDegree : ℕ)
    (hradial : radialLeft < radialRight)
    (haxial : axialLeft < axialRight)
    (swirlCoefficient vorticityCoefficient
      streamFunctionCoefficient :
        Fin (radialDegree + 1) × Fin (axialDegree + 1) → ℝ) :
    TensorBasisReducedProfile
      (Fin (radialDegree + 1)) (Fin (axialDegree + 1)) where
  radialBasis :=
    clampedSinglePanelNormalizedBasis
      radialLeft radialRight radialDegree hradial
  axialBasis :=
    clampedSinglePanelNormalizedBasis
      axialLeft axialRight axialDegree haxial
  swirlCoefficient := swirlCoefficient
  vorticityCoefficient := vorticityCoefficient
  streamFunctionCoefficient := streamFunctionCoefficient

/-- A reduced profile in a finite multi-panel Cox–de Boor tensor basis. -/
def finiteCoxDeBoorTensorReducedProfile
    (radialKnots axialKnots : KnotSequence)
    (radialDegree radialCount axialDegree axialCount : ℕ)
    (radialPartition :
      FiniteCoxDeBoorPartition
        radialKnots radialDegree radialCount)
    (axialPartition :
      FiniteCoxDeBoorPartition
        axialKnots axialDegree axialCount)
    (swirlCoefficient vorticityCoefficient
      streamFunctionCoefficient :
        Fin radialCount × Fin axialCount → ℝ) :
    TensorBasisReducedProfile
      (Fin radialCount) (Fin axialCount) where
  radialBasis := radialPartition.toNormalizedPositiveBasis
  axialBasis := axialPartition.toNormalizedPositiveBasis
  swirlCoefficient := swirlCoefficient
  vorticityCoefficient := vorticityCoefficient
  streamFunctionCoefficient := streamFunctionCoefficient

/-- The tensor basis of a finite Cox–de Boor reduced profile is the direct
radial–axial Cox–de Boor tensor product. -/
theorem finiteCoxDeBoorTensorReducedProfile_basis
    (radialKnots axialKnots : KnotSequence)
    (radialDegree radialCount axialDegree axialCount : ℕ)
    (radialPartition :
      FiniteCoxDeBoorPartition
        radialKnots radialDegree radialCount)
    (axialPartition :
      FiniteCoxDeBoorPartition
        axialKnots axialDegree axialCount)
    (swirlCoefficient vorticityCoefficient
      streamFunctionCoefficient :
        Fin radialCount × Fin axialCount → ℝ) :
    (finiteCoxDeBoorTensorReducedProfile
      radialKnots axialKnots
      radialDegree radialCount axialDegree axialCount
      radialPartition axialPartition
      swirlCoefficient vorticityCoefficient
      streamFunctionCoefficient).basis =
        finiteCoxDeBoorMeridianTensorProduct
          radialPartition axialPartition :=
  rfl

/-- Certificates for three fixed scalar residual functions on one domain. -/
structure ReducedProfileResidualCertificate
    (swirlResidual vorticityResidual streamFunctionResidual : ℝ^2 → ℝ)
    (domain : Set (ℝ^2)) where
  /-- Uniform error budget for the swirl residual. -/
  swirlError : ℝ
  /-- Certified uniform swirl-residual bound. -/
  swirl_sound : ResidualBound swirlResidual domain swirlError
  /-- Uniform error budget for the vorticity residual. -/
  vorticityError : ℝ
  /-- Certified uniform vorticity-residual bound. -/
  vorticity_sound :
    ResidualBound vorticityResidual domain vorticityError
  /-- Uniform error budget for the streamfunction residual. -/
  streamFunctionError : ℝ
  /-- Certified uniform streamfunction-residual bound. -/
  streamFunction_sound :
    ResidualBound streamFunctionResidual domain streamFunctionError

namespace ReducedProfileResidualCertificate

variable
  {swirlResidual vorticityResidual streamFunctionResidual : ℝ^2 → ℝ}
  {domain : Set (ℝ^2)}

/-- Maximum of the three certified residual errors. -/
def maxError
    (certificate :
      ReducedProfileResidualCertificate swirlResidual vorticityResidual
        streamFunctionResidual domain) : ℝ :=
  max certificate.swirlError
    (max certificate.vorticityError certificate.streamFunctionError)

/-- The swirl residual is bounded by the combined error budget. -/
theorem swirl_sound_maxError
    (certificate :
      ReducedProfileResidualCertificate swirlResidual vorticityResidual
        streamFunctionResidual domain) :
    ResidualBound swirlResidual domain certificate.maxError :=
  approxOn_mono_error certificate.swirl_sound
    (le_max_left _ _)

/-- The vorticity residual is bounded by the combined error budget. -/
theorem vorticity_sound_maxError
    (certificate :
      ReducedProfileResidualCertificate swirlResidual vorticityResidual
        streamFunctionResidual domain) :
    ResidualBound vorticityResidual domain certificate.maxError :=
  approxOn_mono_error certificate.vorticity_sound <|
    le_trans (le_max_left _ _) (le_max_right _ _)

/-- The streamfunction residual is bounded by the combined error budget. -/
theorem streamFunction_sound_maxError
    (certificate :
      ReducedProfileResidualCertificate swirlResidual vorticityResidual
        streamFunctionResidual domain) :
    ResidualBound streamFunctionResidual domain certificate.maxError :=
  approxOn_mono_error certificate.streamFunction_sound <|
    le_trans (le_max_right _ _) (le_max_right _ _)

/-- Zero swirl error forces the stated swirl residual to vanish. -/
theorem swirl_eq_zero
    (certificate :
      ReducedProfileResidualCertificate swirlResidual vorticityResidual
        streamFunctionResidual domain)
    (herror : certificate.swirlError = 0)
    {x : ℝ^2} (hx : x ∈ domain) :
    swirlResidual x = 0 := by
  apply eqOn_zero_of_residualBound_zero
    (by simpa [herror] using certificate.swirl_sound)
  exact hx

/-- Zero vorticity error forces the stated vorticity residual to vanish. -/
theorem vorticity_eq_zero
    (certificate :
      ReducedProfileResidualCertificate swirlResidual vorticityResidual
        streamFunctionResidual domain)
    (herror : certificate.vorticityError = 0)
    {x : ℝ^2} (hx : x ∈ domain) :
    vorticityResidual x = 0 := by
  apply eqOn_zero_of_residualBound_zero
    (by simpa [herror] using certificate.vorticity_sound)
  exact hx

/-- Zero streamfunction error forces the stated streamfunction residual to
vanish. -/
theorem streamFunction_eq_zero
    (certificate :
      ReducedProfileResidualCertificate swirlResidual vorticityResidual
        streamFunctionResidual domain)
    (herror : certificate.streamFunctionError = 0)
    {x : ℝ^2} (hx : x ∈ domain) :
    streamFunctionResidual x = 0 := by
  apply eqOn_zero_of_residualBound_zero
    (by simpa [herror] using certificate.streamFunction_sound)
  exact hx

end ReducedProfileResidualCertificate

/-- Residual certificate for the three off-axis steady rescaled reduced
profile equations. -/
abbrev SteadyReducedProfileResidualCertificate
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift swirlRate vorticityRate : ℝ)
    (domain : Set (ℝ^2)) :=
  ReducedProfileResidualCertificate
    (reducedSwirlProfileResidual profile viscosity spatialRate axialDrift
      swirlRate)
    (reducedVorticityProfileResidual profile viscosity spatialRate axialDrift
      vorticityRate)
    (reducedStreamFunctionProfileResidual profile)
    domain

/-- Residual certificate for the three axis-value-extended steady rescaled reduced
profile equations. -/
abbrev SteadyAxisExtendedReducedProfileResidualCertificate
    (profile : ReducedProfile)
    (viscosity spatialRate axialDrift swirlRate vorticityRate : ℝ)
    (domain : Set (ℝ^2)) :=
  ReducedProfileResidualCertificate
    (axisExtendedReducedSwirlProfileResidual profile viscosity spatialRate
      axialDrift swirlRate)
    (axisExtendedReducedVorticityProfileResidual profile viscosity spatialRate
      axialDrift vorticityRate)
    (axisExtendedReducedStreamFunctionProfileResidual profile)
    domain

/-- Three zero-error certificates prove the steady residual equations on the
certified domain. Classical regularity and an off-axis domain are separate
conditions for interpreting these as the classical reduced equations. -/
theorem SteadyReducedProfileResidualCertificate.isSteady
    {profile : ReducedProfile}
    {viscosity spatialRate axialDrift swirlRate vorticityRate : ℝ}
    {domain : Set (ℝ^2)}
    (certificate :
      SteadyReducedProfileResidualCertificate profile viscosity spatialRate
        axialDrift swirlRate vorticityRate domain)
    (hswirl : certificate.swirlError = 0)
    (hvorticity : certificate.vorticityError = 0)
    (hstreamFunction : certificate.streamFunctionError = 0) :
    IsSteadyRescaledReducedProfileOn profile viscosity spatialRate axialDrift
      swirlRate vorticityRate domain := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact certificate.swirl_eq_zero hswirl hx
  · intro x hx
    exact certificate.vorticity_eq_zero hvorticity hx
  · intro x hx
    exact certificate.streamFunction_eq_zero hstreamFunction hx

/-- Three zero-error axis-value-extended residual certificates prove that a profile satisfies
the algebraically extended residual system on the certified domain. Radial parity and a smooth
three-dimensional lift are separate conditions. -/
theorem SteadyAxisExtendedReducedProfileResidualCertificate.isSteady
    {profile : ReducedProfile}
    {viscosity spatialRate axialDrift swirlRate vorticityRate : ℝ}
    {domain : Set (ℝ^2)}
    (certificate :
      SteadyAxisExtendedReducedProfileResidualCertificate profile viscosity
        spatialRate axialDrift swirlRate vorticityRate domain)
    (hswirl : certificate.swirlError = 0)
    (hvorticity : certificate.vorticityError = 0)
    (hstreamFunction : certificate.streamFunctionError = 0) :
    IsSteadyAxisExtendedRescaledResidualProfileOn profile viscosity spatialRate
      axialDrift swirlRate vorticityRate domain := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact certificate.swirl_eq_zero hswirl hx
  · intro x hx
    exact certificate.vorticity_eq_zero hvorticity hx
  · intro x hx
    exact certificate.streamFunction_eq_zero hstreamFunction hx

end

end AxisymmetricFlow
