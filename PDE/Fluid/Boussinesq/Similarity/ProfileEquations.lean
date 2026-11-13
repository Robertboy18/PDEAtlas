/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.Similarity.Ansatz
public import PDE.Representations.Similarity.Calculus

/-!
# Reduced self-similar Boussinesq profile equations

Substituting the backward ansatz with exponent `lambda` into the inviscid Boussinesq system
produces the stationary equations

```text
div U = 0,
-lambda U + (1 + lambda) (y · grad) U + (U · grad) U + grad P = Theta e₂,
(1 - lambda) Theta + (1 + lambda) y · grad Theta + U · grad Theta = 0.
```

The residuals are `momentumProfileResidual` and `temperatureProfileResidual`, and
`IsClassicalSelfSimilarProfile` asks for `C¹` profiles on which they and the divergence vanish.
The substitution theorem showing that such a profile generates a physical solution is in
`PDE.Fluid.Boussinesq.Similarity.Reduction`.
-/

open scoped Gradient

@[expose] public section

open PDE (advectiveDerivative)

namespace Boussinesq

open PDE.Representations.Similarity

set_option linter.missingDocs true

/-- Velocity scaling term `-lambda U + (1 + lambda) (y · grad) U`. -/
noncomputable def velocityProfileScalingTerm
    (profile : SelfSimilarProfile) (y : ℝ^2) : ℝ^2 :=
  (-profile.scalingExponent) • profile.velocityProfile y +
    (1 + profile.scalingExponent) • fderiv ℝ profile.velocityProfile y y

/-- Reduced momentum residual for a self-similar Boussinesq profile. -/
noncomputable def momentumProfileResidual
    (profile : SelfSimilarProfile) (y : ℝ^2) : ℝ^2 :=
  velocityProfileScalingTerm profile y +
    advectiveDerivative profile.velocityProfile profile.velocityProfile y +
    ∇ profile.pressureProfile y -
    buoyancyForce (profile.temperatureProfile y)

/-- Reduced transported-temperature residual for a self-similar Boussinesq profile. -/
noncomputable def temperatureProfileResidual
    (profile : SelfSimilarProfile) (y : ℝ^2) : ℝ :=
  scalingGenerator (1 - profile.scalingExponent)
      (1 + profile.scalingExponent) profile.temperatureProfile y +
    advectiveDerivative profile.velocityProfile profile.temperatureProfile y

/-- First-order classical regularity of all three self-similar profiles. -/
def HasClassicalSelfSimilarProfileRegularity
    (profile : SelfSimilarProfile) : Prop :=
  ContDiff ℝ 1 profile.velocityProfile ∧
    ContDiff ℝ 1 profile.temperatureProfile ∧
    ContDiff ℝ 1 profile.pressureProfile

namespace HasClassicalSelfSimilarProfileRegularity

/-- Extract continuous differentiability of the velocity profile. -/
theorem velocity_contDiff
    {profile : SelfSimilarProfile}
    (h : HasClassicalSelfSimilarProfileRegularity profile) :
    ContDiff ℝ 1 profile.velocityProfile :=
  h.1

/-- Extract continuous differentiability of the temperature profile. -/
theorem temperature_contDiff
    {profile : SelfSimilarProfile}
    (h : HasClassicalSelfSimilarProfileRegularity profile) :
    ContDiff ℝ 1 profile.temperatureProfile :=
  h.2.1

/-- Extract continuous differentiability of the pressure profile. -/
theorem pressure_contDiff
    {profile : SelfSimilarProfile}
    (h : HasClassicalSelfSimilarProfileRegularity profile) :
    ContDiff ℝ 1 profile.pressureProfile :=
  h.2.2

end HasClassicalSelfSimilarProfileRegularity

/-- The divergence, momentum, and temperature residuals vanish at every similarity point. -/
def SatisfiesSelfSimilarProfileEquations
    (profile : SelfSimilarProfile) : Prop :=
  (∀ y : ℝ^2, ∇· profile.velocityProfile y = 0) ∧
    (∀ y : ℝ^2, momentumProfileResidual profile y = 0) ∧
    ∀ y : ℝ^2, temperatureProfileResidual profile y = 0

namespace SatisfiesSelfSimilarProfileEquations

/-- Extract the divergence-free profile equation. -/
theorem divergence_eq_zero
    {profile : SelfSimilarProfile}
    (h : SatisfiesSelfSimilarProfileEquations profile)
    (y : ℝ^2) :
    ∇· profile.velocityProfile y = 0 :=
  h.1 y

/-- Extract vanishing of the stationary momentum residual. -/
theorem momentum_residual_eq_zero
    {profile : SelfSimilarProfile}
    (h : SatisfiesSelfSimilarProfileEquations profile)
    (y : ℝ^2) :
    momentumProfileResidual profile y = 0 :=
  h.2.1 y

/-- Extract vanishing of the stationary temperature residual. -/
theorem temperature_residual_eq_zero
    {profile : SelfSimilarProfile}
    (h : SatisfiesSelfSimilarProfileEquations profile)
    (y : ℝ^2) :
    temperatureProfileResidual profile y = 0 :=
  h.2.2 y

end SatisfiesSelfSimilarProfileEquations

/-- A classical self-similar profile is first-order regular and solves all reduced equations. -/
def IsClassicalSelfSimilarProfile
    (profile : SelfSimilarProfile) : Prop :=
  HasClassicalSelfSimilarProfileRegularity profile ∧
    SatisfiesSelfSimilarProfileEquations profile

namespace IsClassicalSelfSimilarProfile

/-- Extract the classical regularity of a self-similar profile. -/
theorem regularity
    {profile : SelfSimilarProfile}
    (h : IsClassicalSelfSimilarProfile profile) :
    HasClassicalSelfSimilarProfileRegularity profile :=
  h.1

/-- Extract the reduced equations of a classical self-similar profile. -/
theorem equations
    {profile : SelfSimilarProfile}
    (h : IsClassicalSelfSimilarProfile profile) :
    SatisfiesSelfSimilarProfileEquations profile :=
  h.2

/-- Extract continuous differentiability of the velocity profile. -/
theorem velocity_contDiff
    {profile : SelfSimilarProfile}
    (h : IsClassicalSelfSimilarProfile profile) :
    ContDiff ℝ 1 profile.velocityProfile :=
  h.regularity.velocity_contDiff

/-- Extract continuous differentiability of the temperature profile. -/
theorem temperature_contDiff
    {profile : SelfSimilarProfile}
    (h : IsClassicalSelfSimilarProfile profile) :
    ContDiff ℝ 1 profile.temperatureProfile :=
  h.regularity.temperature_contDiff

/-- Extract continuous differentiability of the pressure profile. -/
theorem pressure_contDiff
    {profile : SelfSimilarProfile}
    (h : IsClassicalSelfSimilarProfile profile) :
    ContDiff ℝ 1 profile.pressureProfile :=
  h.regularity.pressure_contDiff

/-- Extract the divergence-free profile equation. -/
theorem divergence_eq_zero
    {profile : SelfSimilarProfile}
    (h : IsClassicalSelfSimilarProfile profile)
    (y : ℝ^2) :
    ∇· profile.velocityProfile y = 0 :=
  h.equations.divergence_eq_zero y

/-- Extract vanishing of the stationary momentum residual. -/
theorem momentum_residual_eq_zero
    {profile : SelfSimilarProfile}
    (h : IsClassicalSelfSimilarProfile profile)
    (y : ℝ^2) :
    momentumProfileResidual profile y = 0 :=
  h.equations.momentum_residual_eq_zero y

/-- Extract vanishing of the stationary temperature residual. -/
theorem temperature_residual_eq_zero
    {profile : SelfSimilarProfile}
    (h : IsClassicalSelfSimilarProfile profile)
    (y : ℝ^2) :
    temperatureProfileResidual profile y = 0 :=
  h.equations.temperature_residual_eq_zero y

end IsClassicalSelfSimilarProfile

end Boussinesq
