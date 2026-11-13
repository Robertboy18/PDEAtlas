/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.Similarity.ProfileEquations
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Exact reduction of the self-similar Boussinesq equations

Substituting the backward power-law ansatz into the two-dimensional inviscid Boussinesq
equations and applying the chain rule, each physical residual is a strictly positive scalar
factor times its reduced profile residual before the candidate singular time. Consequently, a
`C¹` profile satisfying the reduced equations generates a classical physical solution on every
time set contained in `(-∞, 1)`.

The ansatz (from `Boussinesq.Similarity.Ansatz`) is, for scaling exponent `λ`,

```text
y = x / (1 - t)^(1 + λ),
u(x, t) = (1 - t)^λ U(y),   θ(x, t) = (1 - t)^(λ - 1) Θ(y),   p(x, t) = (1 - t)^(2λ) P(y).
```

Substituting into `∂ₜu + (u·∇)u + ∇p = θ e₂`, `∂ₜθ + (u·∇)θ = 0`, `∇·u = 0` and collecting the
powers of `(1 - t)` shows that every physical term in the momentum equation carries the common
factor `(1 - t)^(λ - 1)`, every term in the temperature equation the factor `(1 - t)^(λ - 2)`, and
the divergence the factor `(1 - t)^(-1)`. The reduced equations are the coefficients of these
common factors.

## Main results

* `divergence_selfSimilarAnsatz_velocity`, `momentumResidual_selfSimilarAnsatz`,
  `temperatureResidual_selfSimilarAnsatz`: exact factorisation of each physical residual as a
  power of `(1 - t)` times the corresponding profile residual, for `t < 1`.
* `IsSelfSimilarSolutionOn`: a profile whose generated fields are a classical Boussinesq solution
  on a time set before `t = 1`.
* `IsClassicalSelfSimilarProfile.isSelfSimilarSolutionOn`: a `C¹` profile solving the reduced
  equations generates a classical physical solution on every time set contained in `(-∞, 1)`.
* `zeroSelfSimilarProfile_isSelfSimilarSolutionOn_Iio`: the zero profile is such a solution.

Chen and Hou prove nearly self-similar blowup for the 2D Boussinesq equations through a dynamic
rescaling with time-dependent rates; when the rates are constant and the profile solves the
profile equations exactly, their rescaling becomes a fixed-power ansatz of the kind above
(Part I, Section 2.2).

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1 and Section 2.2, pp. 6-7.
  <https://arxiv.org/abs/2210.07191v4>
-/

open scoped Gradient

@[expose] public section

open PDE (divergence advectiveDerivative)

namespace Boussinesq

open PDE.Representations.Similarity

set_option linter.missingDocs true

private theorem velocityDivergenceScale
    (lambda : ℝ) {t : ℝ} (ht : t < 1) :
    backwardPowerScale (-lambda) 1 t *
        backwardPowerScale (1 + lambda) 1 t =
      backwardPowerScale 1 1 t := by
  rw [backward_power_scale_mul ht]
  congr 2
  ring

private theorem momentumAdvectionScale
    (lambda : ℝ) {t : ℝ} (ht : t < 1) :
    backwardPowerScale (-lambda) 1 t *
          backwardPowerScale (-lambda) 1 t *
        backwardPowerScale (1 + lambda) 1 t =
      backwardPowerScale (1 - lambda) 1 t := by
  calc
    _ = backwardPowerScale (-lambda + -lambda) 1 t *
        backwardPowerScale (1 + lambda) 1 t := by
      rw [backward_power_scale_mul ht]
    _ = backwardPowerScale ((-lambda + -lambda) + (1 + lambda)) 1 t := by
      rw [backward_power_scale_mul ht]
    _ = _ := congrArg (fun a : ℝ ↦ backwardPowerScale a 1 t) (by ring)

private theorem pressureGradientScale
    (lambda : ℝ) {t : ℝ} (ht : t < 1) :
    backwardPowerScale (-2 * lambda) 1 t *
        backwardPowerScale (1 + lambda) 1 t =
      backwardPowerScale (1 - lambda) 1 t := by
  rw [backward_power_scale_mul ht]
  exact congrArg (fun a : ℝ ↦ backwardPowerScale a 1 t) (by ring)

private theorem temperatureAdvectionScale
    (lambda : ℝ) {t : ℝ} (ht : t < 1) :
    backwardPowerScale (-lambda) 1 t *
          backwardPowerScale (1 - lambda) 1 t *
        backwardPowerScale (1 + lambda) 1 t =
      backwardPowerScale (2 - lambda) 1 t := by
  calc
    _ = backwardPowerScale (-lambda + (1 - lambda)) 1 t *
        backwardPowerScale (1 + lambda) 1 t := by
      rw [backward_power_scale_mul ht]
    _ = backwardPowerScale ((-lambda + (1 - lambda)) + (1 + lambda)) 1 t := by
      rw [backward_power_scale_mul ht]
    _ = _ := congrArg (fun a : ℝ ↦ backwardPowerScale a 1 t) (by ring)

/-- The divergence of the physical velocity is the profile divergence times one inverse-time
factor. -/
theorem divergence_selfSimilarAnsatz_velocity
    (ssb : SelfSimilarProfile) (x : ℝ^2) {t : ℝ} (ht : t < 1)
    (hvelocity : ∀ i : Fin 2,
      DifferentiableAt ℝ (fun y ↦ ssb.velocityProfile y i)
        (selfSimilarCoords ssb x t)) :
    ∇· (fun y ↦ (selfSimilarAnsatz ssb).velocity y t) x =
      backwardPowerScale 1 1 t *
        ∇· ssb.velocityProfile (selfSimilarCoords ssb x t) := by
  change
    ∇·
        (fun y ↦ backwardPowerScale (-ssb.scalingExponent) 1 t •
          ssb.velocityProfile
            (centeredDilation
              (backwardPowerScale (1 + ssb.scalingExponent) 1 t) 0 y)) x =
      _
  rw [divergence_smul_comp_centered_dilation
    ssb.velocityProfile
    (backwardPowerScale (-ssb.scalingExponent) 1 t)
    (backwardPowerScale (1 + ssb.scalingExponent) 1 t) 0 x hvelocity]
  rw [velocityDivergenceScale ssb.scalingExponent ht]
  rfl

/-- Time differentiation of the physical velocity produces the velocity-profile scaling term. -/
theorem deriv_selfSimilarAnsatz_velocity
    (ssb : SelfSimilarProfile) (x : ℝ^2) {t : ℝ} (ht : t < 1)
    (hvelocity : DifferentiableAt ℝ ssb.velocityProfile
      (selfSimilarCoords ssb x t)) :
    deriv (fun s ↦ (selfSimilarAnsatz ssb).velocity x s) t =
      backwardPowerScale (1 - ssb.scalingExponent) 1 t •
        velocityProfileScalingTerm ssb (selfSimilarCoords ssb x t) := by
  change
    deriv (fun s ↦ backwardSelfSimilarAnsatz ssb.velocityProfile
      (-ssb.scalingExponent) (1 + ssb.scalingExponent) 1 0 x s) t = _
  rw [(hasDerivAt_backward_self_similar_ansatz ssb.velocityProfile
    (-ssb.scalingExponent) (1 + ssb.scalingExponent) 1 0 x t
    hvelocity ht).deriv]
  have hscale :
      backwardPowerScale (-ssb.scalingExponent + 1) 1 t =
        backwardPowerScale (1 - ssb.scalingExponent) 1 t := by
    exact congrArg (fun a : ℝ ↦ backwardPowerScale a 1 t) (by ring)
  rw [hscale]
  rfl

/-- The physical convective acceleration is the profile convective acceleration times the
common momentum scale. -/
theorem advectiveDerivative_selfSimilarAnsatz_velocity
    (ssb : SelfSimilarProfile) (x : ℝ^2) {t : ℝ} (ht : t < 1)
    (hvelocity : DifferentiableAt ℝ ssb.velocityProfile
      (selfSimilarCoords ssb x t)) :
    advectiveDerivative
        (fun y ↦ (selfSimilarAnsatz ssb).velocity y t)
        (fun y ↦ (selfSimilarAnsatz ssb).velocity y t) x =
      backwardPowerScale (1 - ssb.scalingExponent) 1 t •
        advectiveDerivative ssb.velocityProfile ssb.velocityProfile
          (selfSimilarCoords ssb x t) := by
  change
    advectiveDerivative
        (fun y ↦ backwardPowerScale (-ssb.scalingExponent) 1 t •
          ssb.velocityProfile
            (centeredDilation
              (backwardPowerScale (1 + ssb.scalingExponent) 1 t) 0 y))
        (fun y ↦ backwardPowerScale (-ssb.scalingExponent) 1 t •
          ssb.velocityProfile
            (centeredDilation
              (backwardPowerScale (1 + ssb.scalingExponent) 1 t) 0 y)) x = _
  rw [advectiveDerivative_smul_comp_centered_dilation
    ssb.velocityProfile ssb.velocityProfile
    (backwardPowerScale (-ssb.scalingExponent) 1 t)
    (backwardPowerScale (-ssb.scalingExponent) 1 t)
    (backwardPowerScale (1 + ssb.scalingExponent) 1 t) 0 x hvelocity]
  rw [momentumAdvectionScale ssb.scalingExponent ht]
  rfl

/-- The physical pressure gradient is the profile pressure gradient times the common momentum
scale. -/
theorem gradient_selfSimilarAnsatz_pressure
    (ssb : SelfSimilarProfile) (x : ℝ^2) {t : ℝ} (ht : t < 1)
    (hpressure : DifferentiableAt ℝ ssb.pressureProfile
      (selfSimilarCoords ssb x t)) :
    ∇ (fun y ↦ (selfSimilarAnsatz ssb).pressure y t) x =
      backwardPowerScale (1 - ssb.scalingExponent) 1 t •
        ∇ ssb.pressureProfile (selfSimilarCoords ssb x t) := by
  change
    ∇
        (fun y ↦ scaledProfileAnsatz ssb.pressureProfile
          (backwardPowerScale (-2 * ssb.scalingExponent) 1)
          (backwardPowerScale (1 + ssb.scalingExponent) 1) 0 y t) x = _
  rw [gradient_scaled_profile_ansatz ssb.pressureProfile
    (backwardPowerScale (-2 * ssb.scalingExponent) 1)
    (backwardPowerScale (1 + ssb.scalingExponent) 1) 0 x t hpressure]
  rw [pressureGradientScale ssb.scalingExponent ht]
  rfl

/-- The physical buoyancy force is the profile buoyancy force times the common momentum scale. -/
theorem buoyancyForce_selfSimilarAnsatz_temperature
    (ssb : SelfSimilarProfile) (x : ℝ^2) (t : ℝ) :
    buoyancyForce ((selfSimilarAnsatz ssb).temperature x t) =
      backwardPowerScale (1 - ssb.scalingExponent) 1 t •
        buoyancyForce (ssb.temperatureProfile (selfSimilarCoords ssb x t)) := by
  rw [selfSimilarAnsatz_temperature_apply_eq_backwardPowerScale,
    buoyancyForce_smul]

/-- Exact factorization of the physical momentum residual by the reduced profile residual. -/
theorem momentumResidual_selfSimilarAnsatz
    (ssb : SelfSimilarProfile) (x : ℝ^2) {t : ℝ} (ht : t < 1)
    (hvelocity : DifferentiableAt ℝ ssb.velocityProfile
      (selfSimilarCoords ssb x t))
    (hpressure : DifferentiableAt ℝ ssb.pressureProfile
      (selfSimilarCoords ssb x t)) :
    deriv (fun s ↦ (selfSimilarAnsatz ssb).velocity x s) t +
          advectiveDerivative
            (fun y ↦ (selfSimilarAnsatz ssb).velocity y t)
            (fun y ↦ (selfSimilarAnsatz ssb).velocity y t) x +
          ∇ (fun y ↦ (selfSimilarAnsatz ssb).pressure y t) x -
        buoyancyForce ((selfSimilarAnsatz ssb).temperature x t) =
      backwardPowerScale (1 - ssb.scalingExponent) 1 t •
        momentumProfileResidual ssb (selfSimilarCoords ssb x t) := by
  rw [deriv_selfSimilarAnsatz_velocity ssb x ht hvelocity,
    advectiveDerivative_selfSimilarAnsatz_velocity ssb x ht hvelocity,
    gradient_selfSimilarAnsatz_pressure ssb x ht hpressure,
    buoyancyForce_selfSimilarAnsatz_temperature]
  unfold momentumProfileResidual
  module

/-- Time differentiation of physical temperature produces its reduced scaling generator. -/
theorem deriv_selfSimilarAnsatz_temperature
    (ssb : SelfSimilarProfile) (x : ℝ^2) {t : ℝ} (ht : t < 1)
    (htemperature : DifferentiableAt ℝ ssb.temperatureProfile
      (selfSimilarCoords ssb x t)) :
    deriv (fun s ↦ (selfSimilarAnsatz ssb).temperature x s) t =
      backwardPowerScale (2 - ssb.scalingExponent) 1 t *
        scalingGenerator (1 - ssb.scalingExponent)
          (1 + ssb.scalingExponent) ssb.temperatureProfile
          (selfSimilarCoords ssb x t) := by
  change
    deriv (fun s ↦ backwardSelfSimilarAnsatz ssb.temperatureProfile
      (1 - ssb.scalingExponent) (1 + ssb.scalingExponent) 1 0 x s) t = _
  rw [deriv_backward_self_similar_ansatz ssb.temperatureProfile
    (1 - ssb.scalingExponent) (1 + ssb.scalingExponent) 1 0 x t
    htemperature ht]
  congr 2
  ring

/-- Physical temperature advection is profile advection times the common temperature scale. -/
theorem advectiveDerivative_selfSimilarAnsatz_temperature
    (ssb : SelfSimilarProfile) (x : ℝ^2) {t : ℝ} (ht : t < 1)
    (htemperature : DifferentiableAt ℝ ssb.temperatureProfile
      (selfSimilarCoords ssb x t)) :
    advectiveDerivative
        (fun y ↦ (selfSimilarAnsatz ssb).velocity y t)
        (fun y ↦ (selfSimilarAnsatz ssb).temperature y t) x =
      backwardPowerScale (2 - ssb.scalingExponent) 1 t *
        advectiveDerivative ssb.velocityProfile ssb.temperatureProfile
          (selfSimilarCoords ssb x t) := by
  change
    advectiveDerivative
        (fun y ↦ backwardPowerScale (-ssb.scalingExponent) 1 t •
          ssb.velocityProfile
            (centeredDilation
              (backwardPowerScale (1 + ssb.scalingExponent) 1 t) 0 y))
        (fun y ↦ backwardPowerScale (1 - ssb.scalingExponent) 1 t •
          ssb.temperatureProfile
            (centeredDilation
              (backwardPowerScale (1 + ssb.scalingExponent) 1 t) 0 y)) x = _
  rw [advectiveDerivative_smul_comp_centered_dilation
    ssb.velocityProfile ssb.temperatureProfile
    (backwardPowerScale (-ssb.scalingExponent) 1 t)
    (backwardPowerScale (1 - ssb.scalingExponent) 1 t)
    (backwardPowerScale (1 + ssb.scalingExponent) 1 t) 0 x htemperature]
  simp only [smul_eq_mul]
  rw [temperatureAdvectionScale ssb.scalingExponent ht]
  rfl

/-- Exact factorization of the physical temperature residual by the reduced profile residual. -/
theorem temperatureResidual_selfSimilarAnsatz
    (ssb : SelfSimilarProfile) (x : ℝ^2) {t : ℝ} (ht : t < 1)
    (htemperature : DifferentiableAt ℝ ssb.temperatureProfile
      (selfSimilarCoords ssb x t)) :
    deriv (fun s ↦ (selfSimilarAnsatz ssb).temperature x s) t +
        advectiveDerivative
          (fun y ↦ (selfSimilarAnsatz ssb).velocity y t)
          (fun y ↦ (selfSimilarAnsatz ssb).temperature y t) x =
      backwardPowerScale (2 - ssb.scalingExponent) 1 t *
        temperatureProfileResidual ssb (selfSimilarCoords ssb x t) := by
  rw [deriv_selfSimilarAnsatz_temperature ssb x ht htemperature,
    advectiveDerivative_selfSimilarAnsatz_temperature ssb x ht htemperature]
  unfold temperatureProfileResidual
  ring

/-- A self-similar profile whose generated fields solve the original
Boussinesq equations on a pre-singular time set. -/
def IsSelfSimilarSolutionOn
    (profile : SelfSimilarProfile) (times : Set ℝ) : Prop :=
  times ⊆ Set.Iio 1 ∧
    IsClassicalSolutionOn (selfSimilarAnsatz profile) times

namespace IsSelfSimilarSolutionOn

/-- Extract that all admitted times precede the candidate singular time. -/
theorem times_subset_Iio
    {profile : SelfSimilarProfile} {times : Set ℝ}
    (h : IsSelfSimilarSolutionOn profile times) :
    times ⊆ Set.Iio 1 :=
  h.1

/-- Extract the classical physical solution generated by the profile. -/
theorem isClassicalSolutionOn
    {profile : SelfSimilarProfile} {times : Set ℝ}
    (h : IsSelfSimilarSolutionOn profile times) :
    IsClassicalSolutionOn (selfSimilarAnsatz profile) times :=
  h.2

end IsSelfSimilarSolutionOn

/-- A classical solution of the reduced profile equations generates a classical physical
Boussinesq solution on every time set before `t = 1`. -/
theorem IsClassicalSelfSimilarProfile.isSelfSimilarSolutionOn
    {profile : SelfSimilarProfile}
    (hprofile : IsClassicalSelfSimilarProfile profile)
    {times : Set ℝ} (htimes : times ⊆ Set.Iio 1) :
    IsSelfSimilarSolutionOn profile times := by
  have hvelocity := hprofile.velocity_contDiff
  have htemperature := hprofile.temperature_contDiff
  have hpressure := hprofile.pressure_contDiff
  -- each field is a profile `g` composed with the backward self-similar scalings
  have hcd {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ^2 → F) (a : ℝ)
      (hg : ContDiff ℝ 1 g) :
      ContDiffOn ℝ 1 (fun xt : ℝ^2 × ℝ ↦ backwardSelfSimilarAnsatz g a
        (1 + profile.scalingExponent) 1 0 xt.1 xt.2) (Set.univ ×ˢ times) := by
    unfold backwardSelfSimilarAnsatz
    exact contDiffOn_prod_scaled_profile_ansatz g (backwardPowerScale a 1)
      (backwardPowerScale (1 + profile.scalingExponent) 1) 0 times hg
      ((contDiffOn_backward_power_scale a 1).mono htimes)
      ((contDiffOn_backward_power_scale (1 + profile.scalingExponent) 1).mono htimes)
  have hdt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ^2 → F) (a : ℝ)
      (hg : ContDiff ℝ 1 g) (x : ℝ^2) {t : ℝ} (ht : t ∈ times) :
      DifferentiableAt ℝ
        (fun s ↦ backwardSelfSimilarAnsatz g a (1 + profile.scalingExponent) 1 0 x s) t :=
    (hasDerivAt_backward_self_similar_ansatz g a (1 + profile.scalingExponent) 1 0 x t
      ((hg.differentiable (by norm_num)).differentiableAt) (htimes ht)).differentiableAt
  refine ⟨htimes,
    { velocity_contDiffOn := hcd profile.velocityProfile _ hvelocity
      temperature_contDiffOn := hcd profile.temperatureProfile _ htemperature
      pressure_contDiffOn := hcd profile.pressureProfile _ hpressure
      velocity_differentiableAt_time := fun ht ↦ hdt profile.velocityProfile _ hvelocity _ ht
      temperature_differentiableAt_time := fun ht ↦
        hdt profile.temperatureProfile _ htemperature _ ht
      divergence_eq_zero := ?_
      momentum_eq := ?_
      temperature_transport_eq := ?_ }⟩
  · intro x t ht
    rw [divergence_selfSimilarAnsatz_velocity profile x (htimes ht)
      (fun i ↦ (((contDiff_piLp (p := (2 : ENNReal))).1 hvelocity i).differentiable
        (by norm_num)).differentiableAt), hprofile.divergence_eq_zero]
    simp
  · intro x t ht
    rw [← sub_eq_zero, momentumResidual_selfSimilarAnsatz profile x (htimes ht)
      ((hvelocity.differentiable (by norm_num)).differentiableAt)
      ((hpressure.differentiable (by norm_num)).differentiableAt),
      hprofile.momentum_residual_eq_zero]
    simp
  · intro x t ht
    rw [temperatureResidual_selfSimilarAnsatz profile x (htimes ht)
      ((htemperature.differentiable (by norm_num)).differentiableAt),
      hprofile.temperature_residual_eq_zero]
    simp

/-- The zero profile satisfies the reduced equations with classical regularity. -/
theorem zeroSelfSimilarProfile_isClassicalSelfSimilarProfile :
    IsClassicalSelfSimilarProfile zeroSelfSimilarProfile := by
  refine ⟨⟨by fun_prop, by fun_prop, by fun_prop⟩, ?_, ?_, ?_⟩
  · intro y
    simp [zeroSelfSimilarProfile, divergence, PDE.partialDeriv_const]
  · intro y
    ext i
    simp [momentumProfileResidual, velocityProfileScalingTerm,
      zeroSelfSimilarProfile, advectiveDerivative, gradient,
      buoyancyForce]
  · intro y
    simp [temperatureProfileResidual, scalingGenerator,
      zeroSelfSimilarProfile, advectiveDerivative]

/-- The zero profile is a self-similar solution on all of `(-∞, 1)`. -/
theorem zeroSelfSimilarProfile_isSelfSimilarSolutionOn_Iio :
    IsSelfSimilarSolutionOn zeroSelfSimilarProfile (Set.Iio 1) :=
  zeroSelfSimilarProfile_isClassicalSelfSimilarProfile.isSelfSimilarSolutionOn
    fun _ ht ↦ ht

end Boussinesq
