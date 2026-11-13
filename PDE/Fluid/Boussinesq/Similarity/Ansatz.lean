/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Boussinesq.Model
public import PDE.Representations.Similarity.Pointwise

/-!
# Backward self-similar Boussinesq ansatz

The exact power-law ansatz is centered at the origin and normalized to a candidate singular time
`T = 1`. It reuses LeanPDE's equation-independent backward similarity transformation.

For scaling exponent `λ`, the physical fields are

```text
y = x / (1 - t)^(1 + λ),
u(x,t) = (1 - t)^λ U(y),
θ(x,t) = (1 - t)^(λ - 1) Θ(y),
p(x,t) = (1 - t)^(2 λ) P(y).
```

The familiar quotient formulas are proved only for `t < 1`, where the real-power base is
strictly positive. The underlying Lean functions remain total outside that analytic domain.

This is the exact fixed-power ansatz for the upward-buoyancy primitive model in
`Boussinesq.Model`. The nearly self-similar formulation of Chen and Hou, with time-dependent
scales, is the dynamic rescaling of `Boussinesq.VorticityStream.DynamicRescaling`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1 and Section 2.2, pp. 6-7.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace Boussinesq

open PDE.Representations.Similarity

set_option linter.missingDocs true

/-- Spatial profiles and scaling exponent for the backward self-similar
Boussinesq ansatz. -/
structure SelfSimilarProfile where
  /-- Free exponent controlling amplitude and spatial concentration. -/
  scalingExponent : ℝ
  /-- Velocity profile in similarity coordinates. -/
  velocityProfile : ℝ^2 → ℝ^2
  /-- Temperature profile in similarity coordinates. -/
  temperatureProfile : ℝ^2 → ℝ
  /-- Pressure profile in similarity coordinates. -/
  pressureProfile : ℝ^2 → ℝ

/-- The zero self-similar Boussinesq profile. -/
def zeroSelfSimilarProfile : SelfSimilarProfile where
  scalingExponent := 0
  velocityProfile := fun _ ↦ 0
  temperatureProfile := fun _ ↦ 0
  pressureProfile := fun _ ↦ 0

/-- Similarity coordinates centered at the origin with reference time `1`.
The physical length scale tends to zero as `t ↑ 1` when `scalingExponent > -1`. -/
noncomputable def selfSimilarCoords
    (profile : SelfSimilarProfile) (x : ℝ^2) (t : ℝ) : ℝ^2 :=
  centeredDilation
    (backwardPowerScale (1 + profile.scalingExponent) 1 t) 0 x

/-- Component form of the total similarity-coordinate definition. -/
theorem selfSimilarCoords_apply
    (profile : SelfSimilarProfile) (x : ℝ^2) (t : ℝ) (i : Fin 2) :
    selfSimilarCoords profile x t i =
      backwardPowerScale (1 + profile.scalingExponent) 1 t * x i := by
  simp [selfSimilarCoords, centeredDilation]

/-- Before the candidate singular time, similarity coordinates have the usual quotient form. -/
theorem selfSimilarCoords_apply_of_lt
    (profile : SelfSimilarProfile) (x : ℝ^2) {t : ℝ} (ht : t < 1)
    (i : Fin 2) :
    selfSimilarCoords profile x t i =
      x i / ((1 - t) ^ (1 + profile.scalingExponent)) := by
  rw [selfSimilarCoords_apply]
  unfold backwardPowerScale
  rw [Real.rpow_neg (sub_pos.mpr ht).le]
  ring

/-- Convert similarity profiles into physical-space Boussinesq fields. -/
noncomputable def selfSimilarAnsatz
    (profile : SelfSimilarProfile) : BoussinesqFields where
  velocity := backwardSelfSimilarAnsatz profile.velocityProfile
    (-profile.scalingExponent) (1 + profile.scalingExponent) 1 0
  temperature := backwardSelfSimilarAnsatz profile.temperatureProfile
    (1 - profile.scalingExponent) (1 + profile.scalingExponent) 1 0
  pressure := backwardSelfSimilarAnsatz profile.pressureProfile
    (-2 * profile.scalingExponent) (1 + profile.scalingExponent) 1 0

/-- Component formula in terms of LeanPDE's total backward power scale. -/
theorem selfSimilarAnsatz_velocity_apply_eq_backwardPowerScale
    (profile : SelfSimilarProfile) (x : ℝ^2) (t : ℝ) (i : Fin 2) :
    (selfSimilarAnsatz profile).velocity x t i =
      backwardPowerScale (-profile.scalingExponent) 1 t *
        profile.velocityProfile (selfSimilarCoords profile x t) i := by
  rfl

/-- Temperature formula in terms of LeanPDE's total backward power scale. -/
theorem selfSimilarAnsatz_temperature_apply_eq_backwardPowerScale
    (profile : SelfSimilarProfile) (x : ℝ^2) (t : ℝ) :
    (selfSimilarAnsatz profile).temperature x t =
      backwardPowerScale (1 - profile.scalingExponent) 1 t *
        profile.temperatureProfile (selfSimilarCoords profile x t) := by
  rfl

/-- Pressure formula in terms of LeanPDE's total backward power scale. -/
theorem selfSimilarAnsatz_pressure_apply_eq_backwardPowerScale
    (profile : SelfSimilarProfile) (x : ℝ^2) (t : ℝ) :
    (selfSimilarAnsatz profile).pressure x t =
      backwardPowerScale (-2 * profile.scalingExponent) 1 t *
        profile.pressureProfile (selfSimilarCoords profile x t) := by
  rfl

/-- The velocity amplitude is the total real power `(1 - t)^λ`. -/
theorem selfSimilarAnsatz_velocity_apply
    (profile : SelfSimilarProfile) (x : ℝ^2) (t : ℝ) (i : Fin 2) :
    (selfSimilarAnsatz profile).velocity x t i =
      (1 - t) ^ profile.scalingExponent *
        profile.velocityProfile (selfSimilarCoords profile x t) i := by
  rw [selfSimilarAnsatz_velocity_apply_eq_backwardPowerScale]
  unfold backwardPowerScale
  congr 2
  ring

/-- The temperature amplitude is the total real power `(1 - t)^(λ - 1)`. -/
theorem selfSimilarAnsatz_temperature_apply
    (profile : SelfSimilarProfile) (x : ℝ^2) (t : ℝ) :
    (selfSimilarAnsatz profile).temperature x t =
      (1 - t) ^ (-1 + profile.scalingExponent) *
        profile.temperatureProfile (selfSimilarCoords profile x t) := by
  rw [selfSimilarAnsatz_temperature_apply_eq_backwardPowerScale]
  unfold backwardPowerScale
  congr 2
  ring

/-- The pressure amplitude is the total real power `(1 - t)^(2 λ)`. -/
theorem selfSimilarAnsatz_pressure_apply
    (profile : SelfSimilarProfile) (x : ℝ^2) (t : ℝ) :
    (selfSimilarAnsatz profile).pressure x t =
      (1 - t) ^ (2 * profile.scalingExponent) *
        profile.pressureProfile (selfSimilarCoords profile x t) := by
  rw [selfSimilarAnsatz_pressure_apply_eq_backwardPowerScale]
  unfold backwardPowerScale
  congr 2
  ring

/-- The zero profiles generate exactly the zero physical Boussinesq fields. -/
theorem selfSimilarAnsatz_zeroSelfSimilarProfile :
    selfSimilarAnsatz zeroSelfSimilarProfile = zeroFields := by
  change BoussinesqFields.mk _ _ _ = BoussinesqFields.mk _ _ _
  congr
  · funext x t
    simp [zeroSelfSimilarProfile, backwardSelfSimilarAnsatz,
      scaledProfileAnsatz]
  · funext x t
    simp [zeroSelfSimilarProfile, backwardSelfSimilarAnsatz,
      scaledProfileAnsatz]
  · funext x t
    simp [zeroSelfSimilarProfile, backwardSelfSimilarAnsatz,
      scaledProfileAnsatz]

end Boussinesq
