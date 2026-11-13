/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.PSystem.CharacteristicCurve
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import PDE.Hyperbolic.ConservationLaw.System.PSystem.WaveGeometry

/-!
# Self-similar rarefaction profiles for the one-dimensional p-system

For a genuinely nonlinear p-system, the state inside a rarefaction wave is
determined by the self-similar coordinate `ξ = x / t`. Its strain is selected
by inverting the relevant characteristic speed, and its velocity follows the
corresponding characteristic curve through the left state.

The inverse `rarefactionStrain` is totalized by `Function.invFun`, so analytic
statements carry an explicit hypothesis that the speed lies in the attained
range. On that range the profile is `C¹`, satisfies the rarefaction ODE, and
its self-similar lift solves the p-system pointwise away from `t = 0`.

The profile is the one in the proof of Theorem 1 of Evans, §11.2.2. There the rarefaction is
`v(Gₖ(x/t))`, where `v` solves the eigenvector equation (6) of §11.2.1 and `Gₖ` inverts
`Fₖ' = λₖ ∘ v`, (8)-(9), so the `k`th characteristic speed of the state equals the similarity
variable. For the p-system the strain is itself a parameter along the curve, and we invert the
speed as a function of the strain.

## Main results

* `rarefactionSpeed`, `rarefactionStrain`: the `k`th characteristic speed
  `∓√p'(v)` as a function of strain, and its inverse. When `p' > 0` and
  `p'' > 0` the speed is strictly monotone with nonvanishing derivative, so
  the inverse is `C¹` on the attained range (`contDiffAt_rarefactionStrain`).
* `rarefactionProfile`: the state at similarity speed `ξ`, reached by
  following the `k`th characteristic curve from `left` to the selected
  strain, so that `λₖ(w(ξ)) = ξ` (`rarefactionSpeed_rarefactionProfile`).
* `rarefactionProfile_ode`: the tangent `w'(ξ)` is an eigenvector of the flux
  Jacobian with eigenvalue `ξ`, that is, `DF(w(ξ)) w'(ξ) = ξ w'(ξ)`.
* `fluxResidual_selfSimilar_rarefactionProfile_eq_zero`: consequently the
  self-similar lift `(t, x) ↦ w(x / t)` solves the p-system pointwise for
  `t ≠ 0` wherever `x / t` is an attained speed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equations (6)-(9); §11.2.2, proof of Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

open PDE.Hyperbolic.ConservationLaw.System

/-- The `k`th characteristic speed as a function of strain. -/
def rarefactionSpeed
    (stress : ℝ → ℝ) (k : Fin 2) (strain : ℝ) : ℝ :=
  characteristicSpeed (soundSpeed stress strain) k

/-- The family-zero characteristic speed is `-c(v) = -√p'(v)`. -/
@[simp]
theorem rarefactionSpeed_zero (stress : ℝ → ℝ) (strain : ℝ) :
    rarefactionSpeed stress 0 strain = -soundSpeed stress strain := by
  simp [rarefactionSpeed, characteristicSpeed]

/-- The family-one characteristic speed is `c(v) = √p'(v)`. -/
@[simp]
theorem rarefactionSpeed_one (stress : ℝ → ℝ) (strain : ℝ) :
    rarefactionSpeed stress 1 strain = soundSpeed stress strain := by
  simp [rarefactionSpeed, characteristicSpeed]

/-- The characteristic speed is `C¹` as a function of strain. -/
theorem contDiff_rarefactionSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) :
    ContDiff ℝ 1 (rarefactionSpeed stress k) := by
  fin_cases k
  · change ContDiff ℝ 1 (fun v ↦ -soundSpeed stress v)
    exact (contDiff_soundSpeed hstress hpositive).neg
  · change ContDiff ℝ 1 (soundSpeed stress)
    exact contDiff_soundSpeed hstress hpositive

/-- Derivative of the `k`th characteristic speed with respect to strain. -/
theorem hasDerivAt_rarefactionSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) (strain : ℝ) :
    HasDerivAt (rarefactionSpeed stress k) (if k = 0 then -(deriv (deriv stress) strain /
      (2 * soundSpeed stress strain)) else deriv (deriv stress) strain /
      (2 * soundSpeed stress strain)) strain := by
  fin_cases k
  · change HasDerivAt (fun v ↦ -soundSpeed stress v) (-(deriv (deriv stress) strain /
        (2 * soundSpeed stress strain))) strain
    exact (hasDerivAt_soundSpeed hstress (hpositive strain)).neg
  · change HasDerivAt (soundSpeed stress) (deriv (deriv stress) strain /
        (2 * soundSpeed stress strain)) strain
    exact hasDerivAt_soundSpeed hstress (hpositive strain)

/-- Formula for the derivative of the `k`th characteristic speed. -/
theorem deriv_rarefactionSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) (strain : ℝ) :
    deriv (rarefactionSpeed stress k) strain = if k = 0 then
      -(deriv (deriv stress) strain / (2 * soundSpeed stress strain)) else deriv (deriv stress)
      strain / (2 * soundSpeed stress strain) :=
  (hasDerivAt_rarefactionSpeed hstress hpositive k strain).deriv

/-- Positive `p''` makes every characteristic speed injective as a function
of strain. Family zero is strictly decreasing and family one is strictly
increasing. -/
theorem rarefactionSpeed_injective {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2) :
    Function.Injective (rarefactionSpeed stress k) := by
  have hsound := strictMono_soundSpeed hstress hpositive hsecond
  fin_cases k
  · intro v w hspeed
    change -soundSpeed stress v = -soundSpeed stress w at hspeed
    exact hsound.injective (neg_inj.mp hspeed)
  · change Function.Injective (soundSpeed stress)
    exact hsound.injective

/-- The strain derivative of a characteristic speed never vanishes in the
genuinely nonlinear regime. -/
theorem deriv_rarefactionSpeed_ne_zero {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (strain : ℝ) :
    deriv (rarefactionSpeed stress k) strain ≠ 0 := by
  rw [deriv_rarefactionSpeed hstress hpositive]
  have hcoefficient : 0 < deriv (deriv stress) strain / (2 * soundSpeed stress strain) :=
    div_pos (hsecond strain) (mul_pos (by norm_num) (soundSpeed_pos (hpositive strain)))
  fin_cases k
  · exact neg_ne_zero.mpr hcoefficient.ne'
  · exact hcoefficient.ne'

/-- The strain selected by a self-similar speed.

Outside the range of `rarefactionSpeed`, this uses the arbitrary value built
into `Function.invFun`; all analytic results below include a range
hypothesis. -/
def rarefactionStrain
    (stress : ℝ → ℝ) (k : Fin 2) (speed : ℝ) : ℝ :=
  Function.invFun (rarefactionSpeed stress k) speed

/-- Inverting the speed of a strain returns that strain. -/
@[simp]
theorem rarefactionStrain_rarefactionSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (strain : ℝ) :
    rarefactionStrain stress k (rarefactionSpeed stress k strain) = strain :=
  Function.leftInverse_invFun (rarefactionSpeed_injective hstress hpositive hsecond k) strain

/-- A speed in the range is recovered from its selected strain. -/
theorem rarefactionSpeed_rarefactionStrain {stress : ℝ → ℝ} (k : Fin 2) {speed : ℝ}
    (hspeed : speed ∈ Set.range (rarefactionSpeed stress k)) :
    rarefactionSpeed stress k (rarefactionStrain stress k speed) = speed :=
  Function.invFun_eq hspeed

/-- Speeds between two attained endpoint speeds remain in the range. -/
theorem mem_range_rarefactionSpeed_of_mem_Icc {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (k : Fin 2) (leftStrain rightStrain : ℝ) {speed : ℝ}
    (hspeed : speed ∈
      Set.Icc (rarefactionSpeed stress k leftStrain) (rarefactionSpeed stress k rightStrain)) :
    speed ∈ Set.range (rarefactionSpeed stress k) := by
  have hc := continuous_soundSpeed (hstress.of_le (by norm_num))
  have hcontinuous : ContinuousOn (rarefactionSpeed stress k) Set.univ := by
    fin_cases k
    · change ContinuousOn (fun v ↦ -soundSpeed stress v) Set.univ
      exact hc.neg.continuousOn
    · change ContinuousOn (soundSpeed stress) Set.univ
      exact hc.continuousOn
  rcases hcontinuous.surjOn_Icc (s := Set.univ) (a := leftStrain) (b := rightStrain)
      (by simp) (by simp) hspeed with
    ⟨strain, _, hstrain⟩
  exact ⟨strain, hstrain⟩

/-- The selected strain is differentiable at every attained speed. -/
theorem hasStrictDerivAt_rarefactionStrain {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    {speed : ℝ} (hspeed : speed ∈ Set.range (rarefactionSpeed stress k)) :
    HasStrictDerivAt (rarefactionStrain stress k)
      (deriv (rarefactionSpeed stress k) (rarefactionStrain stress k speed))⁻¹ speed := by
  let strain := rarefactionStrain stress k speed
  have hstrict : HasStrictDerivAt (rarefactionSpeed stress k)
        (deriv (rarefactionSpeed stress k) strain) strain :=
    (contDiff_rarefactionSpeed hstress hpositive k).contDiffAt
      |>.hasStrictDerivAt one_ne_zero
  have hleft : ∀ᶠ v in nhds strain, rarefactionStrain stress k (rarefactionSpeed stress k v) = v :=
    Filter.Eventually.of_forall fun v ↦ rarefactionStrain_rarefactionSpeed
        hstress hpositive hsecond k v
  have hinverse := hstrict.to_local_left_inverse (deriv_rarefactionSpeed_ne_zero
        hstress hpositive hsecond k strain) hleft
  have himage : rarefactionSpeed stress k strain = speed :=
    rarefactionSpeed_rarefactionStrain k hspeed
  simpa only [strain, himage] using hinverse

/-- The selected strain is `C¹` at every attained characteristic speed.

The inverse function theorem supplies a smooth local inverse near the
corresponding strain. Injectivity of the characteristic speed identifies that
local inverse with the totalized `Function.invFun` used by
`rarefactionStrain`. -/
theorem contDiffAt_rarefactionStrain {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    {speed : ℝ} (hspeed : speed ∈ Set.range (rarefactionSpeed stress k)) :
    ContDiffAt ℝ 1 (rarefactionStrain stress k) speed := by
  let strain := rarefactionStrain stress k speed
  let slope := deriv (rarefactionSpeed stress k) strain
  have hslope : slope ≠ 0 := deriv_rarefactionSpeed_ne_zero hstress hpositive hsecond k strain
  let derivativeEquiv : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 slope hslope)
  have hspeedContDiff : ContDiffAt ℝ 1 (rarefactionSpeed stress k) strain :=
    (contDiff_rarefactionSpeed hstress hpositive k).contDiffAt
  have hspeedDerivative : HasFDerivAt (rarefactionSpeed stress k)
        (derivativeEquiv : ℝ →L[ℝ] ℝ) strain := by
    have hderiv : HasDerivAt (rarefactionSpeed stress k) slope strain :=
      hspeedContDiff.differentiableAt_one.hasDerivAt
    exact hderiv.hasFDerivAt_equiv hslope
  have hlocal : ContDiffAt ℝ 1 (hspeedContDiff.localInverse hspeedDerivative (by norm_num))
        (rarefactionSpeed stress k strain) :=
    hspeedContDiff.to_localInverse hspeedDerivative (by norm_num)
  have hright : ∀ᶠ currentSpeed in nhds (rarefactionSpeed stress k strain),
        rarefactionSpeed stress k (hspeedContDiff.localInverse hspeedDerivative
              (by norm_num) currentSpeed) =
          currentSpeed :=
    (hspeedContDiff.hasStrictFDerivAt' hspeedDerivative (by norm_num)).eventually_right_inverse
  have heq : rarefactionStrain stress k =ᶠ[nhds (rarefactionSpeed stress k strain)]
        hspeedContDiff.localInverse hspeedDerivative (by norm_num) := by
    filter_upwards [hright] with currentSpeed hcurrent
    apply rarefactionSpeed_injective hstress hpositive hsecond k
    rw [rarefactionSpeed_rarefactionStrain k ⟨_, hcurrent⟩, hcurrent]
  have himage : rarefactionSpeed stress k strain = speed :=
    rarefactionSpeed_rarefactionStrain k hspeed
  rw [← himage]
  exact hlocal.congr_of_eventuallyEq heq

/-- The state inside a `k`-rarefaction fan through `left`.

The strain is selected from the self-similar speed, and the velocity is
obtained by following the explicit characteristic curve from `left`. -/
def rarefactionProfile
    (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2)
    (speed : ℝ) : ℝ^2 :=
  characteristicCurve stress k (rarefactionStrain stress k speed - left 0) left

/-- The strain of the rarefaction profile is the strain selected by inverting
the characteristic speed. -/
@[simp]
theorem rarefactionProfile_apply_zero (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2) (speed : ℝ) :
    rarefactionProfile stress k left speed 0 = rarefactionStrain stress k speed := by
  simp [rarefactionProfile]

/-- At a speed attained by `strain`, the profile reaches the corresponding
point of the characteristic curve. -/
theorem rarefactionProfile_rarefactionSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strain : ℝ) :
    rarefactionProfile stress k left (rarefactionSpeed stress k strain) =
      characteristicCurve stress k (strain - left 0) left := by
  simp [rarefactionProfile, rarefactionStrain_rarefactionSpeed hstress hpositive hsecond]

/-- The left fan speed gives the left state. -/
@[simp]
theorem rarefactionProfile_leftSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) :
    rarefactionProfile stress k left (rarefactionSpeed stress k (left 0)) = left := by
  simpa using rarefactionProfile_rarefactionSpeed hstress hpositive hsecond k left (left 0)

/-- The speed at the endpoint of a characteristic step gives that endpoint. -/
theorem rarefactionProfile_rightSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) (strength : ℝ) :
    rarefactionProfile stress k left (rarefactionSpeed stress k (left 0 + strength)) =
      characteristicCurve stress k strength left := by
  simpa using rarefactionProfile_rarefactionSpeed
      hstress hpositive hsecond k left (left 0 + strength)

/-- The profile has the prescribed characteristic speed throughout the fan. -/
theorem rarefactionSpeed_rarefactionProfile {stress : ℝ → ℝ} (k : Fin 2) (left : ℝ^2) {speed : ℝ}
    (hspeed : speed ∈ Set.range (rarefactionSpeed stress k)) :
    rarefactionSpeed stress k (rarefactionProfile stress k left speed 0) = speed := by
  rw [rarefactionProfile_apply_zero]
  exact rarefactionSpeed_rarefactionStrain k hspeed

/-- A Riemann invariant remains constant throughout its rarefaction profile. -/
theorem riemannInvariant_rarefactionProfile {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (base : ℝ) (k : Fin 2) (left : ℝ^2) (speed : ℝ) :
    riemannInvariant stress base k (rarefactionProfile stress k left speed) =
      riemannInvariant stress base k left :=
  riemannInvariant_characteristicCurve hstress base k left
    (rarefactionStrain stress k speed - left 0)

/-- Derivative of the rarefaction profile at an attained speed. -/
theorem hasDerivAt_rarefactionProfile {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) {speed : ℝ} (hspeed : speed ∈ Set.range (rarefactionSpeed stress k)) :
    HasDerivAt (rarefactionProfile stress k left) ((deriv (rarefactionSpeed stress k)
      (rarefactionStrain stress k speed))⁻¹ •
      rightEigenvector (soundSpeed stress (rarefactionStrain stress k speed)) k) speed := by
  have hstrain := (hasStrictDerivAt_rarefactionStrain hstress hpositive hsecond k hspeed).hasDerivAt
  have hstrength := hstrain.sub_const (left 0)
  have hcurve :=
    hasDerivAt_characteristicCurve (hstress.of_le (by norm_num)) k left
      (rarefactionStrain stress k speed - left 0)
  change HasDerivAt (fun currentSpeed ↦ characteristicCurve stress k
        (rarefactionStrain stress k currentSpeed - left 0) left)
    _ speed
  convert hcurve.scomp speed hstrength using 1 <;> first
    | rfl
    | simp only [characteristicCurve_apply_zero, add_sub_cancel]

/-- The p-system rarefaction profile is `C¹` at every attained
characteristic speed. -/
theorem contDiffAt_rarefactionProfile {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) {speed : ℝ} (hspeed : speed ∈ Set.range (rarefactionSpeed stress k)) :
    ContDiffAt ℝ 1 (rarefactionProfile stress k left) speed := by
  have hstrain := contDiffAt_rarefactionStrain hstress hpositive hsecond k hspeed
  have hstrength : ContDiffAt ℝ 1 (fun currentSpeed ↦
          rarefactionStrain stress k currentSpeed - left 0)
        speed := hstrain.sub contDiffAt_const
  have hinput : ContDiffAt ℝ 1 (fun currentSpeed ↦
          (rarefactionStrain stress k currentSpeed - left 0, left))
        speed := hstrength.prodMk contDiffAt_const
  have hcurve : ContDiffAt ℝ 1 (fun input : ℝ × ℝ^2 ↦ characteristicCurve stress k input.1 input.2)
        (rarefactionStrain stress k speed - left 0, left) :=
    (contDiff_characteristicCurve (hstress.of_le (by norm_num)) k).contDiffAt
  have hcomposition : ContDiffAt ℝ 1 ((fun input : ℝ × ℝ^2 ↦
            characteristicCurve stress k input.1 input.2) ∘
          fun currentSpeed ↦ (rarefactionStrain stress k currentSpeed - left 0, left))
        speed := ContDiffAt.comp speed hcurve hinput
  change ContDiffAt ℝ 1 (fun currentSpeed ↦ characteristicCurve stress k
        (rarefactionStrain stress k currentSpeed - left 0) left) speed
  simpa only [Function.comp_def] using hcomposition

/-- The p-system rarefaction profile satisfies
`DF(w(ξ))w'(ξ) = ξw'(ξ)` at every attained speed. -/
theorem rarefactionProfile_ode {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2)
    (left : ℝ^2) {speed : ℝ} (hspeed : speed ∈ Set.range (rarefactionSpeed stress k)) :
    fderiv ℝ (flux stress) (rarefactionProfile stress k left speed)
      (curveTangent (rarefactionProfile stress k left) speed) =
      speed • curveTangent (rarefactionProfile stress k left) speed := by
  let field :=
    characteristicField stress (hstress.differentiable (by norm_num)) hpositive k
  let coefficient := (deriv (rarefactionSpeed stress k) (rarefactionStrain stress k speed))⁻¹
  have htangent : curveTangent (rarefactionProfile stress k left) speed = coefficient •
          field.rightEigenvector (rarefactionProfile stress k left speed) := by
    rw [curveTangent, (hasDerivAt_rarefactionProfile hstress hpositive hsecond k left hspeed).deriv]
    simp [coefficient, field, characteristicField]
  have hfieldSpeed : field.speed (rarefactionProfile stress k left speed) = speed := by
    change rarefactionSpeed stress k (rarefactionProfile stress k left speed 0) = speed
    exact rarefactionSpeed_rarefactionProfile k left hspeed
  calc
    fderiv ℝ (flux stress) (rarefactionProfile stress k left speed)
        (curveTangent (rarefactionProfile stress k left) speed) =
      fderiv ℝ (flux stress) (rarefactionProfile stress k left speed) (coefficient •
          field.rightEigenvector (rarefactionProfile stress k left speed)) := by
          rw [htangent]
    _ = coefficient • fderiv ℝ (flux stress) (rarefactionProfile stress k left speed)
          (field.rightEigenvector (rarefactionProfile stress k left speed)) := by
          rw [map_smul]
    _ = coefficient • (field.speed (rarefactionProfile stress k left speed) • field.rightEigenvector
            (rarefactionProfile stress k left speed)) :=
          congrArg (fun v : ℝ^2 ↦ coefficient • v) ((field.eigenvector
              (rarefactionProfile stress k left speed)).apply_eq_smul)
    _ = field.speed (rarefactionProfile stress k left speed) • (coefficient • field.rightEigenvector
            (rarefactionProfile stress k left speed)) := by
          simp only [smul_smul]
          rw [mul_comm]
    _ = speed • curveTangent (rarefactionProfile stress k left) speed := by
          rw [hfieldSpeed, htangent]

/-- The self-similar rarefaction solves the conservative p-system at points
whose similarity coordinate is an attained characteristic speed. -/
theorem fluxResidual_selfSimilar_rarefactionProfile_eq_zero {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2) (left : ℝ^2) {p : ℝ^2} (htime : p 0 ≠ 0)
    (hspeed : similarityVariable p ∈ Set.range (rarefactionSpeed stress k)) :
    fluxResidual (flux stress) (selfSimilarWave (rarefactionProfile stress k left)) p = 0 := by
  apply fluxResidual_selfSimilarWave_eq_zero htime
  · exact differentiableAt_flux (hstress.differentiable (by norm_num)
        (rarefactionProfile stress k left (similarityVariable p) 0))
  · exact (hasDerivAt_rarefactionProfile hstress hpositive hsecond k left hspeed).differentiableAt
  · exact rarefactionProfile_ode hstress hpositive hsecond k left hspeed

/-- Interval form of the pointwise rarefaction theorem. The endpoint order is
part of the interval hypothesis; the family-specific orientation lemmas in
`PSystem.WaveGeometry` establish it for physical rarefactions. -/
theorem fluxResidual_selfSimilar_rarefactionProfile_eq_zero_of_mem_Icc {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (k : Fin 2) (left : ℝ^2) (strength : ℝ) {p : ℝ^2}
    (htime : p 0 ≠ 0)
    (hspeed : similarityVariable p ∈ Set.Icc (rarefactionSpeed stress k (left 0))
      (rarefactionSpeed stress k (left 0 + strength))) :
    fluxResidual (flux stress) (selfSimilarWave (rarefactionProfile stress k left)) p = 0 := by
  apply fluxResidual_selfSimilar_rarefactionProfile_eq_zero hstress hpositive hsecond k left htime
  exact mem_range_rarefactionSpeed_of_mem_Icc
    hstress k (left 0) (left 0 + strength) hspeed

end PDE.Hyperbolic.ConservationLaw.System.PSystem
