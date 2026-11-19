/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.PSystem.CharacteristicCurve
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import CAS.ExactTactic

/-!
# Genuine nonlinearity for the one-dimensional p-system

We compute the wave geometry of the explicit p-system characteristic fields
used in the Riemann problem. In the strictly hyperbolic region,

`c(v) = √p'(v)` and `c'(v) = p''(v) / (2c(v))`.

The two characteristic speeds are `-c` and `c`. Their derivatives in the
corresponding right-eigenvector directions are therefore `-c'` and `c'`.
Consequently, either field is genuinely nonlinear exactly where `p''` does
not vanish. When `p'' > 0`, the sound speed is strictly increasing. The
explicit characteristic curves from `PSystem.CharacteristicCurve` then give
rarefaction connections in the negative direction for family zero and in the
positive direction for family one.

The speeds `∓c` are those of Evans, §11.1.2, Example 1 (continued), and genuine nonlinearity is
the condition (11) of §11.2.1. The rarefaction connections join `u_l` to the states
`u_r ∈ Rₖ⁺(u_l)` of Theorem 1 of §11.2.2.

## Main results

* `deriv_soundSpeed`, `strictMono_soundSpeed`: `c' = p'' / (2c)`, and `c` is
  strictly increasing when `p'' > 0`.
* `fderiv_characteristicSpeed_rightEigenvector`: `∇λₖ · rₖ = ∓c'`, so by
  `isGenuinelyNonlinearAt_characteristicField` each field is genuinely
  nonlinear wherever `p'' ≠ 0`.
* `isRarefactionConnection_characteristicCurve_zero_of_neg`,
  `isRarefactionConnection_characteristicCurve_one_of_pos`: with `p'' > 0`,
  the family-zero characteristic curve traversed in the negative direction
  and the family-one curve in the positive direction are rarefaction
  connections, hence admissible elementary connections.
* `characteristicWaveMap_elementaryConnections_of_neg_pos`: in the
  two-rarefaction quadrant the ordered characteristic wave map is a chain of
  two admissible connections.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.2, Example 1 (continued); §11.2.1, equation (11)
  and the notation `Rₖ⁺`; §11.2.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

open PDE.Hyperbolic.ConservationLaw.System

/-- The sound speed has derivative `p'' / (2c)` in the strictly hyperbolic
region. -/
theorem hasDerivAt_soundSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress) {v : ℝ}
    (hpositive : 0 < deriv stress v) :
    HasDerivAt (soundSpeed stress) (deriv (deriv stress) v / (2 * soundSpeed stress v)) v := by
  change HasDerivAt (fun x ↦ √(deriv stress x)) (deriv (deriv stress) v / (2 * √(deriv stress v))) v
  exact (hstress.differentiable_deriv_two v).hasDerivAt.sqrt hpositive.ne'

/-- A `C²` stress law with positive derivative has `C¹` sound speed. -/
theorem contDiff_soundSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) :
    ContDiff ℝ 1 (soundSpeed stress) := by
  change ContDiff ℝ 1 (fun v ↦ √(deriv stress v))
  exact hstress.deriv'.sqrt fun v ↦ (hpositive v).ne'

/-- The derivative of the sound speed is `p'' / (2c)` in the strictly
hyperbolic region. -/
theorem deriv_soundSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress) {v : ℝ}
    (hpositive : 0 < deriv stress v) :
    deriv (soundSpeed stress) v = deriv (deriv stress) v / (2 * soundSpeed stress v) :=
  (hasDerivAt_soundSpeed hstress hpositive).deriv

/-- A positive second stress derivative makes the sound speed strictly
increasing throughout the strictly hyperbolic region. -/
theorem strictMono_soundSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (hsecond : ∀ v, 0 < deriv (deriv stress) v) :
    StrictMono (soundSpeed stress) := by
  apply strictMono_of_hasDerivAt_pos
  · exact fun v ↦ hasDerivAt_soundSpeed hstress (hpositive v)
  · exact fun v ↦ div_pos (hsecond v) (mul_pos (by norm_num) (soundSpeed_pos (hpositive v)))

/-- Differential of a p-system characteristic speed on state space. -/
theorem fderiv_characteristicSpeed_apply {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) (state direction : ℝ^2) :
    fderiv ℝ
        (fun y : ℝ^2 ↦
          characteristicSpeed (soundSpeed stress (y 0)) k)
        state direction =
      if k = 0 then
        -(deriv (deriv stress) (state 0) /
          (2 * soundSpeed stress (state 0)) * direction 0)
      else
        deriv (deriv stress) (state 0) /
          (2 * soundSpeed stress (state 0)) * direction 0 := by
  let coefficient := deriv (deriv stress) (state 0) / (2 * soundSpeed stress (state 0))
  have hsound : HasDerivAt (soundSpeed stress) coefficient (state 0) := by
    simpa only [coefficient] using hasDerivAt_soundSpeed hstress (hpositive (state 0))
  have hcomp : HasFDerivAt (fun y : ℝ^2 ↦ soundSpeed stress (y 0)) (coefficient •
          (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ))
        state := by
    simpa [Function.comp_def] using hsound.comp_hasFDerivAt state (PiLp.hasFDerivAt_apply
          (𝕜 := ℝ) (2 : ENNReal) state (0 : Fin 2))
  by_cases hk : k = 0
  · subst k
    simp only [characteristicSpeed, ite_true]
    rw [fderiv_fun_neg, hcomp.fderiv]
    simp [coefficient, EuclideanSpace.proj, smul_eq_mul]
  · simp only [characteristicSpeed, hk, ite_false]
    rw [hcomp.fderiv]
    simp [coefficient, EuclideanSpace.proj, smul_eq_mul]

/-- The derivative of a characteristic speed in its right-eigenvector
direction is the signed sound-speed derivative. -/
theorem fderiv_characteristicSpeed_rightEigenvector {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) (state : ℝ^2) :
    fderiv ℝ
        (fun y : ℝ^2 ↦
          characteristicSpeed (soundSpeed stress (y 0)) k)
        state (rightEigenvector (soundSpeed stress (state 0)) k) =
      if k = 0 then
        -(deriv (deriv stress) (state 0) /
          (2 * soundSpeed stress (state 0)))
      else
        deriv (deriv stress) (state 0) /
          (2 * soundSpeed stress (state 0)) := by
  rw [fderiv_characteristicSpeed_apply hstress hpositive]
  simp [rightEigenvector]

/-- The first p-system family has directional speed derivative `-p''/(2c)`. -/
theorem fderiv_characteristicSpeed_rightEigenvector_zero {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (state : ℝ^2) :
    fderiv ℝ (fun y : ℝ^2 ↦ characteristicSpeed (soundSpeed stress (y 0)) 0) state
      (rightEigenvector (soundSpeed stress (state 0)) 0) =
      -(deriv (deriv stress) (state 0) / (2 * soundSpeed stress (state 0))) := by
  simpa using fderiv_characteristicSpeed_rightEigenvector hstress hpositive (0 : Fin 2) state

/-- The second p-system family has directional speed derivative `p''/(2c)`. -/
theorem fderiv_characteristicSpeed_rightEigenvector_one {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (state : ℝ^2) :
    fderiv ℝ (fun y : ℝ^2 ↦ characteristicSpeed (soundSpeed stress (y 0)) 1) state
      (rightEigenvector (soundSpeed stress (state 0)) 1) =
      deriv (deriv stress) (state 0) / (2 * soundSpeed stress (state 0)) := by
  simpa using fderiv_characteristicSpeed_rightEigenvector hstress hpositive (1 : Fin 2) state

/-- Positive `p''` makes the first characteristic speed decrease along its
right eigenvector. -/
theorem fderiv_characteristicSpeed_rightEigenvector_zero_neg {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (state : ℝ^2)
    (hsecond : 0 < deriv (deriv stress) (state 0)) :
    fderiv ℝ (fun y : ℝ^2 ↦ characteristicSpeed (soundSpeed stress (y 0)) 0) state
      (rightEigenvector (soundSpeed stress (state 0)) 0) < 0 := by
  rw [fderiv_characteristicSpeed_rightEigenvector_zero hstress hpositive]
  exact neg_neg_of_pos <| div_pos hsecond
      (mul_pos (by norm_num) (soundSpeed_pos (hpositive (state 0))))

/-- Positive `p''` makes the second characteristic speed increase along its
right eigenvector. -/
theorem fderiv_characteristicSpeed_rightEigenvector_one_pos {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (state : ℝ^2)
    (hsecond : 0 < deriv (deriv stress) (state 0)) :
    0 < fderiv ℝ (fun y : ℝ^2 ↦ characteristicSpeed (soundSpeed stress (y 0)) 1) state
      (rightEigenvector (soundSpeed stress (state 0)) 1) := by
  rw [fderiv_characteristicSpeed_rightEigenvector_one hstress hpositive]
  exact div_pos hsecond (mul_pos (by norm_num) (soundSpeed_pos (hpositive (state 0))))

/-- The directional derivative of either characteristic speed vanishes
exactly where the second stress derivative vanishes. -/
theorem fderiv_characteristicSpeed_rightEigenvector_ne_zero_iff {stress : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2)
    (state : ℝ^2) :
    fderiv ℝ (fun y : ℝ^2 ↦ characteristicSpeed (soundSpeed stress (y 0)) k) state
      (rightEigenvector (soundSpeed stress (state 0)) k) ≠ 0 ↔ deriv (deriv stress) (state 0) ≠
      0 := by
  rw [fderiv_characteristicSpeed_rightEigenvector hstress hpositive]
  have hdenominator : 2 * soundSpeed stress (state 0) ≠ 0 :=
    mul_ne_zero (by norm_num) (soundSpeed_pos (hpositive (state 0))).ne'
  by_cases hk : k = 0
  · subst k
    simp [hdenominator]
  · simp [hk, hdenominator]

/-- A nonzero second stress derivative makes each p-system characteristic
field genuinely nonlinear at the given state. -/
theorem isGenuinelyNonlinearAt_characteristicField
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2)
    (state : ℝ^2)
    (hsecond : deriv (deriv stress) (state 0) ≠ 0) :
    (characteristicField stress
      (hstress.differentiable (by norm_num)) hpositive k).IsGenuinelyNonlinearAt
      state := by
  have hsound : DifferentiableAt ℝ (fun y : ℝ^2 ↦ soundSpeed stress (y 0)) state := by
    have hsoundDeriv : DifferentiableAt ℝ (soundSpeed stress) (state 0) :=
      (hasDerivAt_soundSpeed hstress (hpositive (state 0))).differentiableAt
    have hcoordinate : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) state := by
      cas
    simpa [Function.comp_def] using hsoundDeriv.comp state hcoordinate
  constructor
  · by_cases hk : k = 0
    · subst k
      change DifferentiableAt ℝ (-fun y : ℝ^2 ↦ soundSpeed stress (y 0)) state
      exact hsound.neg
    · change DifferentiableAt ℝ (fun y : ℝ^2 ↦
          characteristicSpeed (soundSpeed stress (y 0)) k) state
      simpa only [characteristicSpeed, hk, ite_false] using hsound
  · change fderiv ℝ (fun y : ℝ^2 ↦ characteristicSpeed (soundSpeed stress (y 0)) k)
        state (rightEigenvector (soundSpeed stress (state 0)) k) ≠ 0
    exact (fderiv_characteristicSpeed_rightEigenvector_ne_zero_iff
        hstress hpositive k state).2 hsecond

/-- If `p''` never vanishes, both p-system characteristic fields are
genuinely nonlinear throughout state space. -/
theorem isGenuinelyNonlinear_characteristicField
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, deriv (deriv stress) v ≠ 0)
    (k : Fin 2) :
    (characteristicField stress
      (hstress.differentiable (by norm_num)) hpositive k).IsGenuinelyNonlinear :=
  fun state ↦ isGenuinelyNonlinearAt_characteristicField hstress hpositive k state
      (hsecond (state 0))

/-! ## Explicit rarefaction connections -/

/-- Along a negatively oriented family-zero curve, the characteristic speed
is strictly increasing. -/
theorem strictMono_characteristicSpeed_characteristicCurve_zero_of_neg
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (base : ℝ^2) {strength : ℝ} (hstrength : strength < 0) :
    StrictMono fun θ ↦
      (characteristicField stress
          (hstress.differentiable (by norm_num)) hpositive 0).speed
        (characteristicCurve stress 0 (θ * strength) base) := by
  intro θ₁ θ₂ hθ
  have hstrain : base 0 + θ₂ * strength < base 0 + θ₁ * strength :=
    add_lt_add_right (mul_lt_mul_of_neg_right hθ hstrength) _
  change -soundSpeed stress (base 0 + θ₁ * strength) < -soundSpeed stress (base 0 + θ₂ * strength)
  exact neg_lt_neg (strictMono_soundSpeed hstress hpositive hsecond hstrain)

/-- Along a positively oriented family-one curve, the characteristic speed
is strictly increasing. -/
theorem strictMono_characteristicSpeed_characteristicCurve_one_of_pos
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (base : ℝ^2) {strength : ℝ} (hstrength : 0 < strength) :
    StrictMono fun θ ↦
      (characteristicField stress
          (hstress.differentiable (by norm_num)) hpositive 1).speed
        (characteristicCurve stress 1 (θ * strength) base) := by
  intro θ₁ θ₂ hθ
  have hstrain : base 0 + θ₁ * strength < base 0 + θ₂ * strength :=
    add_lt_add_right (mul_lt_mul_of_pos_right hθ hstrength) _
  change soundSpeed stress (base 0 + θ₁ * strength) < soundSpeed stress (base 0 + θ₂ * strength)
  exact strictMono_soundSpeed hstress hpositive hsecond hstrain

/-- A negative family-zero strength increases the characteristic speed from
the base state to the endpoint of the explicit curve. -/
theorem characteristicSpeed_lt_characteristicCurve_zero_of_neg
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (base : ℝ^2) {strength : ℝ} (hstrength : strength < 0) :
    (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive 0).speed base <
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive 0).speed
        (characteristicCurve stress 0 strength base) := by
  simpa using strictMono_characteristicSpeed_characteristicCurve_zero_of_neg
      hstress hpositive hsecond base hstrength zero_lt_one

/-- A positive family-one strength increases the characteristic speed from
the base state to the endpoint of the explicit curve. -/
theorem characteristicSpeed_lt_characteristicCurve_one_of_pos
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (base : ℝ^2) {strength : ℝ} (hstrength : 0 < strength) :
    (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive 1).speed base <
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive 1).speed
        (characteristicCurve stress 1 strength base) := by
  simpa using strictMono_characteristicSpeed_characteristicCurve_one_of_pos
      hstress hpositive hsecond base hstrength zero_lt_one

/-- A negative family-zero strength gives an admissible p-system
rarefaction connection. -/
theorem isRarefactionConnection_characteristicCurve_zero_of_neg
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (base : ℝ^2) {strength : ℝ} (hstrength : strength < 0) :
    IsRarefactionConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive 0)
      base (characteristicCurve stress 0 strength base) := by
  have hstressOne : ContDiff ℝ 1 stress :=
    hstress.of_le (by norm_num)
  refine ⟨fun s ↦ characteristicCurve stress 0 s base, strength,
    Set.univ, isOpen_univ, Set.subset_univ _, ?_⟩
  refine ⟨?_, characteristicCurve_zero stress 0 base, ?_, rfl, ?_⟩
  · exact ((contDiff_characteristicCurve hstressOne 0).comp
      (contDiff_id.prodMk contDiff_const)).contDiffOn
  · exact (isIntegralCurve_characteristicFlow hstressOne hpositive 0 base).isIntegralCurveOn _
  exact (strictMono_characteristicSpeed_characteristicCurve_zero_of_neg
      hstress hpositive hsecond base hstrength).strictMonoOn (Set.Icc 0 1)

/-- A positive family-one strength gives an admissible p-system
rarefaction connection. -/
theorem isRarefactionConnection_characteristicCurve_one_of_pos
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (base : ℝ^2) {strength : ℝ} (hstrength : 0 < strength) :
    IsRarefactionConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive 1)
      base (characteristicCurve stress 1 strength base) := by
  have hstressOne : ContDiff ℝ 1 stress :=
    hstress.of_le (by norm_num)
  refine ⟨fun s ↦ characteristicCurve stress 1 s base, strength,
    Set.univ, isOpen_univ, Set.subset_univ _, ?_⟩
  refine ⟨?_, characteristicCurve_zero stress 1 base, ?_, rfl, ?_⟩
  · exact ((contDiff_characteristicCurve hstressOne 1).comp
      (contDiff_id.prodMk contDiff_const)).contDiffOn
  · exact (isIntegralCurve_characteristicFlow hstressOne hpositive 1 base).isIntegralCurveOn _
  exact (strictMono_characteristicSpeed_characteristicCurve_one_of_pos
      hstress hpositive hsecond base hstrength).strictMonoOn (Set.Icc 0 1)

/-- A negative family-zero characteristic strength is an elementary
rarefaction wave. -/
theorem isElementaryConnection_characteristicCurve_zero_of_neg
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (base : ℝ^2) {strength : ℝ} (hstrength : strength < 0) :
    IsElementaryConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) 0
      base (characteristicCurve stress 0 strength base) :=
  IsElementaryConnection.rarefaction (isRarefactionConnection_characteristicCurve_zero_of_neg
      hstress hpositive hsecond base hstrength)

/-- A positive family-one characteristic strength is an elementary
rarefaction wave. -/
theorem isElementaryConnection_characteristicCurve_one_of_pos
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (base : ℝ^2) {strength : ℝ} (hstrength : 0 < strength) :
    IsElementaryConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) 1
      base (characteristicCurve stress 1 strength base) :=
  IsElementaryConnection.rarefaction (isRarefactionConnection_characteristicCurve_one_of_pos
      hstress hpositive hsecond base hstrength)

/-- The first stage of the two-rarefaction characteristic map is an
admissible family-zero connection. -/
theorem isElementaryConnection_characteristicWaveMap_zero_of_neg
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left strength : ℝ^2) (hzero : strength 0 < 0) :
    IsElementaryConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) 0
      left (characteristicCurve stress 0 (strength 0) left) :=
  isElementaryConnection_characteristicCurve_zero_of_neg hstress hpositive hsecond left hzero

/-- The second stage of the two-rarefaction characteristic map is an
admissible family-one connection. -/
theorem isElementaryConnection_characteristicWaveMap_one_of_pos
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left strength : ℝ^2) (hone : 0 < strength 1) :
    IsElementaryConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) 1
      (characteristicCurve stress 0 (strength 0) left)
      (characteristicWaveMap stress left strength) := by
  simpa [characteristicWaveMap] using isElementaryConnection_characteristicCurve_one_of_pos
      hstress hpositive hsecond (characteristicCurve stress 0 (strength 0) left) hone

/-- In the two-rarefaction quadrant, the p-system characteristic wave map is
an ordered pair of admissible elementary connections. -/
theorem characteristicWaveMap_elementaryConnections_of_neg_pos
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left strength : ℝ^2)
    (hzero : strength 0 < 0) (hone : 0 < strength 1) :
    IsElementaryConnection
        (characteristicField stress
          (hstress.differentiable (by norm_num)) hpositive) 0
        left
        (characteristicCurve stress 0 (strength 0) left) ∧
      IsElementaryConnection
        (characteristicField stress
          (hstress.differentiable (by norm_num)) hpositive) 1
        (characteristicCurve stress 0 (strength 0) left)
        (characteristicWaveMap stress left strength) :=
  ⟨isElementaryConnection_characteristicWaveMap_zero_of_neg
        hstress hpositive hsecond left strength hzero,
      isElementaryConnection_characteristicWaveMap_one_of_pos
        hstress hpositive hsecond left strength hone⟩

end PDE.Hyperbolic.ConservationLaw.System.PSystem
