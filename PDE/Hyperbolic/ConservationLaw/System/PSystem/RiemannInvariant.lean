/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.PSystem
public import PDE.Hyperbolic.ConservationLaw.System.SimpleWave
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import CAS.ExactTactic

/-!
# Riemann invariants for the p-system

For the p-system flux `F(v, w) = (-w, -p(v))`, set
`c(v) = √p'(v)` and `A(v) = ∫ x in base..v, c(x)`. When `p' > 0`, the
ordered characteristic fields are

* `λ₀ = -c`, `r₀ = (1, c)`, with invariant `w - A(v)`;
* `λ₁ = c`, `r₁ = (1, -c)`, with invariant `w + A(v)`.

The flux is the p-system flux (7) of Evans, §11.1, and each invariant satisfies the condition
(2') that defines Riemann invariants of a system of two equations in §11.3.1. Although
`Real.sqrt` is totalized, the characteristic-field and invariance results assume `p' > 0`, the
strictly hyperbolic regime. Global `C¹` regularity makes `p'`, hence `c`, continuous for the
fundamental theorem of calculus; the characteristic field itself only requires
differentiability. The acoustic primitive is strictly increasing in this regime, so the two
Riemann invariants jointly determine the state. The invariants are constant along global
Mathlib integral curves of the eigenvector fields, as in (3) of §11.3.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1, Example 1, equation (7); §11.1.2, Example 1
  (continued); §11.3.1, definition of Riemann invariants, equations (2)-(3).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

/-- Sound speed `c(v) = √p'(v)` for the p-system sign convention. -/
def soundSpeed (stress : ℝ → ℝ) (v : ℝ) : ℝ :=
  √(deriv stress v)

/-- Positivity of the stress derivative gives a positive sound speed. -/
theorem soundSpeed_pos {stress : ℝ → ℝ} {v : ℝ} (hpositive : 0 < deriv stress v) :
    0 < soundSpeed stress v :=
  Real.sqrt_pos.2 hpositive

/-- A `C¹` stress law has continuous sound speed. -/
theorem continuous_soundSpeed {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) :
    Continuous (soundSpeed stress) := by
  change Continuous (fun v ↦ √(deriv stress v))
  exact hstress.continuous_deriv_one.sqrt

/-- A primitive of the sound speed, normalized to vanish at `base`. -/
def acousticPrimitive
    (stress : ℝ → ℝ) (base v : ℝ) : ℝ :=
  ∫ x in base..v, soundSpeed stress x

/-- The acoustic primitive has derivative `c(v)`. -/
theorem hasDerivAt_acousticPrimitive {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (base v : ℝ) :
    HasDerivAt (acousticPrimitive stress base) (soundSpeed stress v) v := by
  have hsound := continuous_soundSpeed hstress
  change HasDerivAt (fun u ↦ ∫ x in base..u, soundSpeed stress x) (soundSpeed stress v) v
  exact intervalIntegral.integral_hasDerivAt_right (hsound.intervalIntegrable base v)
    hsound.aestronglyMeasurable.stronglyMeasurableAtFilter hsound.continuousAt

/-- The derivative of the acoustic primitive is the sound speed. -/
theorem deriv_acousticPrimitive {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (base v : ℝ) :
    deriv (acousticPrimitive stress base) v = soundSpeed stress v :=
  (hasDerivAt_acousticPrimitive hstress base v).deriv

/-- The acoustic primitive is continuously differentiable, with derivative
equal to the sound speed. -/
theorem contDiff_acousticPrimitive {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (base : ℝ) :
    ContDiff ℝ 1 (acousticPrimitive stress base) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun v ↦ (hasDerivAt_acousticPrimitive hstress base v).differentiableAt, ?_⟩
  have hderiv : deriv (acousticPrimitive stress base) = soundSpeed stress := by
    funext v
    exact deriv_acousticPrimitive hstress base v
  rw [hderiv]
  exact continuous_soundSpeed hstress

/-- A globally positive stress derivative makes the acoustic primitive
strictly increasing. -/
theorem strictMono_acousticPrimitive {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (base : ℝ) :
    StrictMono (acousticPrimitive stress base) := by
  apply strictMono_of_hasDerivAt_pos
  · exact hasDerivAt_acousticPrimitive hstress base
  · exact fun v ↦ soundSpeed_pos (hpositive v)

/-- The `k`th global characteristic field of the p-system.

Strict positivity records strict hyperbolicity at every state. Its global
form, rather than a hypothesis at one state, reflects that `CharacteristicField`
is a field on the whole state space. -/
def characteristicField
    (stress : ℝ → ℝ) (hstress : Differentiable ℝ stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) :
    CharacteristicField (flux stress) where
  flux_differentiable := fun state ↦
    differentiableAt_flux (hstress (state 0))
  speed := fun state ↦
    characteristicSpeed (soundSpeed stress (state 0)) k
  rightEigenvector := fun state ↦
    rightEigenvector (soundSpeed stress (state 0)) k
  eigenvector := fun state ↦ by
    simpa [soundSpeed] using
      hasEigenvector_fderiv_flux
        (hstress (state 0)) (hpositive (state 0)).le k

/-- The Riemann invariant associated with the `k`th p-system field.

For family zero this is `w - A(v)`; for family one it is `w + A(v)`. -/
def riemannInvariant
    (stress : ℝ → ℝ) (base : ℝ) (k : Fin 2)
    (state : ℝ^2) : ℝ :=
  if k = 0 then state 1 - acousticPrimitive stress base (state 0)
  else state 1 + acousticPrimitive stress base (state 0)

/-- The family-zero Riemann invariant is `w - A(v)`. -/
@[simp]
theorem riemannInvariant_zero (stress : ℝ → ℝ) (base : ℝ) (state : ℝ^2) :
    riemannInvariant stress base 0 state = state 1 - acousticPrimitive stress base (state 0) := by
  simp [riemannInvariant]

/-- The family-one Riemann invariant is `w + A(v)`. -/
@[simp]
theorem riemannInvariant_one (stress : ℝ → ℝ) (base : ℝ) (state : ℝ^2) :
    riemannInvariant stress base 1 state = state 1 + acousticPrimitive stress base (state 0) := by
  simp [riemannInvariant]

/-- The sum of the two Riemann invariants recovers twice the velocity. -/
theorem riemannInvariant_zero_add_one (stress : ℝ → ℝ) (base : ℝ) (state : ℝ^2) :
    riemannInvariant stress base 0 state + riemannInvariant stress base 1 state = 2 * state 1 := by
  simp only [riemannInvariant_zero, riemannInvariant_one]
  ring

/-- The difference of the two Riemann invariants recovers twice the acoustic
coordinate. -/
theorem riemannInvariant_one_sub_zero (stress : ℝ → ℝ) (base : ℝ) (state : ℝ^2) :
    riemannInvariant stress base 1 state - riemannInvariant stress base 0 state =
      2 * acousticPrimitive stress base (state 0) := by
  simp only [riemannInvariant_zero, riemannInvariant_one]
  ring

/-- Recover the velocity from the two p-system Riemann invariants. -/
theorem velocity_eq_riemannInvariant_average (stress : ℝ → ℝ) (base : ℝ) (state : ℝ^2) :
    state 1 =
      (riemannInvariant stress base 0 state + riemannInvariant stress base 1 state) / 2 := by
  rw [riemannInvariant_zero_add_one]
  ring

/-- Recover the acoustic coordinate from the two p-system Riemann
invariants. -/
theorem acousticPrimitive_eq_riemannInvariant_halfDifference
    (stress : ℝ → ℝ) (base : ℝ) (state : ℝ^2) :
    acousticPrimitive stress base (state 0) =
      (riemannInvariant stress base 1 state - riemannInvariant stress base 0 state) / 2 := by
  rw [riemannInvariant_one_sub_zero]
  ring

/-- Under strict hyperbolicity, the two p-system Riemann invariants jointly
determine the state. -/
theorem riemannInvariants_injective {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (base : ℝ) :
    Function.Injective (fun state : ℝ^2 ↦ fun k : Fin 2 ↦
      riemannInvariant stress base k state) := by
  intro state₁ state₂ hstate
  have hzero := congrFun hstate (0 : Fin 2)
  have hone := congrFun hstate (1 : Fin 2)
  simp only [riemannInvariant, ↓reduceIte] at hzero
  norm_num [riemannInvariant] at hone
  have hvelocity : state₁ 1 = state₂ 1 := by
    linarith
  have hacoustic : acousticPrimitive stress base (state₁ 0) =
        acousticPrimitive stress base (state₂ 0) := by
    linarith
  have hstrain : state₁ 0 = state₂ 0 :=
    (strictMono_acousticPrimitive hstress hpositive base).injective hacoustic
  ext i
  fin_cases i
  · exact hstrain
  · exact hvelocity

/-- A p-system Riemann invariant is globally `C¹` for a `C¹` stress law. -/
theorem contDiff_riemannInvariant {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (base : ℝ)
    (k : Fin 2) :
    ContDiff ℝ 1 (riemannInvariant stress base k) := by
  have hvelocity : ContDiff ℝ 1 (fun state : ℝ^2 ↦ state 1) := by
    cas
  have hstrain : ContDiff ℝ 1 (fun state : ℝ^2 ↦ state 0) := by
    cas
  have hacoustic : ContDiff ℝ 1 (fun state : ℝ^2 ↦ acousticPrimitive stress base (state 0)) :=
    (contDiff_acousticPrimitive hstress base).comp hstrain
  fin_cases k
  · exact hvelocity.sub hacoustic
  · exact hvelocity.add hacoustic

/-- The two p-system Riemann invariants are globally differentiable for a
`C¹` stress law. -/
theorem differentiable_riemannInvariant {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (base : ℝ)
    (k : Fin 2) :
    Differentiable ℝ (riemannInvariant stress base k) :=
  (contDiff_riemannInvariant hstress base k).differentiable one_ne_zero

/-- Explicit differential of the `k`th p-system Riemann invariant. -/
theorem fderiv_riemannInvariant_apply {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress) (base : ℝ)
    (k : Fin 2) (state direction : ℝ^2) :
    fderiv ℝ (riemannInvariant stress base k) state direction = if k =
      0 then direction 1 - soundSpeed stress (state 0) * direction 0 else direction 1 +
      soundSpeed stress (state 0) * direction 0 := by
  have hvelocity := PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) state (1 : Fin 2)
  have hacoustic := (hasDerivAt_acousticPrimitive hstress base (state 0)).hasFDerivAt.comp state
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) state (0 : Fin 2))
  fin_cases k
  · change fderiv ℝ (fun y : ℝ^2 ↦ y 1 - acousticPrimitive stress base (y 0)) state direction =
        direction 1 - soundSpeed stress (state 0) * direction 0
    have h := congrArg (fun L : ℝ^2 →L[ℝ] ℝ ↦ L direction) (hvelocity.sub hacoustic).fderiv
    have hfun : ((fun y : ℝ^2 ↦ y 1) - (acousticPrimitive stress base ∘ fun y : ℝ^2 ↦ y 0)) =
          fun y : ℝ^2 ↦ y 1 - acousticPrimitive stress base (y 0) := by
      rfl
    rw [hfun] at h
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
      EuclideanSpace.proj, smul_eq_mul, mul_comm] using h
  · change fderiv ℝ (fun y : ℝ^2 ↦ y 1 + acousticPrimitive stress base (y 0)) state direction =
        direction 1 + soundSpeed stress (state 0) * direction 0
    have h := congrArg (fun L : ℝ^2 →L[ℝ] ℝ ↦ L direction) (hvelocity.add hacoustic).fderiv
    have hfun : ((fun y : ℝ^2 ↦ y 1) + (acousticPrimitive stress base ∘ fun y : ℝ^2 ↦ y 0)) =
          fun y : ℝ^2 ↦ y 1 + acousticPrimitive stress base (y 0) := by
      rfl
    rw [hfun] at h
    simpa [Function.comp_def, ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv,
      EuclideanSpace.proj, smul_eq_mul, mul_comm] using h

/-- The signed acoustic primitives are Riemann invariants for the
corresponding p-system characteristic fields. -/
theorem isRiemannInvariant_riemannInvariant {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (base : ℝ) (k : Fin 2) :
    (characteristicField stress (hstress.differentiable one_ne_zero) hpositive k).IsRiemannInvariant
      (riemannInvariant stress base k) := by
  constructor
  · exact differentiable_riemannInvariant hstress base k
  · intro state
    rw [fderiv_riemannInvariant_apply hstress]
    fin_cases k <;> simp [characteristicField, rightEigenvector]

/-- A p-system Riemann invariant is constant along every global integral
curve of its corresponding characteristic field. -/
theorem riemannInvariant_eq_on_integralCurve {stress : ℝ → ℝ} (hstress : ContDiff ℝ 1 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (base : ℝ) (k : Fin 2) {curve : ℝ → ℝ^2}
    (hcurve : IsIntegralCurve curve
      (characteristicField stress (hstress.differentiable one_ne_zero) hpositive k).vectorField)
    (s₁ s₂ : ℝ) :
    riemannInvariant stress base k (curve s₁) = riemannInvariant stress base k (curve s₂) :=
  (isRiemannInvariant_riemannInvariant hstress hpositive base k).eq_on_integralCurve hcurve s₁ s₂

end PDE.Hyperbolic.ConservationLaw.System.PSystem
