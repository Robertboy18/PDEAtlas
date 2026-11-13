/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.DSlope
public import PDE.Hyperbolic.ConservationLaw.System.PSystem.RiemannInvariant
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve
public import PDE.Hyperbolic.ConservationLaw.PlanarShock
public import PDE.Hyperbolic.ConservationLaw.System.EntropyWeak
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import PDE.Analysis.Scalar.ConvexIntegral
import PDE.Analysis.Scalar.DividedDifference
import PDE.Hyperbolic.ConservationLaw.System.PlanarShock
import CAS.ExactTactic

/-!
# Shock connections for the one-dimensional p-system

For the p-system flux `F(v, w) = (-w, -p(v))`, a discontinuity from
`(vL, wL)` to `(vR, wR)` with speed `s` satisfies Rankine–Hugoniot when

`s² = slope p vL vR` and `wR - wL = -s (vR - vL)`.

The shock speed is defined using Mathlib's differentiable slope `dslope`.
Away from the diagonal this is the usual secant slope, while at `vR = vL` it
is `p'(vL)`. Thus the two signs of its square root select the two
characteristic speeds even at zero jump. We prove the jump and Lax
conditions and strict mechanical-entropy dissipation.

When `p' > 0` and `p'' > 0`, strict convexity places the secant slope strictly
between the endpoint derivatives. Thus family zero gives a Lax shock for
`vL < vR`, while family one gives a Lax shock for `vR < vL`.

The jump condition is the Rankine–Hugoniot condition (20) of Evans, §11.1.1, and the shock
inequalities are the Lax entropy condition (42) of §11.2.3(b); the condition goes back to Lax's
1957 paper. The mechanical entropy pair is Example 2 of §11.4.2.

## Main results

* `shockSpeed`, `shockState`: the signed speed `∓√(dslope p vL vR)` and the
  Hugoniot endpoint `(vR, wL - s (vR - vL))` of family `k` through `left`.
* `rankineHugoniot_shockState`, `isWeakSolution_planarShock_shockState`: the
  endpoint satisfies the vector Rankine–Hugoniot condition, so the planar
  two-state profile is a global weak solution.
* `contDiff_shockState_strength`, `hasFDerivAt_shockState_strength_zero`:
  the Hugoniot branch is jointly `C¹` in strain increment and left state,
  with the right eigenvector as strength derivative at zero jump.
* `mechanicalEntropyProduction_shockState_zero_lt_zero`,
  `mechanicalEntropyProduction_shockState_one_lt_zero`: strict dissipation of
  the mechanical entropy across the physical shocks.
* `laxShock_shockState_zero_of_left_lt_right`,
  `laxShock_shockState_one_of_right_lt_left`: on the physical branches the
  shock speed lies strictly between the `k`th characteristic speeds of the
  right and left states, so these shocks are admissible elementary
  connections.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.1.1, equation (20); §11.2.3(b), equations (35)-(42);
  §11.4.2, Example 2.
  <https://doi.org/10.1090/gsm/019>
* P. D. Lax, *Hyperbolic systems of conservation laws II*, Comm. Pure Appl. Math. 10 (1957),
  537-566.
  <https://doi.org/10.1002/cpa.3160100406>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.PSystem

open PDE.Analysis.Scalar
open PDE.Hyperbolic.ConservationLaw.System
open Filter

/-- The p-system shock speed in family `k`.

The differentiable slope agrees with the stress secant slope for a nonzero
jump and extends it by `p'` on the diagonal. Consequently zero jump has the
corresponding characteristic speed rather than the artificial value zero. -/
def shockSpeed
    (stress : ℝ → ℝ) (k : Fin 2) (vL vR : ℝ) : ℝ :=
  characteristicSpeed (√(dslope stress vL vR)) k

/-- The family-zero shock speed is the negative square root of the stress
difference quotient `dslope stress vL vR`. -/
@[simp]
theorem shockSpeed_zero (stress : ℝ → ℝ) (vL vR : ℝ) :
    shockSpeed stress 0 vL vR = -√(dslope stress vL vR) := by
  simp [shockSpeed, characteristicSpeed]

/-- The family-one shock speed is the positive square root of the stress
difference quotient `dslope stress vL vR`. -/
@[simp]
theorem shockSpeed_one (stress : ℝ → ℝ) (vL vR : ℝ) :
    shockSpeed stress 1 vL vR = √(dslope stress vL vR) := by
  simp [shockSpeed, characteristicSpeed]

/-- At zero jump, the shock speed is the corresponding characteristic
speed. -/
@[simp]
theorem shockSpeed_self (stress : ℝ → ℝ) (k : Fin 2) (v : ℝ) :
    shockSpeed stress k v v = characteristicSpeed (√(deriv stress v)) k := by
  simp [shockSpeed]

/-- For a differentiable stress law, shock speed depends continuously on
the right strain as it approaches the left strain. -/
theorem continuousAt_shockSpeed_right {stress : ℝ → ℝ} {vL : ℝ}
    (hstress : DifferentiableAt ℝ stress vL) (k : Fin 2) :
    ContinuousAt (shockSpeed stress k vL) vL := by
  have hslope : ContinuousAt (dslope stress vL) vL := continuousAt_dslope_same.2 hstress
  fin_cases k
  · change ContinuousAt (fun vR ↦ -√(dslope stress vL vR)) vL
    exact hslope.sqrt.neg
  · change ContinuousAt (fun vR ↦ √(dslope stress vL vR)) vL
    exact hslope.sqrt

/-- The signed shock speed is jointly `C¹` in the strain increment and left
strain when the stress derivative is everywhere positive. -/
theorem contDiff_shockSpeed_strength {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ shockSpeed stress k p.2 (p.2 + p.1)) := by
  have hslope : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ dslope stress p.2 (p.2 + p.1)) :=
    (contDiff_dslope_add hstress).comp (contDiff_snd.prodMk contDiff_fst)
  have hsqrt : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ √(dslope stress p.2 (p.2 + p.1))) :=
    hslope.sqrt fun p ↦ (dslope_pos_of_deriv_pos hpositive p.2 (p.2 + p.1)).ne'
  fin_cases k
  · simpa [shockSpeed, characteristicSpeed] using hsqrt.neg
  · simpa [shockSpeed, characteristicSpeed] using hsqrt

/-- The right endpoint on the `k`th p-system Hugoniot branch through `left`,
parameterized by its strain coordinate `vR`. -/
def shockState
    (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2) (vR : ℝ) : ℝ^2 :=
  !₂[vR, left 1 - shockSpeed stress k (left 0) vR * (vR - left 0)]

/-- The strain of the Hugoniot endpoint is the prescribed right strain
`vR`. -/
@[simp]
theorem shockState_apply_zero (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2) (vR : ℝ) :
    shockState stress k left vR 0 = vR := by
  simp [shockState]

/-- The velocity of the Hugoniot endpoint is fixed by the second
Rankine–Hugoniot relation `wR - wL = -s (vR - vL)`. -/
@[simp]
theorem shockState_apply_one (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2) (vR : ℝ) :
    shockState stress k left vR 1 = left 1 - shockSpeed stress k (left 0) vR * (vR - left 0) := by
  simp [shockState]

/-- Choosing the left strain produces no jump. -/
@[simp]
theorem shockState_left_strain (stress : ℝ → ℝ) (k : Fin 2) (left : ℝ^2) :
    shockState stress k left (left 0) = left := by
  ext i
  fin_cases i <;> simp

/-- The shock endpoint is jointly `C¹` in strain increment and left state
under the strict-hyperbolicity assumption `p' > 0`. -/
theorem contDiff_shockState_strength {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ shockState stress k p.2 (p.2 0 + p.1)) := by
  have hstrain : ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ p.2 0) := by
    fun_prop
  have hvelocity : ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ p.2 1) := by
    fun_prop
  have hspeed : ContDiff ℝ 1 (fun p : ℝ × ℝ^2 ↦ shockSpeed stress k (p.2 0) (p.2 0 + p.1)) :=
    (contDiff_shockSpeed_strength hstress hpositive k).comp (contDiff_fst.prodMk hstrain)
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · simpa [shockState] using hstrain.add contDiff_fst
  · simpa [shockState] using hvelocity.sub (hspeed.mul contDiff_fst)

private theorem hasDerivAt_const_sub_mul_sub {g : ℝ → ℝ} {a c : ℝ} (hg : ContinuousAt g a) :
    HasDerivAt (fun x ↦ c - g x * (x - a)) (-g a) a := by
  rw [hasDerivAt_iff_tendsto_slope]
  apply (tendsto_nhdsWithin_of_tendsto_nhds hg.neg).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hsub : x - a ≠ 0 := sub_ne_zero.mpr hx
  simp only [Pi.neg_apply, slope, sub_self, mul_zero, sub_zero,
    vsub_eq_sub, sub_sub_cancel_left, smul_eq_mul, mul_neg, neg_inj]
  rw [mul_comm (g x) (x - a), ← mul_assoc, inv_mul_cancel₀ hsub, one_mul]

/-- At zero jump, the Hugoniot branch is tangent to the selected right
eigenvector. Only continuity of the extended shock speed is needed because
its variation is multiplied by the vanishing strain jump. -/
theorem hasDerivAt_shockState_left_strain {stress : ℝ → ℝ} (left : ℝ^2)
    (hstress : DifferentiableAt ℝ stress (left 0)) (k : Fin 2) :
    HasDerivAt (fun vR ↦ shockState stress k left vR)
      (rightEigenvector (soundSpeed stress (left 0)) k) (left 0) := by
  have hstrain : HasDerivAt (fun vR : ℝ ↦ vR) 1 (left 0) := hasDerivAt_id (left 0)
  have hvelocity : HasDerivAt (fun vR ↦ left 1 - shockSpeed stress k (left 0) vR * (vR - left 0))
        (-shockSpeed stress k (left 0) (left 0)) (left 0) :=
    hasDerivAt_const_sub_mul_sub (continuousAt_shockSpeed_right hstress k)
  let coordinates := EuclideanSpace.equiv (Fin 2) ℝ
  have hcoordinates : HasDerivAt (fun vR : ℝ ↦ ![vR, left 1 - shockSpeed stress k (left 0) vR *
              (vR - left 0)]) ![1, -shockSpeed stress k (left 0) (left 0)]
        (left 0) := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hstrain
    · simpa using hvelocity
  have hstate := coordinates.symm.hasFDerivAt.comp_hasDerivAt (left 0) hcoordinates
  fin_cases k <;> simpa [coordinates, shockState, rightEigenvector, soundSpeed,
      Function.comp_def, characteristicSpeed] using hstate

/-- Parameterized by strain increment, the Hugoniot branch has the selected
right eigenvector as its derivative at zero strength. -/
theorem hasDerivAt_shockState_strength_zero {stress : ℝ → ℝ} (left : ℝ^2)
    (hstress : DifferentiableAt ℝ stress (left 0)) (k : Fin 2) :
    HasDerivAt (fun strength ↦ shockState stress k left (left 0 + strength))
      (rightEigenvector (soundSpeed stress (left 0)) k) 0 := by
  have hargument : ContinuousAt (fun strength : ℝ ↦ left 0 + strength) 0 :=
    continuousAt_const.add continuousAt_id
  have hspeedAt : ContinuousAt (shockSpeed stress k (left 0)) (left 0 + 0) := by
    simpa using continuousAt_shockSpeed_right hstress k
  have hspeed : ContinuousAt (fun strength ↦
          shockSpeed stress k (left 0) (left 0 + strength)) 0 := by
    change ContinuousAt (shockSpeed stress k (left 0) ∘ fun strength : ℝ ↦ left 0 + strength) 0
    exact hspeedAt.comp hargument
  have hstrain : HasDerivAt (fun strength : ℝ ↦ left 0 + strength) 1 0 := by
    cas
  have hvelocity : HasDerivAt (fun strength ↦ left 1 -
            shockSpeed stress k (left 0) (left 0 + strength) * (strength - 0))
        (-shockSpeed stress k (left 0) (left 0 + 0)) 0 := hasDerivAt_const_sub_mul_sub hspeed
  let coordinates := EuclideanSpace.equiv (Fin 2) ℝ
  have hcoordinates : HasDerivAt (fun strength : ℝ ↦ ![left 0 + strength, left 1 -
              shockSpeed stress k (left 0) (left 0 + strength) * strength])
        ![1, -shockSpeed stress k (left 0) (left 0)] 0 := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa using hstrain
    · simpa using hvelocity
  have hstate := coordinates.symm.hasFDerivAt.comp_hasDerivAt 0 hcoordinates
  fin_cases k <;> simpa [coordinates, shockState, rightEigenvector, soundSpeed,
      Function.comp_def, characteristicSpeed] using hstate

/-- At zero strength, the joint strength-state derivative of a Hugoniot step
has the right eigenvector as its strength column and the identity as its state
block. -/
theorem hasFDerivAt_shockState_strength_zero {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v) (k : Fin 2) (left : ℝ^2) :
    HasFDerivAt (fun p : ℝ × ℝ^2 ↦ shockState stress k p.2 (p.2 0 + p.1))
      (waveStepDerivative (rightEigenvector (soundSpeed stress (left 0)) k)) (0, left) :=
  hasFDerivAt_waveStep_zero (fun strength state ↦ shockState stress k state (state 0 + strength))
      left (rightEigenvector (soundSpeed stress (left 0)) k)
      (fun state ↦ by simp)
      ((contDiff_shockState_strength hstress hpositive k).differentiable one_ne_zero (0, left))
      (hasDerivAt_shockState_strength_zero left (hstress.differentiable (by norm_num) (left 0)) k)

/-- Squaring either signed shock speed recovers the differentiable stress
slope. -/
theorem shockSpeed_sq_eq_dslope {stress : ℝ → ℝ} {vL vR : ℝ} (k : Fin 2)
    (hslope : 0 ≤ dslope stress vL vR) :
    shockSpeed stress k vL vR ^ 2 = dslope stress vL vR := by
  fin_cases k <;> simp [shockSpeed, characteristicSpeed, Real.sq_sqrt hslope]

/-- The explicit shock endpoint satisfies the vector Rankine–Hugoniot
condition whenever the stress difference quotient `dslope` is nonnegative. -/
theorem rankineHugoniot_shockState {stress : ℝ → ℝ} (k : Fin 2) (left : ℝ^2) (vR : ℝ)
    (hslope : 0 ≤ dslope stress (left 0) vR) :
    RankineHugoniot (flux stress) left (shockState stress k left vR)
      (shockSpeed stress k (left 0) vR) := by
  have hsecant := sub_smul_dslope stress (left 0) vR
  have hspeed := shockSpeed_sq_eq_dslope k hslope
  rw [RankineHugoniot]
  ext i
  fin_cases i
  · change -(left 1 - shockSpeed stress k (left 0) vR * (vR - left 0)) - -left 1 =
        shockSpeed stress k (left 0) vR * (vR - left 0)
    ring
  · change (vR - left 0) * dslope stress (left 0) vR = stress vR - stress (left 0) at hsecant
    change -stress vR - -stress (left 0) = shockSpeed stress k (left 0) vR * ((left 1 -
              shockSpeed stress k (left 0) vR * (vR - left 0)) - left 1)
    calc
      -stress vR - -stress (left 0) = -(stress vR - stress (left 0)) := by ring
      _ = -((vR - left 0) * dslope stress (left 0) vR) := by
        rw [hsecant]
      _ = -(shockSpeed stress k (left 0) vR ^ 2 * (vR - left 0)) := by
        rw [hspeed]
        ring
      _ = shockSpeed stress k (left 0) vR * ((left 1 -
              shockSpeed stress k (left 0) vR * (vR - left 0)) -
            left 1) := by
        ring

/-- The explicit p-system Hugoniot jump gives a global distributional
solution with a planar interface. -/
theorem isWeakSolution_planarShock_shockState {stress : ℝ → ℝ} (k : Fin 2) (left : ℝ^2) (vR : ℝ)
    (hslope : 0 ≤ dslope stress (left 0) vR) :
    IsWeakSolution (flux stress) ⊤
      (planarShock left (shockState stress k left vR) (shockSpeed stress k (left 0) vR)) :=
  (rankineHugoniot_shockState k left vR hslope).isWeakSolution_planarShock

private theorem strictConvexOn_stress {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) :
    StrictConvexOn ℝ Set.univ stress := by
  apply strictConvexOn_univ_of_deriv2_pos hstress.continuous
  simpa [Function.iterate_succ_apply] using hsecond

/-! ## Mechanical entropy dissipation -/

/-- Mechanical entropy production across an explicit p-system shock,
reduced to the error in the endpoint trapezoid rule for the stress. -/
theorem mechanicalEntropyProduction_shockState {stress potential : ℝ → ℝ} (k : Fin 2) (left : ℝ^2)
    (vR : ℝ) (hslope : 0 ≤ dslope stress (left 0) vR) :
    mechanicalEntropyFlux stress (shockState stress k left vR) -
          mechanicalEntropyFlux stress left -
        shockSpeed stress k (left 0) vR *
          (mechanicalEntropy potential (shockState stress k left vR) -
            mechanicalEntropy potential left) =
      shockSpeed stress k (left 0) vR *
        ((vR - left 0) * (stress (left 0) + stress vR) / 2 -
          (potential vR - potential (left 0))) := by
  have hsecant := sub_smul_dslope stress (left 0) vR
  have hspeed := shockSpeed_sq_eq_dslope k hslope
  simp only [mechanicalEntropyFlux, mechanicalEntropy, shockState_apply_zero, shockState_apply_one]
  rw [← hspeed] at hsecant
  simp only [smul_eq_mul] at hsecant
  linear_combination (left 1 - shockSpeed stress k (left 0) vR * (vR - left 0) / 2) * hsecant

private theorem intervalIntegral_stress_eq_potential_sub {stress potential : ℝ → ℝ}
    (hpotential : ContDiff ℝ 1 potential) (hderiv : ∀ x, deriv potential x = stress x) (a b : ℝ) :
    (∫ x in a..b, stress x) = potential b - potential a := by
  have hftc := intervalIntegral.integral_deriv_eq_sub (f := potential) (a := a) (b := b)
      (fun x _ ↦ hpotential.differentiable one_ne_zero x)
      (hpotential.continuous_deriv_one.intervalIntegrable a b)
  rwa [show deriv potential = stress by funext x; exact hderiv x] at hftc

/-- An increasing-strain family-zero shock strictly dissipates mechanical
entropy. -/
theorem mechanicalEntropyProduction_shockState_zero_lt_zero {stress potential : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (left : ℝ^2) {vR : ℝ} (hstrain : left 0 < vR) :
    mechanicalEntropyFlux stress (shockState stress 0 left vR) -
          mechanicalEntropyFlux stress left -
        shockSpeed stress 0 (left 0) vR *
          (mechanicalEntropy potential (shockState stress 0 left vR) -
            mechanicalEntropy potential left) < 0 := by
  have hconvex := strictConvexOn_stress hstress hsecond
  have htrapezoid := intervalIntegral_lt_trapezoid_of_strictConvexOn hconvex hstrain
  rw [intervalIntegral_stress_eq_potential_sub hpotential hderiv] at htrapezoid
  have hbracket : 0 < (vR - left 0) * (stress (left 0) + stress vR) / 2 -
          (potential vR - potential (left 0)) := by
    linarith
  have hdslope : 0 < dslope stress (left 0) vR := dslope_pos_of_deriv_pos hpositive _ _
  have hspeed : shockSpeed stress 0 (left 0) vR < 0 := by
    rw [shockSpeed_zero]
    exact neg_neg_of_pos (Real.sqrt_pos.2 hdslope)
  rw [mechanicalEntropyProduction_shockState (k := 0) left vR hdslope.le]
  exact mul_neg_of_neg_of_pos hspeed hbracket

/-- A decreasing-strain family-one shock strictly dissipates mechanical
entropy. -/
theorem mechanicalEntropyProduction_shockState_one_lt_zero {stress potential : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress) (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x) (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v) (left : ℝ^2) {vR : ℝ} (hstrain : vR < left 0) :
    mechanicalEntropyFlux stress (shockState stress 1 left vR) -
          mechanicalEntropyFlux stress left -
        shockSpeed stress 1 (left 0) vR *
          (mechanicalEntropy potential (shockState stress 1 left vR) -
            mechanicalEntropy potential left) < 0 := by
  have hconvex := strictConvexOn_stress hstress hsecond
  have htrapezoid := intervalIntegral_lt_trapezoid_of_strictConvexOn hconvex hstrain
  rw [intervalIntegral_stress_eq_potential_sub hpotential hderiv] at htrapezoid
  have hbracket : (vR - left 0) * (stress (left 0) + stress vR) / 2 -
          (potential vR - potential (left 0)) < 0 := by
    linarith
  have hdslope : 0 < dslope stress (left 0) vR := dslope_pos_of_deriv_pos hpositive _ _
  have hspeed : 0 < shockSpeed stress 1 (left 0) vR := by
    rw [shockSpeed_one]
    exact Real.sqrt_pos.2 hdslope
  rw [mechanicalEntropyProduction_shockState (k := 1) left vR hdslope.le]
  exact mul_neg_of_pos_of_neg hspeed hbracket

/-- An increasing-strain family-zero shock is entropy-admissible for the
mechanical entropy pair. -/
theorem mechanicalEntropyPair_isAdmissibleShock_zero
    {stress potential : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) {vR : ℝ} (hstrain : left 0 < vR) :
    (mechanicalEntropyPair stress potential
      (hstress.of_le (by norm_num)) hpotential hderiv).IsAdmissibleShock
        left (shockState stress 0 left vR)
        (shockSpeed stress 0 (left 0) vR) := by
  have hdslope : 0 < dslope stress (left 0) vR := dslope_pos_of_deriv_pos hpositive _ _
  constructor
  · exact rankineHugoniot_shockState 0 left vR hdslope.le
  · change mechanicalEntropyFlux stress (shockState stress 0 left vR) -
          mechanicalEntropyFlux stress left ≤ shockSpeed stress 0 (left 0) vR *
          (mechanicalEntropy potential (shockState stress 0 left vR) -
            mechanicalEntropy potential left)
    linarith [mechanicalEntropyProduction_shockState_zero_lt_zero
      hstress hpotential hderiv hpositive hsecond left hstrain]

/-- A decreasing-strain family-one shock is entropy-admissible for the
mechanical entropy pair. -/
theorem mechanicalEntropyPair_isAdmissibleShock_one
    {stress potential : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) {vR : ℝ} (hstrain : vR < left 0) :
    (mechanicalEntropyPair stress potential
      (hstress.of_le (by norm_num)) hpotential hderiv).IsAdmissibleShock
        left (shockState stress 1 left vR)
        (shockSpeed stress 1 (left 0) vR) := by
  have hdslope : 0 < dslope stress (left 0) vR := dslope_pos_of_deriv_pos hpositive _ _
  constructor
  · exact rankineHugoniot_shockState 1 left vR hdslope.le
  · change mechanicalEntropyFlux stress (shockState stress 1 left vR) -
          mechanicalEntropyFlux stress left ≤ shockSpeed stress 1 (left 0) vR *
          (mechanicalEntropy potential (shockState stress 1 left vR) -
            mechanicalEntropy potential left)
    linarith [mechanicalEntropyProduction_shockState_one_lt_zero
      hstress hpotential hderiv hpositive hsecond left hstrain]

/-- The planar family-zero p-system shock satisfies the distributional
mechanical-entropy inequality. -/
theorem satisfiesEntropyInequalityFor_planarShock_shockState_zero_of_left_lt_right
    {stress potential : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) {vR : ℝ} (hstrain : left 0 < vR) :
    SatisfiesEntropyInequalityFor ⊤
      (planarShock left (shockState stress 0 left vR)
        (shockSpeed stress 0 (left 0) vR))
      (mechanicalEntropyPair stress potential
        (hstress.of_le (by norm_num)) hpotential hderiv) :=
  satisfiesEntropyInequalityFor_planarShock_iff.mpr
    (mechanicalEntropyPair_isAdmissibleShock_zero
      hstress hpotential hderiv hpositive hsecond left hstrain).2

/-- The planar family-one p-system shock satisfies the distributional
mechanical-entropy inequality. -/
theorem satisfiesEntropyInequalityFor_planarShock_shockState_one_of_right_lt_left
    {stress potential : ℝ → ℝ}
    (hstress : ContDiff ℝ 2 stress)
    (hpotential : ContDiff ℝ 1 potential)
    (hderiv : ∀ x, deriv potential x = stress x)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) {vR : ℝ} (hstrain : vR < left 0) :
    SatisfiesEntropyInequalityFor ⊤
      (planarShock left (shockState stress 1 left vR)
        (shockSpeed stress 1 (left 0) vR))
      (mechanicalEntropyPair stress potential
        (hstress.of_le (by norm_num)) hpotential hderiv) :=
  satisfiesEntropyInequalityFor_planarShock_iff.mpr
    (mechanicalEntropyPair_isAdmissibleShock_one
      hstress hpotential hderiv hpositive hsecond left hstrain).2

/-- If `p' > 0` and `p'' > 0`, increasing the strain produces a family-zero
Lax shock on the negative-speed Hugoniot branch. -/
theorem laxShock_shockState_zero_of_left_lt_right
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) {vR : ℝ} (hstrain : left 0 < vR) :
    LaxShock
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) 0
      left (shockState stress 0 left vR)
      (shockSpeed stress 0 (left 0) vR) := by
  have hconvex := strictConvexOn_stress hstress hsecond
  have hleft : deriv stress (left 0) < slope stress (left 0) vR :=
    hconvex.deriv_lt_slope (Set.mem_univ _) (Set.mem_univ _) hstrain
      (hstress.differentiable (by norm_num) (left 0))
  have hright : slope stress (left 0) vR < deriv stress vR :=
    hconvex.slope_lt_deriv (Set.mem_univ _) (Set.mem_univ _) hstrain
      (hstress.differentiable (by norm_num) vR)
  have hslope : 0 ≤ slope stress (left 0) vR := ((hpositive (left 0)).trans hleft).le
  have hdslope : dslope stress (left 0) vR = slope stress (left 0) vR :=
    dslope_of_ne stress (ne_of_gt hstrain)
  have hsqrtLeft : √(deriv stress (left 0)) < √(slope stress (left 0) vR) :=
    Real.sqrt_lt_sqrt (hpositive (left 0)).le hleft
  have hsqrtRight : √(slope stress (left 0) vR) < √(deriv stress vR) :=
    Real.sqrt_lt_sqrt hslope hright
  refine ⟨rankineHugoniot_shockState 0 left vR (hdslope ▸ hslope), ?_, ?_, ?_, ?_⟩
  · change -√(deriv stress vR) < shockSpeed stress 0 (left 0) vR
    rw [shockSpeed_zero, hdslope]
    exact neg_lt_neg hsqrtRight
  · change shockSpeed stress 0 (left 0) vR < -√(deriv stress (left 0))
    rw [shockSpeed_zero, hdslope]
    exact neg_lt_neg hsqrtLeft
  · exact fun j hj ↦ False.elim (by omega)
  · intro j hj
    have hj1 : j = 1 := by omega
    subst j
    change shockSpeed stress 0 (left 0) vR < √(deriv stress vR)
    rw [shockSpeed_zero, hdslope]
    nlinarith [Real.sqrt_nonneg (deriv stress vR), Real.sqrt_pos.2 (hpositive (left 0))]

/-- If `p' > 0` and `p'' > 0`, decreasing the strain produces a family-one
Lax shock on the positive-speed Hugoniot branch. -/
theorem laxShock_shockState_one_of_right_lt_left
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) {vR : ℝ} (hstrain : vR < left 0) :
    LaxShock
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) 1
      left (shockState stress 1 left vR)
      (shockSpeed stress 1 (left 0) vR) := by
  have hconvex := strictConvexOn_stress hstress hsecond
  have hright : deriv stress vR < slope stress (left 0) vR := by
    rw [slope_comm stress (left 0) vR]
    exact hconvex.deriv_lt_slope (Set.mem_univ _) (Set.mem_univ _) hstrain
      (hstress.differentiable (by norm_num) vR)
  have hleft : slope stress (left 0) vR < deriv stress (left 0) := by
    rw [slope_comm stress (left 0) vR]
    exact hconvex.slope_lt_deriv (Set.mem_univ _) (Set.mem_univ _) hstrain
      (hstress.differentiable (by norm_num) (left 0))
  have hslope : 0 ≤ slope stress (left 0) vR := ((hpositive vR).trans hright).le
  have hdslope : dslope stress (left 0) vR = slope stress (left 0) vR :=
    dslope_of_ne stress (ne_of_lt hstrain)
  have hsqrtRight : √(deriv stress vR) < √(slope stress (left 0) vR) :=
    Real.sqrt_lt_sqrt (hpositive vR).le hright
  have hsqrtLeft : √(slope stress (left 0) vR) < √(deriv stress (left 0)) :=
    Real.sqrt_lt_sqrt hslope hleft
  refine ⟨rankineHugoniot_shockState 1 left vR (hdslope ▸ hslope), ?_, ?_, ?_, ?_⟩
  · change √(deriv stress vR) < shockSpeed stress 1 (left 0) vR
    rw [shockSpeed_one, hdslope]
    exact hsqrtRight
  · change shockSpeed stress 1 (left 0) vR < √(deriv stress (left 0))
    rw [shockSpeed_one, hdslope]
    exact hsqrtLeft
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    change -√(deriv stress (left 0)) < shockSpeed stress 1 (left 0) vR
    rw [shockSpeed_one, hdslope]
    nlinarith [Real.sqrt_nonneg (deriv stress (left 0)), Real.sqrt_pos.2 (hpositive vR)]
  · exact fun j hj ↦ False.elim (by omega)

/-- An increasing-strain family-zero p-system shock is an admissible
elementary connection. -/
theorem isElementaryConnection_shockState_zero_of_left_lt_right
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) {vR : ℝ} (hstrain : left 0 < vR) :
    IsElementaryConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) 0
      left (shockState stress 0 left vR) :=
  IsElementaryConnection.shock (shockSpeed stress 0 (left 0) vR)
    (laxShock_shockState_zero_of_left_lt_right hstress hpositive hsecond left hstrain)

/-- A decreasing-strain family-one p-system shock is an admissible elementary
connection. -/
theorem isElementaryConnection_shockState_one_of_right_lt_left
    {stress : ℝ → ℝ} (hstress : ContDiff ℝ 2 stress)
    (hpositive : ∀ v, 0 < deriv stress v)
    (hsecond : ∀ v, 0 < deriv (deriv stress) v)
    (left : ℝ^2) {vR : ℝ} (hstrain : vR < left 0) :
    IsElementaryConnection
      (characteristicField stress
        (hstress.differentiable (by norm_num)) hpositive) 1
      left (shockState stress 1 left vR) :=
  IsElementaryConnection.shock (shockSpeed stress 1 (left 0) vR)
    (laxShock_shockState_one_of_right_lt_left hstress hpositive hsecond left hstrain)

end PDE.Hyperbolic.ConservationLaw.System.PSystem
