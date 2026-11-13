/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.OddDimensions.AnalyticBridge
public import PDE.Hyperbolic.Models.Wave.EulerPoissonDarboux

/-!
# The wave representation in odd space dimensions

Write the space dimension as `2 * m + 3`. The reduction (28) of Evans, §2.4.1(d), applies
`(r⁻¹ d/dr)^m` to `r^(2m+1)` times a spherical mean. The resulting profile
satisfies the one-dimensional wave equation away from `r = 0` (his Lemma 3), once radial and
time differentiation are known to commute.

We define the profile and the positive-time candidate representation, and
prove the radial reduction and the center-trace identity under explicit finite
radial regularity. The last theorem identifies the
transformed profile with the one-dimensional d'Alembert solution by classical
uniqueness. It assumes global joint `C³` regularity of the specified
totalized intermediate radial transforms on the whole time-radius plane,
including radius zero; the reduced wave equation and representation formula
are then conclusions.

For `m = 0` the dimension is three, the radial transform is the identity, and
the formula reduces to the usual spherical-mean form of Kirchhoff's formula.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(d), equations (28)-(31), Lemmas 2 and 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SatisfiesPDEProblem coordinateLine)

noncomputable section

namespace WaveEquation

open PDE.Analysis PDE.Common Set

/-- The radial profile used in Evans's odd-dimensional reduction.

For `m > 0`, this is a total function containing divisions by the radius.
Analytic identities involving those divisions are proved at nonzero radius.
Center identities require explicit regularity of the total radial functions. -/
noncomputable def oddSphericalProfile
    (m : ℕ)
    (f : ℝ^(2 * m + 3) → ℝ)
    (x : ℝ^(2 * m + 3)) :
    ℝ → ℝ :=
  oddRadialTransform m
    (fun r ↦
      r ^ (2 * m + 1) *
        unitSphereAverage (2 * m + 3) f x r)

/-- In three dimensions, Evans's radial profile is simply radius times the
spherical mean. -/
@[simp]
theorem oddSphericalProfile_zero (f : ℝ^3 → ℝ) (x : ℝ^3) :
    oddSphericalProfile 0 f x = fun r ↦ r * unitSphereAverage 3 f x r := by
  simp [oddSphericalProfile]

/-- Evans's transformed spherical profile is odd in the signed radius. -/
theorem oddSphericalProfile_odd (m : ℕ) (f : ℝ^(2 * m + 3) → ℝ) (x : ℝ^(2 * m + 3)) :
    Function.Odd (oddSphericalProfile m f x) := by
  apply oddRadialTransform_odd
  intro r
  change (-r) ^ (2 * m + 1) * unitSphereAverage (2 * m + 3) f x (-r) = -(r ^ (2 * m + 1) *
        unitSphereAverage (2 * m + 3) f x r)
  rw [unitSphereAverage_neg_radius]
  rw [(odd_two_mul_add_one m).neg_pow]
  ring

/-- The center derivative of Evans's transformed spherical profile.

The factor `(2m+1)‼` is exactly the normalization appearing in the
odd-dimensional representation formula. -/
theorem deriv_oddSphericalProfile_zero (m : ℕ) (f : ℝ^(2 * m + 3) → ℝ) (x : ℝ^(2 * m + 3))
    (hmean : ContDiff ℝ (m + 1 : ℕ) (unitSphereAverage (2 * m + 3) f x)) :
    deriv (oddSphericalProfile m f x) 0 = (Nat.doubleFactorial (2 * m + 1) : ℝ) * f x := by
  rw [oddSphericalProfile]
  rw [deriv_oddRadialTransform_pow_mul_zero m hmean]
  have hzero : unitSphereAverage (2 * m + 3) f x 0 = f x :=
    @unitSphereAverage_zero (2 * m + 3) ⟨by omega⟩ f x
  rw [hzero]

/-- Evans's candidate representation in space dimension `2 * m + 3`.

The time variable is a member of `Ioi 0`, so this declaration never evaluates
the singular radial operator at the origin.  Establishing the Cauchy trace at
`t = 0` is a separate analytic theorem. -/
noncomputable def evansOddDimensionalFormula
    (m : ℕ)
    (g h : ℝ^(2 * m + 3) → ℝ)
    (x : ℝ^(2 * m + 3))
    (t : Ioi (0 : ℝ)) :
    ℝ :=
  (deriv (oddSphericalProfile m g x) (t : ℝ) +
      oddSphericalProfile m h x (t : ℝ)) /
    (Nat.doubleFactorial (2 * m + 1) : ℝ)

/-- The case `m = 0` is the standard three-dimensional spherical-mean
representation. -/
@[simp]
theorem evansOddDimensionalFormula_zero (g h : ℝ^3 → ℝ) (x : ℝ^3) (t : Ioi (0 : ℝ)) :
    evansOddDimensionalFormula 0 g h x t = deriv (fun r ↦ r * unitSphereAverage 3 g x r) (t : ℝ) +
      (t : ℝ) * unitSphereAverage 3 h x (t : ℝ) := by
  simp [evansOddDimensionalFormula]

/-- The spatial derivative at the center of d'Alembert's formula for odd
initial data.

Oddness turns the two endpoint contributions into the sum of the displacement
derivative and velocity evaluated at time `t`. -/
theorem deriv_dAlembertFormula_zero_of_odd {g h : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h)
    (hgodd : Function.Odd g) (hhodd : Function.Odd h) (t : ℝ) :
    deriv (fun r ↦ dAlembertFormula g h r t) 0 = deriv g t + h t := by
  let U := fun q : ℝ^2 ↦ dAlembertFormula g h (q 1) (q 0)
  let w : ℝ^1 → ℝ := fun y ↦ U (timeSpaceCons t y)
  have hU : ContDiff ℝ 2 U := contDiff_two_dAlembertFormula g h hg hh
  have hgderiv : deriv g (-t) = deriv g t := by
    have hderiv := congrFun (congrArg deriv (funext hgodd : (fun r ↦ g (-r)) = -g)) t
    rw [deriv_comp_neg, deriv.neg] at hderiv
    exact neg_inj.mp hderiv
  have hline : (fun r ↦ dAlembertFormula g h r t) = w ∘ coordinateLine (0 : Fin 1) 0 := by
    funext r
    simp only [Function.comp_apply, w, U, dAlembertFormula]
    rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, timeSpaceCons_succ, timeSpaceCons_zero,
      PDE.coordinateLine_apply_same]
  have hspaceZero : timeSpaceCons t (0 : ℝ^1) (1 : Fin 2) = 0 := by
    rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, timeSpaceCons_succ]
    exact PiLp.zero_apply (fun _ : Fin 1 ↦ ℝ) (0 : Fin 1)
  have hw : DifferentiableAt ℝ w 0 := (hU.differentiable (by norm_num)).differentiableAt.comp 0
    (PDE.Common.hasFDerivAt_timeSpaceCons_spatial 1 t 0).differentiableAt
  have hcoordinate : (∂[(0 : Fin 1)] w) 0 = deriv (w ∘ coordinateLine (0 : Fin 1) 0) 0 := by
    simpa using PDE.partialDeriv_eq_deriv_coordinateLine (i := (0 : Fin 1)) (x := (0 : ℝ^1)) hw
  calc deriv (fun r ↦ dAlembertFormula g h r t) 0 = (∂[(0 : Fin 1)] w) 0 := by
        rw [hline, ← hcoordinate]
    _ = (∂[(1 : Fin 2)] U) (timeSpaceCons t (0 : ℝ^1)) :=
      PDE.partialDeriv_timeSpaceCons_spatial (0 : Fin 1) U t 0
        (hU.differentiable (by norm_num)).differentiableAt
    _ = (1 / 2 : ℝ) * (deriv g t + deriv g (-t)) + (1 / 2 : ℝ) * (h t - h (-t)) := by
      simpa only [hspaceZero, timeSpaceCons_zero, zero_add, zero_sub] using
        partialDeriv_dAlembert_space g h hg hh (timeSpaceCons t (0 : ℝ^1))
    _ = deriv g t + h t := by
      rw [hgderiv, hhodd t]
      ring

/-- Evans's odd-dimensional formula follows from the transformed
one-dimensional d'Alembert representation.

The hypotheses are two analytic inputs about spherical means: enough
radial regularity for the center trace,
and identification of the transformed wave profile with its d'Alembert
solution. -/
theorem eq_evansOddDimensionalFormula_of_transformed_dAlembert (m : ℕ) {g h : ℝ^(2 * m + 3) → ℝ}
    {u : ℝ^((2 * m + 3) + 1) → ℝ} (x : ℝ^(2 * m + 3)) (t : Ioi (0 : ℝ))
    (hmean : ContDiff ℝ (m + 1 : ℕ) (waveSphericalMean u x (t : ℝ)))
    (hg : ContDiff ℝ 2 (oddSphericalProfile m g x)) (hh : ContDiff ℝ 1 (oddSphericalProfile m h x))
    (hrepresentation : oddSphericalProfile m (fun y ↦ u (timeSpaceCons (t : ℝ) y)) x = fun r ↦
      dAlembertFormula (oddSphericalProfile m g x) (oddSphericalProfile m h x) r (t : ℝ)) :
    u (timeSpaceCons (t : ℝ) x) = evansOddDimensionalFormula m g h x t := by
  have hscaled : (Nat.doubleFactorial (2 * m + 1) : ℝ) * u (timeSpaceCons (t : ℝ) x) =
      deriv (oddSphericalProfile m g x) (t : ℝ) + oddSphericalProfile m h x (t : ℝ) := by
    rw [← deriv_oddSphericalProfile_zero m (fun y ↦ u (timeSpaceCons (t : ℝ) y)) x hmean,
      hrepresentation]
    exact deriv_dAlembertFormula_zero_of_odd hg hh (oddSphericalProfile_odd m g x)
      (oddSphericalProfile_odd m h x) (t : ℝ)
  rw [evansOddDimensionalFormula, eq_div_iff (by positivity)]
  simpa only [mul_comm] using hscaled

/-- The radial part of Evans's odd-dimensional reduction.

For a classical solution of the assigned-Cauchy-data problem, the
second radial derivative of the transformed spherical mean is the same radial
transform applied to the averaged second time derivative. The
`hmean` hypothesis supplies the finite radial regularity of the spherical mean. -/
theorem secondDeriv_oddSphericalProfile_of_wave (m : ℕ) {g h : ℝ^(2 * m + 3) → ℝ}
    {u : ℝ^((2 * m + 3) + 1) → ℝ} (x : ℝ^(2 * m + 3)) {t : ℝ} (ht : 0 < t) (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 2 * m + 3) g h) u)
    (hmean : ContDiff ℝ (m + 2) (waveSphericalMean u x t)) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (oddSphericalProfile m (fun y ↦ u (timeSpaceCons t y)) x)) r = oddRadialTransform m
      (fun s ↦ s ^ (2 * m + 1) * deriv (deriv (fun q ↦ waveSphericalMean u x q s)) t) r := by
  have hdim : Fact (0 < 2 * m + 3) := ⟨by omega⟩
  have hcoeff : (((2 * m + 3 : ℕ) : ℝ) - 1) = ((2 * m + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  have hEPD : ∀ s, 0 < s → deriv (deriv (waveSphericalMean u x t)) s +
      (((2 * m + 2 : ℕ) : ℝ) / s) * deriv (waveSphericalMean u x t) s =
        deriv (deriv (fun q ↦ waveSphericalMean u x q s)) t := fun s hs ↦ by
    simpa only [hcoeff] using (@waveSphericalMean_eulerPoissonDarboux_of_timeSlice
      (2 * m + 3) hdim u x t s hs hu fun y ↦
        forcedWaveResidualAssignedCauchyDataProblem.residual_eq hsol
          (by simpa only [timeSpaceCons_zero] using ht)).symm
  simpa only [oddSphericalProfile, waveSphericalMean] using
    oddRadialTransform_eulerPoissonDarboux m hmean hEPD hr

private def sphericalWaveWeight (m : ℕ) (u : ℝ^((2 * m + 3) + 1) → ℝ)
    (x : ℝ^(2 * m + 3)) (t r : ℝ) : ℝ :=
  r ^ (2 * m + 1) * waveSphericalMean u x t r

private def transformedSphericalWave (m : ℕ) (u : ℝ^((2 * m + 3) + 1) → ℝ)
    (x : ℝ^(2 * m + 3)) (p : ℝ^2) : ℝ :=
  oddRadialTransform m (sphericalWaveWeight m u x (p 0)) (p 1)

private theorem odd_sphericalWaveWeight (m : ℕ) (u : ℝ^((2 * m + 3) + 1) → ℝ)
    (x : ℝ^(2 * m + 3)) (t : ℝ) : Function.Odd (sphericalWaveWeight m u x t) := by
  intro r
  change (-r) ^ (2 * m + 1) * waveSphericalMean u x t (-r) =
    -(r ^ (2 * m + 1) * waveSphericalMean u x t r)
  rw [waveSphericalMean_neg_radius, (odd_two_mul_add_one m).neg_pow]
  ring

/-- The transformed displacement is the radial transform of the initial displacement. -/
private theorem transformedSphericalWave_initial_position (m : ℕ) {g h : ℝ^(2 * m + 3) → ℝ}
    {u : ℝ^((2 * m + 3) + 1) → ℝ} (x : ℝ^(2 * m + 3))
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem g h) u) (y : ℝ^1) :
    transformedSphericalWave m u x (timeSpaceCons 0 y) = oddSphericalProfile m g x (y 0) := by
  have hposition : (fun z ↦ u (timeSpaceCons 0 z)) = g := by
    funext z
    simpa using forcedWaveResidualAssignedCauchyDataProblem.initial_position_eq
      hsol (x := timeSpaceCons 0 z) (by simp)
  change oddSphericalProfile m (fun z ↦ u (timeSpaceCons 0 z)) x (y 0) = _
  rw [hposition]

/-- Time differentiation commutes with the radial transform and carries the original
velocity trace to the transformed velocity trace. -/
private theorem transformedSphericalWave_initial_velocity (m : ℕ) {g h : ℝ^(2 * m + 3) → ℝ}
    {u : ℝ^((2 * m + 3) + 1) → ℝ} (x : ℝ^(2 * m + 3)) (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem g h) u)
    (hregular : ∀ k ≤ m,
      ContDiff ℝ 2 (fun p : ℝ^2 ↦ oddRadialTransform k (sphericalWaveWeight m u x (p 0)) (p 1)))
    (y : ℝ^1) :
    (∂[0] (transformedSphericalWave m u x)) (timeSpaceCons 0 y) =
      oddSphericalProfile m h x (y 0) := by
  have hW : ContDiff ℝ 2 (transformedSphericalWave m u x) := hregular m le_rfl
  have hvelocity : (fun z ↦ (∂[0] u) (timeSpaceCons 0 z)) = h := by
    funext z
    simpa using forcedWaveResidualAssignedCauchyDataProblem.initial_velocity_eq
      hsol (x := timeSpaceCons 0 z) (by simp)
  have htrace : (fun q ↦ transformedSphericalWave m u x (timeSpaceCons q y)) =
        fun q ↦ oddRadialTransform m (sphericalWaveWeight m u x q) (y 0) := by
    funext q
    simp only [transformedSphericalWave, timeSpaceCons_zero]
    rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, timeSpaceCons_succ]
  have hweightVelocity : (fun r ↦ deriv (fun q ↦ sphericalWaveWeight m u x q r) 0) =
        fun r ↦ r ^ (2 * m + 1) * unitSphereAverage (2 * m + 3) h x r := by
    funext r
    change deriv (fun q ↦ r ^ (2 * m + 1) * waveSphericalMean u x q r) 0 = _
    rw [deriv_const_mul_field,
      (hasDerivAt_waveSphericalMean_time u x 0 r (hu.of_le (by norm_num))).deriv, hvelocity]
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ y 0
    (hW.differentiable (by norm_num)).differentiableAt, htrace,
    deriv_oddRadialTransform_time m _ hregular, hweightVelocity]
  rfl

/-- The positive-radius EPD reduction, together with commutation of two time derivatives,
gives the one-dimensional wave equation for the transformed spherical mean. -/
private theorem transformedSphericalWave_secondDeriv_eq_of_pos (m : ℕ) {g h : ℝ^(2 * m + 3) → ℝ}
    {u : ℝ^((2 * m + 3) + 1) → ℝ} (x : ℝ^(2 * m + 3)) (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem g h) u)
    (hmean : ∀ q, 0 < q → ContDiff ℝ (m + 2) (waveSphericalMean u x q))
    (hregular : ∀ k ≤ m,
      ContDiff ℝ 3 (fun p : ℝ^2 ↦ oddRadialTransform k (sphericalWaveWeight m u x (p 0)) (p 1)))
    (q r : ℝ) (hq : 0 < q) (hr : 0 < r) :
    deriv (deriv (fun a ↦ oddRadialTransform m (sphericalWaveWeight m u x a) r)) q =
      deriv (deriv (oddRadialTransform m (sphericalWaveWeight m u x q))) r := by
  have htime := deriv_deriv_oddRadialTransform_time m (sphericalWaveWeight m u x) hregular q r
  have hradial := secondDeriv_oddSphericalProfile_of_wave m x hq hu hsol (hmean q hq) hr
  have hweightSecond : (fun s ↦ deriv (deriv (fun a ↦ sphericalWaveWeight m u x a s)) q) =
        fun s ↦ s ^ (2 * m + 1) * deriv (deriv (fun a ↦ waveSphericalMean u x a s)) q := by
    funext s
    have hfirst : deriv (fun a ↦ sphericalWaveWeight m u x a s) =
        fun a ↦ s ^ (2 * m + 1) * deriv (fun b ↦ waveSphericalMean u x b s) a := by
      funext a
      exact deriv_const_mul_field _
    rw [hfirst, deriv_const_mul_field]
  rw [htime, hweightSecond]
  unfold sphericalWaveWeight
  simpa only [oddSphericalProfile, waveSphericalMean] using hradial.symm

/-- Oddness extends the reduced wave equation through zero and to negative signed radii. -/
private theorem transformedSphericalWave_waveOperator_eq_zero (m : ℕ)
    {g h : ℝ^(2 * m + 3) → ℝ} {u : ℝ^((2 * m + 3) + 1) → ℝ}
    (x : ℝ^(2 * m + 3)) (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem g h) u)
    (hmean : ∀ q, 0 < q → ContDiff ℝ (m + 2) (waveSphericalMean u x q))
    (hregular : ∀ k ≤ m, ContDiff ℝ 3
      (fun p : ℝ^2 ↦ oddRadialTransform k (sphericalWaveWeight m u x (p 0)) (p 1)))
    (p : ℝ^2) (hp : 0 < p 0) : waveOperator (transformedSphericalWave m u x) p = 0 := by
  let Ψ := fun q ↦ oddRadialTransform m (sphericalWaveWeight m u x q)
  have hodd (q : ℝ) : Function.Odd (Ψ q) :=
    oddRadialTransform_odd m (odd_sphericalWaveWeight m u x q)
  have htimeOdd (q : ℝ) : Function.Odd (fun r ↦ deriv (deriv (fun a ↦ Ψ a r)) q) :=
    PDE.Analysis.odd_deriv_parameter (fun s ↦ PDE.Analysis.odd_deriv_parameter hodd s) q
  have hspaceOdd (q : ℝ) : Function.Odd (deriv (deriv (Ψ q))) :=
    PDE.Analysis.odd_deriv_of_even (PDE.Analysis.even_deriv_of_odd (hodd q))
  have hsecond (q : ℝ) (hq : 0 < q) (r : ℝ) :
      deriv (deriv (fun a ↦ Ψ a r)) q = deriv (deriv (Ψ q)) r := by
    rcases lt_trichotomy r 0 with hr | hr | hr
    · have hpositive := transformedSphericalWave_secondDeriv_eq_of_pos
        m x hu hsol hmean hregular q (-r) hq (neg_pos.mpr hr)
      have heq := (htimeOdd q r).symm.trans (hpositive.trans (hspaceOdd q r))
      exact neg_injective heq
    · subst r
      rw [(htimeOdd q).map_zero, (hspaceOdd q).map_zero]
    · exact transformedSphericalWave_secondDeriv_eq_of_pos m x hu hsol hmean hregular q r hq hr
  have hW : ContDiff ℝ 2 (transformedSphericalWave m u x) :=
    (hregular m le_rfl).of_le (by norm_num)
  have hp_repr : timeSpaceCons (p 0) (EuclideanSpace.single (0 : Fin 1) (p 1)) = p := by
    ext i
    fin_cases i
    · exact timeSpaceCons_zero _ _
    · exact timeSpaceCons_single_one _ _
  rw [← hp_repr, waveOperator_one_timeSpaceCons_single _ hW]
  apply sub_eq_zero.mpr
  simpa only [transformedSphericalWave, Ψ, timeSpaceCons_zero, timeSpaceCons_single_one] using
    hsecond (p 0) hp (p 1)

/-- The transformed field satisfies the one-dimensional Cauchy problem, with its equation
and both initial traces derived from the original wave. -/
private theorem transformedSphericalWave_satisfiesCauchyProblem (m : ℕ) {g h : ℝ^(2 * m + 3) → ℝ}
    {u : ℝ^((2 * m + 3) + 1) → ℝ} (x : ℝ^(2 * m + 3)) (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem g h) u)
    (hmean : ∀ q, 0 < q → ContDiff ℝ (m + 2) (waveSphericalMean u x q))
    (hregular : ∀ k ≤ m,
      ContDiff ℝ 3 (fun p : ℝ^2 ↦ oddRadialTransform k (sphericalWaveWeight m u x (p 0)) (p 1))) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem
      (fun y : ℝ^1 ↦ oddSphericalProfile m g x (y 0))
      (fun y : ℝ^1 ↦ oddSphericalProfile m h x (y 0))) (transformedSphericalWave m u x) := by
  apply forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial
  · exact transformedSphericalWave_waveOperator_eq_zero m x hu hsol hmean hregular
  · intro p hp
    have hp_repr : timeSpaceCons 0 (spatialPartCLM 1 p) = p := by
      simpa [hp] using timeSpaceCons_spatialPartCLM p
    rw [← hp_repr]
    exact transformedSphericalWave_initial_position m x hsol _
  · intro p hp
    have hp_repr : timeSpaceCons 0 (spatialPartCLM 1 p) = p := by
      simpa [hp] using timeSpaceCons_spatialPartCLM p
    rw [← hp_repr]
    exact transformedSphericalWave_initial_velocity m x hu hsol
      (fun k hk ↦ (hregular k hk).of_le (by norm_num)) _

/-- The Evans-transformed spherical mean is the one-dimensional d'Alembert
solution determined by the transformed Cauchy data.

The joint `C³` hypothesis is the analytic removable-singularity input at
`r = 0` for every intermediate Evans transform.  From it, the wave equation,
the original Cauchy data, and the positive-radius EPD reduction, the proof
derives the transformed one-dimensional Cauchy problem and applies classical
uniqueness. -/
theorem oddSphericalProfile_eq_dAlembertFormula_of_wave (m : ℕ) {g h : ℝ^(2 * m + 3) → ℝ}
    {u : ℝ^((2 * m + 3) + 1) → ℝ} (x : ℝ^(2 * m + 3)) (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 2 * m + 3) g h) u)
    (hmean : ∀ q, 0 < q → ContDiff ℝ (m + 2) (waveSphericalMean u x q))
    (hg : ContDiff ℝ 2 (oddSphericalProfile m g x)) (hh : ContDiff ℝ 1 (oddSphericalProfile m h x))
    (hregular : ∀ k ≤ m, ContDiff ℝ 3 (fun p : ℝ^2 ↦ oddRadialTransform k
      (fun r ↦ r ^ (2 * m + 1) * waveSphericalMean u x (p 0) r) (p 1)))
    {t : ℝ} (ht : 0 ≤ t) :
    oddSphericalProfile m (fun y ↦ u (timeSpaceCons t y)) x =
      fun r ↦ dAlembertFormula (oddSphericalProfile m g x) (oddSphericalProfile m h x) r t := by
  let W := transformedSphericalWave m u x
  let G : ℝ^1 → ℝ := fun y ↦ oddSphericalProfile m g x (y 0)
  let H : ℝ^1 → ℝ := fun y ↦ oddSphericalProfile m h x (y 0)
  have hW : ContDiff ℝ 2 W := (hregular m le_rfl).of_le (by norm_num)
  have hG : ContDiff ℝ 2 (fun r ↦ G (EuclideanSpace.single (0 : Fin 1) r)) := by
    simpa only [G, PiLp.single_eq_same] using hg
  have hH : ContDiff ℝ 1 (fun r ↦ H (EuclideanSpace.single (0 : Fin 1) r)) := by
    simpa only [H, PiLp.single_eq_same] using hh
  have hsolW := transformedSphericalWave_satisfiesCauchyProblem m x hu hsol hmean hregular
  funext r
  have hunique := eq_dAlembertSolution1D_of_satisfiesResidualAssignedCauchyData
    hW hG hH hsolW ht (EuclideanSpace.single (0 : Fin 1) r)
  dsimp only [W, transformedSphericalWave] at hunique
  unfold sphericalWaveWeight at hunique
  simpa [G, H, oddSphericalProfile, waveSphericalMean, dAlembertSolution1D,
    timeSpaceCons_single_one] using hunique

/-- Evans's odd-dimensional representation follows from the wave equation and
its Cauchy data under the stated radial regularity assumptions and global
joint `C³` regularity of the specified totalized intermediate transforms on
the whole time-radius plane, including radius zero. -/
theorem eq_evansOddDimensionalFormula_of_wave (m : ℕ) {g h : ℝ^(2 * m + 3) → ℝ}
    {u : ℝ^((2 * m + 3) + 1) → ℝ} (x : ℝ^(2 * m + 3)) (t : Ioi (0 : ℝ)) (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 2 * m + 3) g h) u)
    (hmean : ∀ q, 0 < q → ContDiff ℝ (m + 2) (waveSphericalMean u x q))
    (hg : ContDiff ℝ 2 (oddSphericalProfile m g x)) (hh : ContDiff ℝ 1 (oddSphericalProfile m h x))
    (hregular : ∀ k ≤ m, ContDiff ℝ 3 (fun p : ℝ^2 ↦ oddRadialTransform k
      (fun r ↦ r ^ (2 * m + 1) * waveSphericalMean u x (p 0) r) (p 1))) :
    u (timeSpaceCons (t : ℝ) x) = evansOddDimensionalFormula m g h x t :=
  eq_evansOddDimensionalFormula_of_transformed_dAlembert m x t
    ((hmean (t : ℝ) t.property).of_le (by exact_mod_cast (show m + 1 ≤ m + 2 by omega))) hg hh
    (oddSphericalProfile_eq_dAlembertFormula_of_wave m x hu hsol hmean hg hh hregular t.property.le)

end WaveEquation
