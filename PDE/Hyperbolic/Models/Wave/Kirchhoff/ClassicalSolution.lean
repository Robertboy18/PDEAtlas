/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SphericalMean.Regularity
public import PDE.Hyperbolic.Models.Wave.KirchhoffRepresentation
import PDE.FDeriv.Calculus

/-!
# Construction of the three-dimensional Kirchhoff solution

The radius-weighted spherical mean solves the wave equation. Its time
derivative supplies the displacement term in Kirchhoff's formula. The
construction uses `C³` displacement and `C²` velocity data, with no decay or
support restrictions.

The signed-radius expression also describes the total surface
integral at time zero, so the initial traces follow from joint regularity. This is Evans, §2.4.1,
Theorem 2, for `n = 3`, where the representation (31) reduces to Kirchhoff's formula (22).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1, equation (22) and Theorem 2 for n = 3.
  <https://doi.org/10.1090/gsm/019>
-/

open PDE (SatisfiesPDEProblem)

@[expose] public noncomputable section

namespace WaveEquation

open PDE (time)
open PDE.Analysis PDE.Common

/-- The radius-weighted spherical mean on canonical spacetime. Its initial
displacement is zero and its initial velocity is `f`. -/
def kirchhoffPotential (f : ℝ^3 → ℝ) : ℝ^4 → ℝ :=
  spaceTimeUncurry (fun x t ↦ t * unitSphereAverage 3 f x t)

/-- Evaluation of the Kirchhoff potential in space and time coordinates. -/
@[simp]
theorem kirchhoffPotential_timeSpaceCons (f : ℝ^3 → ℝ) (x : ℝ^3) (t : ℝ) :
    kirchhoffPotential f (timeSpaceCons t x) = t * unitSphereAverage 3 f x t := by
  simp [kirchhoffPotential, spaceTimeUncurry, time]

/-- The potential preserves every finite order of regularity of the data. -/
theorem contDiff_kirchhoffPotential {k : ℕ} {f : ℝ^3 → ℝ} (hf : ContDiff ℝ k f) :
    ContDiff ℝ k (kirchhoffPotential f) := by
  apply (contDiff_spaceTimeUncurry_iff _).mpr
  exact contDiff_snd.mul (contDiff_unitSphereAverage hf)

/-- The time derivative of the potential is the derivative of the
radius-weighted mean. -/
theorem partialDeriv_kirchhoffPotential_time {f : ℝ^3 → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ^3) (t : ℝ) :
    (∂[0] (kirchhoffPotential f)) (timeSpaceCons t x) =
      deriv (fun r ↦ r * unitSphereAverage 3 f x r) t := by
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ _ _
    ((contDiff_kirchhoffPotential hf).differentiable one_ne_zero _)]
  simp only [kirchhoffPotential_timeSpaceCons]

/-- Kirchhoff's surface-integral field is the sum of a differentiated
displacement potential and the velocity potential. -/
theorem kirchhoffFormula_eq_potentials {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 1 g) (hh : Continuous h) :
    spaceTimeUncurry (kirchhoffFormula g h) =
      fun p ↦ (∂[0] (kirchhoffPotential g)) p + kirchhoffPotential h p := by
  funext p
  obtain ⟨t, x, rfl⟩ := (timeSpaceContinuousLinearEquiv 3).symm.surjective p
  simp only [timeSpaceContinuousLinearEquiv_symm_apply]
  simp only [spaceTimeUncurry, spatialPart_timeSpaceCons, time, timeSpaceCons_zero,
    kirchhoffFormula_eq_sphericalMean hg hh, kirchhoffPotential_timeSpaceCons,
    partialDeriv_kirchhoffPotential_time hg]

/-- The Kirchhoff field is `C²` jointly in space and time for the classical
`C³` displacement and `C²` velocity hypotheses. -/
theorem contDiff_two_kirchhoffFormula {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 2 (spaceTimeUncurry (kirchhoffFormula g h)) := by
  rw [kirchhoffFormula_eq_potentials (hg.of_le (by norm_num)) hh.continuous]
  exact (PDE.contDiff_partialDeriv_of_succ (m := 2)
    (contDiff_kirchhoffPotential hg)).add (contDiff_kirchhoffPotential hh)

/-- The first time derivative of the potential at the initial slice is the
prescribed velocity. -/
theorem partialDeriv_kirchhoffPotential_initial {f : ℝ^3 → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝ^3) :
    (∂[0] (kirchhoffPotential f)) (timeSpaceCons 0 x) = f x := by
  rw [partialDeriv_kirchhoffPotential_time hf]
  simpa using ((hasDerivAt_id (0 : ℝ)).fun_mul (hasDerivAt_unitSphereAverage f x 0 hf)).deriv

/-- The radius-weighted mean constructed from `C²` data solves the
three-dimensional wave equation at every positive time. -/
theorem waveOperator_kirchhoffPotential {f : ℝ^3 → ℝ}
    (hf : ContDiff ℝ 2 f) {p : ℝ^4} (hp : 0 < p 0) :
    waveOperator (kirchhoffPotential f) p = 0 := by
  have hreg := contDiff_kirchhoffPotential hf
  have heq := waveOperator_timeSpaceCons hreg (spatialPartCLM 3 p) (p 0)
  rw [timeSpaceCons_spatialPartCLM] at heq
  rw [heq]
  simp only [kirchhoffPotential_timeSpaceCons]
  rw [secondDeriv_radius_mul_unitSphereAverage hf _ hp, PDE.laplacian_const_smul,
    laplacian_unitSphereAverage hf, sub_self]

/-- The potential has zero initial acceleration. Oddness in the signed
radius forces its second time derivative to vanish at the center. -/
theorem secondPartialDeriv_kirchhoffPotential_initial {f : ℝ^3 → ℝ}
    (hf : ContDiff ℝ 2 f) (x : ℝ^3) :
    (∂[0] (∂[0] (kirchhoffPotential f))) (timeSpaceCons 0 x) = 0 := by
  rw [secondPartialDeriv_timeSpaceCons (contDiff_kirchhoffPotential hf)]
  simp only [kirchhoffPotential_timeSpaceCons]
  have hodd : Function.Odd (fun r ↦ r * unitSphereAverage 3 f x r) := by
    simpa only [oddSphericalProfile_zero] using oddSphericalProfile_odd 0 f x
  exact (odd_deriv_of_even (even_deriv_of_odd hodd)).map_zero

/-- The time derivative of the displacement potential also solves the wave
equation. The residual is differentiated on the open positive-time region. -/
theorem waveOperator_partialDeriv_kirchhoffPotential {f : ℝ^3 → ℝ}
    (hf : ContDiff ℝ 3 f) {p : ℝ^4} (hp : 0 < p 0) :
    waveOperator (∂[0] (kirchhoffPotential f)) p = 0 :=
  waveOperator_partialDeriv_eq_zero_of_positive_time (contDiff_kirchhoffPotential hf)
    (fun _ hq ↦ waveOperator_kirchhoffPotential (hf.of_le (by norm_num)) hq) 0 hp

/-- Kirchhoff's surface-integral candidate solves the wave equation
for `C³` displacement and `C²` velocity data. -/
theorem waveOperator_kirchhoffFormula {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) {p : ℝ^4} (hp : 0 < p 0) :
    waveOperator (spaceTimeUncurry (kirchhoffFormula g h)) p = 0 := by
  rw [kirchhoffFormula_eq_potentials (hg.of_le (by norm_num)) hh.continuous]
  have hgpot := contDiff_kirchhoffPotential hg
  have hgtime : ContDiff ℝ 2 (∂[0] (kirchhoffPotential g)) :=
    PDE.contDiff_partialDeriv_of_succ (m := 2) hgpot
  rw [waveOperator_add hgtime.contDiffAt (contDiff_kirchhoffPotential hh).contDiffAt,
    waveOperator_partialDeriv_kirchhoffPotential hg hp, waveOperator_kirchhoffPotential hh hp,
    zero_add]

/-- The total Kirchhoff field has the prescribed displacement on the initial
slice. Joint regularity supplies the corresponding limiting trace. -/
theorem kirchhoffFormula_initial_position (g h : ℝ^3 → ℝ) (x : ℝ^3) :
    spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons 0 x) = g x := by
  simp [spaceTimeUncurry, time, kirchhoffFormula]

/-- Kirchhoff's field has the prescribed initial velocity. Two displacement
derivatives and one velocity derivative already suffice for this identity. -/
theorem partialDeriv_kirchhoffFormula_initial_velocity {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (x : ℝ^3) :
    (∂[0] (spaceTimeUncurry (kirchhoffFormula g h))) (timeSpaceCons 0 x) = h x := by
  rw [kirchhoffFormula_eq_potentials (hg.of_le (by norm_num)) hh.continuous]
  have hgtime : ContDiff ℝ 1 (∂[0] (kirchhoffPotential g)) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) (contDiff_kirchhoffPotential hg)
  rw [PDE.partialDeriv_add (hgtime.differentiable one_ne_zero _)
    ((contDiff_kirchhoffPotential hh).differentiable one_ne_zero _),
    secondPartialDeriv_kirchhoffPotential_initial hg,
    partialDeriv_kirchhoffPotential_initial hh, zero_add]

/-- The constructed Kirchhoff field satisfies the wave residual and both
assigned Cauchy data. Its classical regularity is
`contDiff_two_kirchhoffFormula`. -/
theorem kirchhoffFormula_satisfiesResidualAssignedCauchyData {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 3) g h)
      (spaceTimeUncurry (kirchhoffFormula g h)) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
  · exact fun p hp ↦ waveOperator_kirchhoffFormula hg hh hp
  · intro p hp
    have heq := timeSpaceCons_spatialPartCLM p
    rw [hp] at heq
    have hpos := kirchhoffFormula_initial_position g h (spatialPartCLM 3 p)
    rw [heq] at hpos
    simpa only [spatialPartCLM_eq_spatialPart] using hpos
  · intro p hp
    have heq := timeSpaceCons_spatialPartCLM p
    rw [hp] at heq
    have hvel := partialDeriv_kirchhoffFormula_initial_velocity
      (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) (spatialPartCLM 3 p)
    rw [heq] at hvel
    simpa only [spatialPartCLM_eq_spatialPart] using hvel

/-- The displacement trace holds jointly in space and time. In particular,
it implies the positive-time limit in the Cauchy problem. -/
theorem tendsto_kirchhoffFormula_initial_position {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (x : ℝ^3) :
    Filter.Tendsto (spaceTimeUncurry (kirchhoffFormula g h))
      (nhds (timeSpaceCons 0 x)) (nhds (g x)) := by
  simpa only [ContinuousAt, kirchhoffFormula_initial_position] using
    (contDiff_two_kirchhoffFormula hg hh).continuous.continuousAt (x := timeSpaceCons 0 x)

/-- The velocity trace also holds jointly in space and time. -/
theorem tendsto_partialDeriv_kirchhoffFormula_initial_velocity {g h : ℝ^3 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (x : ℝ^3) :
    Filter.Tendsto (∂[0] (spaceTimeUncurry (kirchhoffFormula g h)))
      (nhds (timeSpaceCons 0 x)) (nhds (h x)) := by
  have hreg : ContDiff ℝ 1 (∂[0] (spaceTimeUncurry (kirchhoffFormula g h))) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) (contDiff_two_kirchhoffFormula hg hh)
  simpa only [ContinuousAt, partialDeriv_kirchhoffFormula_initial_velocity
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num))] using
      hreg.continuous.continuousAt (x := timeSpaceCons 0 x)

/-- With zero displacement, Kirchhoff's full field is the velocity potential. -/
theorem kirchhoffFormula_zero_displacement {h : ℝ^3 → ℝ} (hh : Continuous h) :
    spaceTimeUncurry (kirchhoffFormula (fun _ ↦ 0) h) = kirchhoffPotential h := by
  rw [kirchhoffFormula_eq_potentials contDiff_const hh]
  have hz : kirchhoffPotential (fun _ : ℝ^3 ↦ (0 : ℝ)) = fun _ ↦ 0 := by
    funext z
    simp [kirchhoffPotential, spaceTimeUncurry, unitSphereAverage]
  simp only [hz, PDE.partialDeriv_const, zero_add]

end WaveEquation
