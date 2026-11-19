/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.CenteredTrace
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ConeEnergy
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.DuhamelAmplitude
public import
  PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ClassicalRepresentation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.TraceL2
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Bounds

/-!
# Subcritical amplitude control for a wave candidate

Physical energy bounds supply both coordinates of the retarded H¹ trace. The PDE supplies the
Kirchhoff representation, the integral identity (14) of Evans, §12.3.2. The resulting bound is
independent of the candidate's original amplitude bound and of the length of its slab below a fixed
time horizon.

The candidate is ambient C². Spherical reduction supplies its representation with the C¹ real-power
forcing. The argument is steps 1-3 of the proof of Theorem 3 of Evans, §12.3.3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.2, equation (14); §12.3.3, Theorem 3 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric PDE PDE.Common PDE.Analysis WaveEquation
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Nonnegative potential energy controls the velocity on every spatial ball. -/
theorem lpNorm_velocity_ball_le_of_energy {V : ℝ → ℝ} {u : ℝ^4 → ℝ} (hV : ∀ z, 0 ≤ V z)
    (hu : ContDiff ℝ 2 u) (t : ℝ) (hi : Integrable (semilinearWaveSpatialEnergyDensity V u t))
    {E : ℝ} (hE : 0 ≤ E) (henergy : 2 * semilinearWaveSpatialEnergy V u t ≤ E ^ 2) (c : ℝ^3)
    (r : ℝ) :
    lpNorm (fun x ↦ (∂[0] u) (timeSpaceCons t x)) 2 (domainMeasure 3 (ball c r)) ≤ E := by
  have hc : Continuous (fun x : ℝ^3 ↦ (∂[0] u) (timeSpaceCons t x)) :=
    (contDiff_partialDeriv_of_succ (m := 1) (i := 0) hu).continuous.comp
      (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous
  have hs : Integrable (fun x : ℝ^3 ↦ ((∂[0] u) (timeSpaceCons t x)) ^ 2) := by
    convert (integrable_semilinearWaveSpatialKineticEnergyDensity V hV hu t hi).const_mul 2 using 1
    funext x
    simp only [semilinearWaveSpatialKineticEnergyDensity]
    ring
  have hm : MemLp (fun x : ℝ^3 ↦ (∂[0] u) (timeSpaceCons t x)) 2 (domainMeasure 3 (ball c r)) :=
    (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
      (hs.mono_measure Measure.restrict_le_self)
  have hb := setIntegral_le_integral (s := ball c r) hs
    (Filter.Eventually.of_forall fun x ↦ sq_nonneg ((∂[0] u) (timeSpaceCons t x)))
  have he := integral_semilinearWaveTimeDerivativeSq_le_two_mul_spatialEnergy V hV hu t hi
  rw [hm.integral_sq_eq_lpNorm_sq] at hb
  nlinarith [lpNorm_nonneg (f := fun x : ℝ^3 ↦ (∂[0] u) (timeSpaceCons t x))
    (p := 2) (μ := domainMeasure 3 (ball c r))]

/-- The centered retarded trace has a scaled H¹ bound depending only
on physical energy and the initial displacement bound. -/
theorem exists_centered_trace_bound_of_power_solution {p : ℝ} (hp : 1 ≤ p) {u : ℝ^4 → ℝ}
    (hu : ContDiff ℝ 2 u) (c : ℝ^3) {r T E G : ℝ} (hr : 0 < r) (hrT : r ≤ T) (hE : 0 ≤ E)
    (hG : 0 ≤ G) (hg : ∀ x : ℝ^3, ‖u (timeSpaceCons 0 x)‖ ≤ G)
    (hwave : ∀ t ∈ Ioo 0 r, ∀ x ∈ ball c (r - t), waveOperator u (timeSpaceCons t x) +
      Real.signedPower p (u (timeSpaceCons t x)) = 0)
    (hi : ∀ t ∈ Icc 0 r, Integrable (semilinearWaveSpatialEnergyDensity
      (Real.signedPowerPotential p) u t))
    (henergy : ∀ t ∈ Icc 0 r, 2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential p) u t ≤
      E ^ 2) :
    ∃ U : H¹(ball (0 : ℝ^3) r),
      baseRepresentative U =ᵐ[domainMeasure 3 (ball 0 r)] (fun x ↦ u (timeSpaceCons (r - ‖x‖) (c +
      x))) ∧
      ‖∇ U‖ ≤ E ∧ ‖wkpBaseCoordinateCLM U‖ / r ≤ E + G * √(T * volume.real (ball (0 : ℝ^3) 1)) := by
  obtain ⟨U, hbase, _, hgrad⟩ := exists_h1_retardedTrace_of_power_solution hp hu c hr.le hwave
  have hV := Real.contDiff_one_signedPowerPotential hp
  have hV0 := Real.signedPowerPotential_nonneg hp
  have hzero : (0 : ℝ) ∈ Icc 0 r := ⟨le_rfl, hr.le⟩
  have hcone : semilinearBackwardConeEnergy (Real.signedPowerPotential p) u c r 0 ≤
      semilinearWaveSpatialEnergy (Real.signedPowerPotential p) u 0 := by
    rw [semilinearBackwardConeEnergy_eq_ballIntegral hV.continuous
      (hu.of_le (by norm_num))]
    exact setIntegral_le_integral (hi 0 hzero)
      (Filter.Eventually.of_forall fun x ↦ semilinearWaveEnergyDensity_nonneg _ hV0 u _)
  have hgU : ‖∇ U‖ ≤ E := by nlinarith [henergy 0 hzero, norm_nonneg (∇ U)]
  have hbU := norm_base_retardedTrace_le (hu.of_le (by norm_num)) c hr.le hE
    (fun t ht ↦ lpNorm_velocity_ball_le_of_energy hV0 hu t (hi t ht) hE (henergy t ht) c r) U hbase
  obtain ⟨W, hW, hbW, hgW⟩ := exists_centered_retardedTrace U hbase
  refine ⟨W, hW, hgW.le.trans hgU, ?_⟩
  rw [hbW]
  have hb := div_le_div_of_nonneg_right hbU hr.le
  rw [add_div, mul_div_cancel_left₀ E hr.ne'] at hb
  exact hb.trans (by
    have h := lpNorm_initial_div_radius_le hG hg c hr hrT
    linarith)

/-- Every bounded C² real-power wave candidate on a finite forward slab obeys
an amplitude bound determined by the time horizon, energy, initial displacement,
and free wave. The cone trace and retarded representation are derived from the
PDE. -/
theorem exists_uniform_amplitude_bound_of_power_solution {p : ℝ} (hp : 1 < p) (hp5 : p < 5)
    (T E G V : ℝ) (hE : 0 ≤ E) (hG : 0 ≤ G) (hV : 0 ≤ V) :
    ∃ B : ℝ, 0 < B ∧ ∀ (S : ℝ) (u : ℝ^4 → ℝ) (g h : ℝ^3 → ℝ),
      0 < S → S ≤ T → ContDiff ℝ 2 u → ContDiff ℝ 3 g → ContDiff ℝ 2 h →
      (∀ x, u (timeSpaceCons 0 x) = g x) →
      (∀ x, (∂[0] u) (timeSpaceCons 0 x) = h x) →
      (∀ x, ‖g x‖ ≤ G) →
      (∀ t ∈ Ioc 0 S, ∀ x, |kirchhoffFormula g h x t| ≤ V) →
      (∀ t ∈ Ioo 0 S, ∀ x,
        waveOperator u (timeSpaceCons t x) + Real.signedPower p (u (timeSpaceCons t x)) = 0) →
      (∀ t ∈ Icc 0 S,
        Integrable (semilinearWaveSpatialEnergyDensity (Real.signedPowerPotential p) u t)) →
      (∀ t ∈ Icc 0 S,
        2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential p) u t ≤ E ^ 2) →
      (∃ A : ℝ, ∀ t ∈ Ioc 0 S, ∀ x, |u (timeSpaceCons t x)| ≤ A) →
      ∀ t ∈ Ioc 0 S, ∀ x, |u (timeSpaceCons t x)| ≤ B := by
  classical
  let F := E + G * √(T * volume.real (ball (0 : ℝ^3) 1))
  have hF : 0 ≤ F := add_nonneg hE (mul_nonneg hG (Real.sqrt_nonneg _))
  obtain ⟨B, hB, hbound⟩ := exists_uniform_amplitude_bound_of_duhamel hp hp5 T F V hF hV
  refine ⟨B, hB, ?_⟩
  intro S u g h hS hST hu hg hh hposition hinitial hgG hv hwave hi he hbounded
  let X := Ioc (0 : ℝ) S × ℝ^3
  let w : X → ℝ := fun z ↦ u (timeSpaceCons z.1.val z.2)
  let v : X → ℝ := fun z ↦ kirchhoffFormula g h z.2 z.1.val
  let r : X → ℝ := fun z ↦ z.1.val
  let σ : X → ℝ^3 → X := fun z y ↦ if hτ : 0 < z.1.val - ‖y‖ then
      (⟨z.1.val - ‖y‖, hτ, (sub_le_self _ (norm_nonneg y)).trans z.1.property.2⟩, z.2 + y) else z
  have htrace (z : X) : ∃ U : H¹(ball (0 : ℝ^3) (r z)),
      baseRepresentative U =ᵐ[domainMeasure 3 (ball 0 (r z))]
        (fun y ↦ u (timeSpaceCons (r z - ‖y‖) (z.2 + y))) ∧
      ‖∇ U‖ ≤ E ∧ ‖wkpBaseCoordinateCLM U‖ / r z ≤ F := by
    exact exists_centered_trace_bound_of_power_solution hp.le (hu.of_le (by norm_num)) z.2
      z.1.property.1 (z.1.property.2.trans hST) hE hG
      (fun x ↦ by rw [hposition]; exact hgG x)
      (fun t ht x _ ↦ hwave t ⟨ht.1, ht.2.trans_le z.1.property.2⟩ x)
      (fun t ht ↦ hi t ⟨ht.1, ht.2.trans z.1.property.2⟩)
      (fun t ht ↦ he t ⟨ht.1, ht.2.trans z.1.property.2⟩)
  choose U hbase hgrad hnorm using htrace
  have hbdd : BddAbove (range fun z : X ↦ |w z|) := by
    obtain ⟨A, hA⟩ := hbounded
    exact ⟨A, fun _ ⟨z, hz⟩ ↦ hz ▸ hA z.1.val z.1.property z.2⟩
  have hrep (z : X) : baseRepresentative (U z) =ᵐ[domainMeasure 3 (ball 0 (r z))]
      fun y ↦ w (σ z y) := by
    filter_upwards [hbase z, ae_restrict_mem measurableSet_ball] with y hy hball
    have hτ : 0 < z.1.val - ‖y‖ := by
      apply sub_pos.mpr
      simpa only [mem_ball, dist_zero_right] using hball
    simpa only [σ, hτ, ↓reduceDIte, w, r] using hy
  have hduhamel (z : X) : w z = v z - (1 / (4 * Real.pi)) *
      ∫ y in ball (0 : ℝ^3) (r z), Real.signedPower p (baseRepresentative (U z) y) / ‖y‖ := by
    exact eq_centered_retarded_ball_of_classical_power_solution hp.le hu hg hh
      hposition hinitial z.2 z.1.property.1
      (fun t ht x ↦ hwave t ⟨ht.1, ht.2.trans_le z.1.property.2⟩ x) (U z) (hbase z)
  have hamp := hbound w v r σ U hbdd (fun z ↦ z.1.property.1)
    (fun z ↦ z.1.property.2.trans hST) (fun z ↦ hv z.1.val z.1.property z.2)
    (fun z ↦ (hgrad z).trans (le_add_of_nonneg_right (mul_nonneg hG (Real.sqrt_nonneg _))))
    hnorm hrep hduhamel
  exact fun t ht x ↦ hamp (⟨t, ht⟩, x)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
