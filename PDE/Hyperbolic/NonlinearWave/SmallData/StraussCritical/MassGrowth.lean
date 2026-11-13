/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.Interior
public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.LogarithmicSource
public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.PowerGrowth

/-!
# Critical normalized mass growth from the wave equation

The characteristic formula and outgoing shell derive the interior bound.
Spherical Jensen and polar integration then give an unbounded source coefficient.
The spatial-mass derivative identities integrate this gain twice.
Neither the logarithmic estimate nor mass growth is an assumption of these results.
-/

@[expose] public noncomputable section

open Filter MeasureTheory PDE.Analysis PDE.Common Set

namespace WaveEquation.SmallData

/-- The source, divided by the critical baseline power, tends to infinity. -/
theorem tendsto_semilinear_source_div_rpow_atTop {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} {R p : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hh : ContDiff ℝ 2 h)
    (hhs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0) (hhn : ∀ y, 0 ≤ h y) (hR : 0 < R) (hp : 2 < p)
    (hcritical : p * (p - 2) = 1) (hH : 0 < ∫ y : ℝ^3, h y)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) :
    Tendsto (fun t ↦ (∫ x : ℝ^3, |u (timeSpaceCons t x)| ^ p) / t ^ (2 - p)) atTop atTop := by
  let c := interiorSourceCoefficient R (∫ y : ℝ^3, h y) p
  have hc : 0 < c := interiorSourceCoefficient_pos hR hH
  have hdiv : Tendsto (fun t : ℝ ↦ t / 4) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num) tendsto_id
  have hlog₀ : Tendsto (fun t : ℝ ↦ Real.log (t / 4) - Real.log (4 * R)) atTop atTop := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      tendsto_atTop_add_const_right atTop (-Real.log (4 * R)) (Real.tendsto_log_atTop.comp hdiv)
  have hlog : Tendsto (fun t : ℝ ↦ unitSphereArea 3 * c ^ p *
        (Real.log (t / 4) - Real.log (4 * R))) atTop atTop :=
    hlog₀.const_mul_atTop (mul_pos unitSphereArea_pos (Real.rpow_pos_of_pos hc p))
  apply tendsto_atTop_mono' atTop _ hlog
  filter_upwards [eventually_ge_atTop (16 * R)] with t ht
  have ht0 : 0 < t := by linarith only [hR, ht]
  have hv : ContDiff ℝ 2 (fun x : ℝ^3 ↦ u (timeSpaceCons t x)) :=
    hu.comp (contDiff_timeSpaceCons_spatial 3 t)
  have hvi : Integrable (fun x : ℝ^3 ↦ |u (timeSpaceCons t x)| ^ p) :=
    ((contDiff_two_abs_rpow hp).comp hv).continuous.integrable_of_hasCompactSupport
      ((hs.hasCompactSupport_slice ht0.le).comp_left
        (g := fun z : ℝ ↦ |z| ^ p) (by simp [Real.zero_rpow (by linarith : p ≠ 0)]))
  have hbound := power_integral_logarithmic_lower_bound hv hvi hc hR ht hp hcritical
    (fun a ha hat ↦ radiusMean_semilinear_interior_lower_bound
      hu hh hhs hhn hR hp hH hwave hzero hinitial ha hat)
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht0 _)).mpr
  convert hbound using 1
  ring

/-- The normalized spatial mass tends to infinity at the critical exponent.
All source growth and both differentiations under the spatial integral are derived. -/
theorem tendsto_critical_spatialMass_div_rpow_atTop {u : ℝ^4 → ℝ} {h : ℝ^3 → ℝ} {R p : ℝ}
    (hu : ContDiff ℝ 2 u) (hs : HasForwardSupport u R) (hh : ContDiff ℝ 2 h)
    (hhs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0) (hhn : ∀ y, 0 ≤ h y) (hR : 0 < R) (hp : 2 < p)
    (hcritical : p * (p - 2) = 1) (hH : 0 < ∫ y : ℝ^3, h y)
    (hwave : ∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
      |u (timeSpaceCons t x)| ^ p)
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) :
    Tendsto (fun t ↦ spatialMass u t / t ^ (4 - p)) atTop atTop := by
  have hp3 : p < 3 := by nlinarith only [hcritical]
  apply Kato.tendsto_div_rpow_atTop_of_acceleration (a := R) hp3
    (fun t ht ↦ hasDerivAt_spatialMass (hu.of_le (by norm_num)) hs (hR.trans_le ht))
  apply (tendsto_semilinear_source_div_rpow_atTop hu hs hh hhs hhn hR hp
    hcritical hH hwave hzero hinitial).congr'
  filter_upwards [eventually_ge_atTop R] with t ht
  rw [(hasDerivAt_spatialMass_time_eq_source hu hs (hR.trans_le ht)
    (hwave t (hR.trans_le ht))).deriv]

end WaveEquation.SmallData
