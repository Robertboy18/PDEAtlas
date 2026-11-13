/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.TravelingWave
public import PDE.Hyperbolic.ConservationLaw.Burgers.Viscosity.StationaryProfile
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import CAS.ExactTactic

/-!
# A coupled quadratic traveling layer

The linear coordinates `(a,b) ↦ (a+b,a+2b)` conjugate the diagonal flux
`(a²/2,4b+b²/2)` to the polynomial `flux`. The coordinate map is not
orthogonal. A translated and rescaled Burgers profile connects two
distinct nonzero states at speed `1/4` (`isViscousProfile_profile`, from
`isViscousProfile_of_first_order`). Its traveling waves solve the viscous system for
every `ε > 0` and converge to the planar shock as `ε → 0⁺`.

The characteristic speeds of the diagonal flux are `a` and `4 + b`. They coincide on
the line `a = 4 + b`, so the flux is strictly hyperbolic only off that line. Along the
layer `b = 1/2` and `3/20 < a < 7/20`.
-/

@[expose] public noncomputable section

open Filter Set BurgersEquation.Viscosity
open PDE.Hyperbolic.ConservationLaw PDE.Hyperbolic.ConservationLaw.System
open scoped ContDiff Topology

namespace PDE.Examples.Hyperbolic.ConservationLaw.System.ViscousProfile.CoupledPolynomial

/-- The polynomial flux after the nonorthogonal linear change of state. -/
def flux (u : ℝ^2) : ℝ^2 :=
  !₂[5 * u 0 ^ 2 / 2 - 3 * u 0 * u 1 - 4 * u 0 + u 1 ^ 2 + 4 * u 1,
    3 * u 0 ^ 2 - 4 * u 0 * u 1 - 8 * u 0 + 3 * u 1 ^ 2 / 2 + 8 * u 1]

/-- The layer `(3/4, 5/4) + (φ s / 20) (1, 1)`, with `φ = stationaryProfile 20 0`. -/
def profile (s : ℝ) : ℝ^2 :=
  !₂[3 / 4, 5 / 4] + (stationaryProfile 20 0 s / 20) • !₂[1, 1]

private theorem contDiff_flux : ContDiff ℝ ∞ flux := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : ℝ^2 ↦
      5 * q 0 ^ 2 / 2 - 3 * q 0 * q 1 - 4 * q 0 + q 1 ^ 2 + 4 * q 1)
    cas
  · change ContDiff ℝ ∞ (fun q : ℝ^2 ↦
      3 * q 0 ^ 2 - 4 * q 0 * q 1 - 8 * q 0 + 3 * q 1 ^ 2 / 2 + 8 * q 1)
    cas

private theorem contDiff_profile : ContDiff ℝ ∞ profile :=
  contDiff_const.add
    (((contDiff_stationaryProfile 20 0).div_const 20).smul contDiff_const)

/-- `flux` is the diagonal flux `(a²/2, 4b + b²/2)` conjugated by `(a, b) ↦ (a + b, a + 2b)`. -/
theorem flux_conjugacy (a b : ℝ) :
    flux (!₂[a + b, a + 2 * b]) =
      !₂[a ^ 2 / 2 + (4 * b + b ^ 2 / 2),
        a ^ 2 / 2 + 2 * (4 * b + b ^ 2 / 2)] := by
  ext i
  fin_cases i <;> simp only [flux] <;> cas

private theorem profile_first_order (s : ℝ) :
    HasDerivAt profile
      (flux (profile s) - flux (!₂[17 / 20, 27 / 20]) -
        (1 / 4 : ℝ) • (profile s - !₂[17 / 20, 27 / 20])) s := by
  have hd := (hasDerivAt_const s (!₂[3 / 4, 5 / 4] : ℝ^2)).add
    ((((contDiff_stationaryProfile 20 0).differentiable (by simp) s).hasDerivAt.div_const
      20).smul_const (!₂[1, 1] : ℝ^2))
  have heq : (0 : ℝ^2) + (deriv (stationaryProfile 20 0) s / 20) • !₂[1, 1] =
      flux (profile s) - flux (!₂[17 / 20, 27 / 20]) -
        (1 / 4 : ℝ) • (profile s - !₂[17 / 20, 27 / 20]) := by
    rw [deriv_stationaryProfile (by norm_num)]
    ext i
    fin_cases i <;>
      simp only [profile, flux, zero_add, Fin.zero_eta, Fin.mk_one, Fin.isValue,
        PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul, mul_one, one_div] <;> cas
  exact heq ▸ hd

private theorem scalar_left :
    Tendsto (stationaryProfile 20 0) atBot (𝓝 2) := by
  have harg : Tendsto (fun s : ℝ ↦ 2 * (s - 0) / 20) atBot atBot := by
    simpa only [sub_zero, div_eq_mul_inv, mul_assoc, id_eq] using
      (tendsto_id : Tendsto (id : ℝ → ℝ) atBot atBot).atBot_mul_const
        (by norm_num : (0 : ℝ) < 20⁻¹) |>.const_mul_atBot (by norm_num : (0 : ℝ) < 2)
  have he := Real.tendsto_exp_atBot.comp harg
  have hlim := ((tendsto_const_nhds (x := (4 : ℝ))).div
    (he.add_const 1) (by norm_num)).const_add (-2)
  unfold stationaryProfile
  convert hlim using 1 <;> norm_num

private theorem scalar_right :
    Tendsto (stationaryProfile 20 0) atTop (𝓝 (-2)) := by
  have harg : Tendsto (fun s : ℝ ↦ 2 * (s - 0) / 20) atTop atTop := by
    simpa only [sub_zero, div_eq_mul_inv, mul_assoc, id_eq] using
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop).atTop_mul_const
        (by norm_num : (0 : ℝ) < 20⁻¹) |>.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have he := (Real.tendsto_exp_atTop.comp harg).atTop_add
    (tendsto_const_nhds (x := (1 : ℝ)))
  unfold stationaryProfile
  simpa only [Function.comp_def, sub_zero, div_eq_mul_inv, mul_zero, add_zero] using
    ((tendsto_inv_atTop_zero.comp he).const_mul 4).const_add (-2)

/-- The layer is a viscous profile from `(17/20, 27/20)` to `(13/20, 23/20)` with speed
`1/4`. -/
theorem isViscousProfile_profile :
    IsViscousProfile flux (!₂[17 / 20, 27 / 20]) (!₂[13 / 20, 23 / 20])
      (1 / 4) profile := by
  apply isViscousProfile_of_first_order (contDiff_flux.differentiable (by simp))
    (contDiff_profile.of_le (by simp)) profile_first_order
  · have h := ((scalar_left.div_const 20).smul_const (!₂[1, 1] : ℝ^2)).const_add
      (!₂[3 / 4, 5 / 4] : ℝ^2)
    have heq : (!₂[3 / 4, 5 / 4] : ℝ^2) + (2 / 20 : ℝ) • !₂[1, 1] =
        !₂[17 / 20, 27 / 20] := by
      ext i
      fin_cases i <;> norm_num
    unfold profile
    simpa only [heq] using h
  · have h := ((scalar_right.div_const 20).smul_const (!₂[1, 1] : ℝ^2)).const_add
      (!₂[3 / 4, 5 / 4] : ℝ^2)
    have heq : (!₂[3 / 4, 5 / 4] : ℝ^2) + (-2 / 20 : ℝ) • !₂[1, 1] =
        !₂[13 / 20, 23 / 20] := by
      ext i
      fin_cases i <;> norm_num
    unfold profile
    simpa only [heq] using h
  · unfold RankineHugoniot
    ext i
    fin_cases i <;> norm_num [flux]

/-- For every `ε > 0` the traveling wave solves the viscous system. -/
theorem viscous_equation {ε : ℝ} (hε : 0 < ε) (p : ℝ^2) :
    fluxResidual flux (travelingWave profile (1 / 4) ε) p =
      ε • (∂[1] (∂[1] (travelingWave profile (1 / 4) ε))) p :=
  isViscousProfile_profile.fluxResidual_travelingWave
    (contDiff_flux.differentiable (by simp)) hε.ne' p

/-- As `ε → 0⁺` the traveling waves converge to the planar shock at every point off the
shock line. -/
theorem tendsto_viscous {p : ℝ^2} (hp : p 1 ≠ (1 / 4 : ℝ) * p 0) :
    Tendsto (fun ε : ℝ ↦ travelingWave profile (1 / 4) ε p) (𝓝[>] 0)
      (𝓝 (planarShock (!₂[17 / 20, 27 / 20] : ℝ^2) (!₂[13 / 20, 23 / 20])
        (1 / 4) p)) :=
  isViscousProfile_profile.tendsto_travelingWave hp

end PDE.Examples.Hyperbolic.ConservationLaw.System.ViscousProfile.CoupledPolynomial
