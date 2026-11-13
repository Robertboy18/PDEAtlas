/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus
import CAS.ExactTactic

/-!
# Stationary viscous Burgers profiles

The translated profile `-2 + 4 / (1 + exp (2(x-a)/ε))` has size at most two
and converges away from `a` to the stationary jump from two to minus two.
Its viscous equation is certified by the checked calculus engine.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace BurgersEquation.Viscosity

/-- A translated stationary viscous shock of width proportional to `ε`. -/
def stationaryProfile (ε a x : ℝ) : ℝ :=
  -2 + 4 / (Real.exp (2 * (x - a) / ε) + 1)

/-- The exponential denominator is strictly positive, including at zero viscosity
where division in the definition is totalized. -/
theorem stationaryProfile_denominator_pos (ε a x : ℝ) :
    0 < Real.exp (2 * (x - a) / ε) + 1 :=
  add_pos (Real.exp_pos _) zero_lt_one

/-- Every fixed profile is smooth in space. -/
theorem contDiff_stationaryProfile (ε a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (stationaryProfile ε a) := by
  unfold stationaryProfile
  apply contDiff_const.add
  apply contDiff_const.div
  · exact ((contDiff_const.mul (contDiff_id.sub contDiff_const)).div_const ε).exp.add contDiff_const
  · exact fun x ↦ ne_of_gt (stationaryProfile_denominator_pos ε a x)

/-- The profile remains in the interval `[-2,2]`, uniformly in the width and center. -/
theorem norm_stationaryProfile_le (ε a x : ℝ) :
    ‖stationaryProfile ε a x‖ ≤ 2 := by
  have hden := stationaryProfile_denominator_pos ε a x
  have hlo : 0 ≤ 4 / (Real.exp (2 * (x - a) / ε) + 1) := by positivity
  have hhi : 4 / (Real.exp (2 * (x - a) / ε) + 1) ≤ 4 := by
    apply (div_le_iff₀ hden).2
    nlinarith [Real.exp_pos (2 * (x - a) / ε)]
  rw [Real.norm_eq_abs, abs_le]
  unfold stationaryProfile
  constructor <;> linarith

/-- The ordinary derivative obeys the integrated stationary Burgers equation.
`cas` checks the analytic derivative and the rational identity. -/
theorem deriv_stationaryProfile {ε : ℝ} (hε : ε ≠ 0) (a x : ℝ) :
    deriv (stationaryProfile ε a) x = (stationaryProfile ε a x ^ 2 / 2 - 2) / ε := by
  have hden := ne_of_gt (stationaryProfile_denominator_pos ε a x)
  unfold stationaryProfile
  cas using hε

/-- The profile satisfies the second-order stationary Burgers equation. -/
theorem stationaryProfile_equation {ε : ℝ} (hε : ε ≠ 0) (a x : ℝ) :
    ε * deriv (deriv (stationaryProfile ε a)) x =
      stationaryProfile ε a x * deriv (stationaryProfile ε a) x := by
  unfold stationaryProfile
  cas using hε

/-- The limiting stationary jump; its value at the jump is assigned to the right. -/
def stationaryJump (a x : ℝ) : ℝ := if x < a then 2 else -2

/-- At every point away from the jump the viscous profiles converge to that jump. -/
theorem tendsto_stationaryProfile {a x : ℝ} (hx : x ≠ a) :
    Tendsto (fun ε : ℝ ↦ stationaryProfile ε a x) (𝓝[>] 0) (𝓝 (stationaryJump a x)) := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have harg : Tendsto (fun ε : ℝ ↦ 2 * (x - a) / ε) (𝓝[>] 0) atBot := by
      simpa only [div_eq_mul_inv] using
        tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (by linarith : 2 * (x - a) < 0)
    have he := Real.tendsto_exp_atBot.comp harg
    have hlim := (tendsto_const_nhds (x := (4 : ℝ))).div (he.add_const 1) (by norm_num)
    convert hlim.const_add (-2) using 1 <;> norm_num [stationaryProfile, stationaryJump, hx]
  · have harg : Tendsto (fun ε : ℝ ↦ 2 * (x - a) / ε) (𝓝[>] 0) atTop := by
      simpa only [div_eq_mul_inv] using
        tendsto_inv_nhdsGT_zero.const_mul_atTop (by linarith : 0 < 2 * (x - a))
    have he := (Real.tendsto_exp_atTop.comp harg).atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
    have hlim := (tendsto_inv_atTop_zero.comp he).const_mul 4
    simpa [stationaryProfile, stationaryJump, not_lt_of_gt hx, div_eq_mul_inv] using
      hlim.const_add (-2)

end BurgersEquation.Viscosity
