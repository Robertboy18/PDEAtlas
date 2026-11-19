/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.KdV.TravelingWave
public import PDE.Hyperbolic.Models.KdV.Profile
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# KdV solitary waves with general speed and dispersion

For `u_t + a u u_x + b u_xxx = 0`, the solitary wave of positive speed `c`
and positive dispersion `b` is

`u(t,x) = (3c/a) sech²((√(c/b)/2) (x - ct - x₀))`.

We prove the analytic PDE, global smoothness, positivity for `a > 0`,
the moving crest, and decay at both spatial infinities. A separate theorem uses
an arbitrary inverse width `k`, with the relations `c = 4bk²` and `aA = 12bk²`.
Thus both the speed and scale parameterizations are available.

The convention `a = b = 1` gives amplitude `3c`; the coefficient-six convention `a = 6`,
`b = 1` gives amplitude `c/2`. The latter is the KdV equation (4) of Evans, §4.2.1(b), and its
solitary wave is the soliton derived there from (5)-(11), with Evans's speed `σ` and shift `c`
written `c` and `x₀`. These are single solitary waves.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.2.1(b), equations (4)-(11) and the soliton formula.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace KdVEquation

open PDE.Representations.Similarity Filter
open scoped Topology ContDiff

/-- The amplitude and speed relations turn the explicit scaled profile into a
classical KdV solution. No sign restriction is needed for this algebraic identity. -/
theorem scaled_soliton_isSolution (nonlinearity dispersion amplitude scale speed center : ℝ)
    (hspeed : speed = 4 * dispersion * scale ^ 2)
    (hamplitude : nonlinearity * amplitude = 12 * dispersion * scale ^ 2) :
    IsSolution nonlinearity dispersion
      (travelingWave1D (solitonProfile amplitude scale center) speed) := by
  apply travelingWave1D_isSolution_of_profile_ode
    ((contDiff_solitonProfile amplitude scale center).of_le (by norm_num))
    nonlinearity dispersion speed 0
  intro z
  rw [solitonProfile_second_derivative, hspeed]
  unfold solitonProfile
  generalize sechSq (scale * (z - center)) = q
  cas using hamplitude

/-- Prescribing the inverse width gives amplitude `12bk²/a` and speed `4bk²`.
For positive dispersion and nonzero scale, this speed is positive. -/
theorem soliton_from_scale_isSolution {nonlinearity : ℝ}
    (hnonlinearity : nonlinearity ≠ 0) (dispersion scale center : ℝ) :
    IsSolution nonlinearity dispersion (travelingWave1D (solitonProfile
      (12 * dispersion * scale ^ 2 / nonlinearity) scale center) (4 * dispersion * scale ^ 2)) := by
  apply scaled_soliton_isSolution _ _ _ _ _ _ rfl
  cas

/-- The solitary wave with prescribed speed, in the convention
`u_t + a u u_x + b u_xxx = 0`. Analytic solution theorems assume `a ≠ 0`, `b > 0`, `c > 0`. -/
def soliton (nonlinearity dispersion speed center : ℝ) : ℝ^2 → ℝ :=
  travelingWave1D
    (solitonProfile (3 * speed / nonlinearity) (Real.sqrt (speed / dispersion) / 2) center)
    speed

/-- The speed-parameterized solitary wave in the usual hyperbolic-secant notation. -/
theorem soliton_eq_cosh (nonlinearity dispersion speed center : ℝ) (p : ℝ^2) :
    soliton nonlinearity dispersion speed center p = (3 * speed / nonlinearity) /
      Real.cosh (Real.sqrt (speed / dispersion) / 2 * (p 1 - speed * p 0 - center)) ^ 2 := by
  unfold soliton travelingWave1D solitonProfile
  rw [sechSq_eq_inv_cosh_sq, mul_one_div]

/-- Every parameter choice defines a globally smooth spacetime field. -/
theorem contDiff_soliton (nonlinearity dispersion speed center : ℝ) :
    ContDiff ℝ ∞ (soliton nonlinearity dispersion speed center) := by
  unfold soliton travelingWave1D
  exact (contDiff_solitonProfile _ _ _).comp (by fun_prop)

/-- The speed and inverse-width relation for positive dispersion and speed. -/
theorem soliton_speed_scale {dispersion speed : ℝ}
    (hdispersion : 0 < dispersion) (hspeed : 0 < speed) :
    speed = 4 * dispersion * (Real.sqrt (speed / dispersion) / 2) ^ 2 := by
  have hsqrt := Real.sq_sqrt (le_of_lt (div_pos hspeed hdispersion))
  cas using hsqrt

/-- A solitary wave of any positive speed and positive dispersion solves the
KdV PDE. A negative nonlinearity is allowed and gives a negative-amplitude wave. -/
theorem soliton_isSolution {nonlinearity dispersion speed : ℝ} (hnonlinearity : nonlinearity ≠ 0)
    (hdispersion : 0 < dispersion) (hspeed : 0 < speed) (center : ℝ) :
    IsSolution nonlinearity dispersion (soliton nonlinearity dispersion speed center) := by
  unfold soliton
  apply scaled_soliton_isSolution nonlinearity dispersion (3 * speed / nonlinearity)
    (Real.sqrt (speed / dispersion) / 2) speed center (soliton_speed_scale hdispersion hspeed)
  have hscale := soliton_speed_scale hdispersion hspeed
  cas using hscale

/-- Expanded analytic PDE endpoint, with the first time derivative and third spatial derivative. -/
theorem soliton_satisfies_kdv {nonlinearity dispersion speed : ℝ} (hnonlinearity : nonlinearity ≠ 0)
    (hdispersion : 0 < dispersion) (hspeed : 0 < speed) (center : ℝ) (p : ℝ^2) :
    (∂[(0 : Fin 2)] (soliton nonlinearity dispersion speed center)) p +
      nonlinearity * soliton nonlinearity dispersion speed center p *
        (∂[(1 : Fin 2)] (soliton nonlinearity dispersion speed center)) p +
      dispersion * (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] (∂[(1 : Fin 2)]
        (soliton nonlinearity dispersion speed center)))) p = 0 :=
  (soliton_isSolution hnonlinearity hdispersion hspeed center).equation p

/-- Positive speed and nonlinearity give a positive wave at every finite spacetime point. -/
theorem soliton_pos {nonlinearity speed : ℝ} (hnonlinearity : 0 < nonlinearity) (hspeed : 0 < speed)
    (dispersion center : ℝ) (p : ℝ^2) :
    0 < soliton nonlinearity dispersion speed center p := by
  unfold soliton travelingWave1D solitonProfile
  exact mul_pos (div_pos (mul_pos (by norm_num) hspeed) hnonlinearity) (sechSq_pos _)

/-- The crest moves to the right with the prescribed speed and has amplitude `3c/a`. -/
theorem soliton_at_crest (nonlinearity dispersion speed center t : ℝ) :
    soliton nonlinearity dispersion speed center !₂[t, center + speed * t] =
      3 * speed / nonlinearity := by
  unfold soliton travelingWave1D solitonProfile
  simp

/-- For positive amplitude, the moving crest is a global maximum. -/
theorem soliton_le_crest {nonlinearity speed : ℝ} (hnonlinearity : 0 < nonlinearity)
    (hspeed : 0 < speed) (dispersion center : ℝ) (p : ℝ^2) :
    soliton nonlinearity dispersion speed center p ≤ 3 * speed / nonlinearity := by
  unfold soliton travelingWave1D solitonProfile
  exact mul_le_of_le_one_right
    (le_of_lt (div_pos (mul_pos (by norm_num) hspeed) hnonlinearity)) (sechSq_le_one _)

/-- At each fixed time, the solitary wave decays to zero as space tends to the right. -/
theorem tendsto_soliton_atTop {dispersion speed : ℝ} (hdispersion : 0 < dispersion)
    (hspeed : 0 < speed) (nonlinearity center t : ℝ) :
    Tendsto (fun x : ℝ ↦ soliton nonlinearity dispersion speed center !₂[t, x]) atTop (𝓝 0) := by
  have hscale : 0 < Real.sqrt (speed / dispersion) / 2 := by positivity
  have hphase : Tendsto (fun x : ℝ ↦ Real.sqrt (speed / dispersion) / 2 * (x - speed * t - center))
      atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using (tendsto_atTop_add_const_right atTop (-center)
        (tendsto_atTop_add_const_right atTop (-(speed * t)) tendsto_id)).const_mul_atTop hscale
  have h := (tendsto_sechSq_atTop.comp hphase).const_mul (3 * speed / nonlinearity)
  simpa [soliton, travelingWave1D, solitonProfile] using h

/-- At each fixed time, the solitary wave also decays to zero as space tends to the left. -/
theorem tendsto_soliton_atBot {dispersion speed : ℝ} (hdispersion : 0 < dispersion)
    (hspeed : 0 < speed) (nonlinearity center t : ℝ) :
    Tendsto (fun x : ℝ ↦ soliton nonlinearity dispersion speed center !₂[t, x]) atBot (𝓝 0) := by
  have hscale : 0 < Real.sqrt (speed / dispersion) / 2 := by positivity
  have hphase : Tendsto (fun x : ℝ ↦ Real.sqrt (speed / dispersion) / 2 * (x - speed * t - center))
      atBot atBot := by
    simpa only [sub_eq_add_neg, id_eq] using (tendsto_atBot_add_const_right atBot (-center)
        (tendsto_atBot_add_const_right atBot (-(speed * t)) tendsto_id)).const_mul_atBot hscale
  have h := (tendsto_sechSq_atBot.comp hphase).const_mul (3 * speed / nonlinearity)
  simpa [soliton, travelingWave1D, solitonProfile] using h

/-- The normalization `a = b = 1`: amplitude `3c`, speed `c`, and positive cubic dispersion.
Despite the name, the KdV equation (4) of Evans, §4.2.1(b), is the coefficient-six form of
`coefficient_six_soliton_isSolution`. -/
theorem evans_soliton_isSolution {speed : ℝ} (hspeed : 0 < speed) (center : ℝ) :
    IsSolution 1 1 (fun p : ℝ^2 ↦
      3 * speed / Real.cosh (Real.sqrt speed / 2 * (p 1 - speed * p 0 - center)) ^ 2) := by
  have h := soliton_isSolution (by norm_num : (1 : ℝ) ≠ 0)
    (by norm_num : (0 : ℝ) < 1) hspeed center
  simpa only [funext (soliton_eq_cosh 1 1 speed center), div_one] using h

/-- The coefficient-six normalization has amplitude `c/2`, with the same speed and width.
This is the soliton of Evans, §4.2.1(b), for the KdV equation (4). -/
theorem coefficient_six_soliton_isSolution {speed : ℝ} (hspeed : 0 < speed) (center : ℝ) :
    IsSolution 6 1 (fun p : ℝ^2 ↦
      (speed / 2) / Real.cosh (Real.sqrt speed / 2 * (p 1 - speed * p 0 - center)) ^ 2) := by
  have h := soliton_isSolution (by norm_num : (6 : ℝ) ≠ 0)
    (by norm_num : (0 : ℝ) < 1) hspeed center
  have hamplitude : 3 * speed / 6 = speed / 2 := by cas
  simpa only [funext (soliton_eq_cosh 6 1 speed center), div_one, hamplitude] using h

end KdVEquation
