/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import CAS.ExactTactic

/-!
# Spatial difference-energy identities

Integration by parts separates the nonlinear difference terms from the linear
rescaling contribution. Both frozen iteration and coupled uniqueness use these
identities.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace DeGregorio

/-- The transport flux has zero integral derivative when the difference
vorticity vanishes at the endpoints of the energy interval. -/
theorem integral_transport_flux_deriv_eq_zero {d u : ℝ → ℝ} {L : ℝ}
    (hd : ContDiff ℝ 1 d) (hu : ContDiff ℝ 1 u) (hL : 0 ≤ L)
    (hleft : d (-L) = 0) (hright : d L = 0) :
    (∫ x in Icc (-L) L,
      deriv u x * d x ^ 2 + 2 * u x * d x * deriv d x) = 0 := by
  have hderiv (x : ℝ) : HasDerivAt (fun y ↦ u y * d y ^ 2)
      (deriv u x * d x ^ 2 + 2 * u x * d x * deriv d x) x := by
    convert! ((hu.differentiable (by norm_num) x).hasDerivAt.mul
      ((hd.differentiable (by norm_num) x).hasDerivAt.pow 2)) using 1
    simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    cas
  have hcont : Continuous (fun x ↦
      deriv u x * d x ^ 2 + 2 * u x * d x * deriv d x) :=
    ((hu.continuous_deriv le_rfl).mul (hd.continuous.pow 2)).add
      (((continuous_const.mul hu.continuous).mul hd.continuous).mul
        (hd.continuous_deriv le_rfl))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hderiv x) (hcont.intervalIntegrable (-L) L)
  rw [intervalIntegral.integral_of_le (neg_le_self hL),
    ← integral_Icc_eq_integral_Ioc] at hftc
  simpa only [hleft, hright, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_self] using hftc

/-- Integration by parts combines transport and stretching into the coefficient
`3 u_x`, leaving the two coupling terms. -/
theorem integral_difference_transport_energy {d u v w : ℝ → ℝ} {L : ℝ}
    (hd : ContDiff ℝ 1 d) (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) (hL : 0 ≤ L)
    (hleft : d (-L) = 0) (hright : d L = 0) :
    (2 * ∫ x in Icc (-L) L, d x *
      (deriv u x * d x + deriv v x * w x - u x * deriv d x - v x * deriv w x)) =
      ∫ x in Icc (-L) L,
        3 * deriv u x * d x ^ 2 + 2 * d x * deriv v x * w x -
          2 * d x * v x * deriv w x := by
  have hflux := integral_transport_flux_deriv_eq_zero hd hu hL hleft hright
  have hD := hd.continuous_deriv le_rfl
  have hU := hu.continuous_deriv le_rfl
  have hV := hv.continuous_deriv le_rfl
  have hW := hw.continuous_deriv le_rfl
  have hres : Continuous (fun x ↦ 2 * (d x *
      (deriv u x * d x + deriv v x * w x - u x * deriv d x - v x * deriv w x))) := by
    fun_prop
  have hfluxCont : Continuous (fun x ↦
      deriv u x * d x ^ 2 + 2 * u x * d x * deriv d x) := by fun_prop
  calc
    _ = (∫ x in Icc (-L) L, 2 * (d x *
        (deriv u x * d x + deriv v x * w x - u x * deriv d x - v x * deriv w x))) +
        ∫ x in Icc (-L) L,
          deriv u x * d x ^ 2 + 2 * u x * d x * deriv d x := by
      rw [integral_const_mul, hflux, add_zero]
    _ = _ := by
      rw [← integral_add hres.integrableOn_Icc hfluxCont.integrableOn_Icc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      cas

/-- Linear spatial transport and amplitude rescaling contribute `(2 cw + cl) E`
when the difference vorticity vanishes at both endpoints. -/
theorem integral_linear_rescaling_energy {d : ℝ → ℝ} {L : ℝ}
    (hd : ContDiff ℝ 1 d) (hL : 0 ≤ L) (hleft : d (-L) = 0) (hright : d L = 0)
    (cl cw : ℝ) :
    (2 * ∫ x in Icc (-L) L, d x * (cw * d x - cl * x * deriv d x)) =
      (2 * cw + cl) * ∫ x in Icc (-L) L, d x ^ 2 := by
  have hflux : (∫ x in Icc (-L) L, d x ^ 2 + 2 * x * d x * deriv d x) = 0 := by
    simpa using integral_transport_flux_deriv_eq_zero
      (u := fun x : ℝ ↦ x) hd contDiff_id hL hleft hright
  have hD := hd.continuous_deriv le_rfl
  have hrate : Continuous (fun x ↦ 2 * (d x * (cw * d x - cl * x * deriv d x))) := by
    fun_prop
  have hfluxCont : Continuous (fun x ↦ cl * (d x ^ 2 + 2 * x * d x * deriv d x)) := by
    fun_prop
  calc
    _ = (∫ x in Icc (-L) L, 2 * (d x * (cw * d x - cl * x * deriv d x))) +
        ∫ x in Icc (-L) L, cl * (d x ^ 2 + 2 * x * d x * deriv d x) := by
      rw [integral_const_mul, integral_const_mul, hflux, mul_zero, add_zero]
    _ = _ := by
      rw [← integral_add hrate.integrableOn_Icc hfluxCont.integrableOn_Icc,
        ← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      cas

end DeGregorio
