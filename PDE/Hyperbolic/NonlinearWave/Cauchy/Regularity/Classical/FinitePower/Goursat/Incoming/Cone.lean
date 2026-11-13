/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Incoming.Data
import CAS.ExactTactic

/-!
# Incoming free-wave signs on the cone

The chosen free profile has positive transverse derivative wherever it vanishes on the incoming
cone, including for the corresponding Kirchhoff field.
-/

@[expose] public noncomputable section

section

open Set Filter
open scoped ContDiff Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- On the incoming unit cone, the baseline value is twice the initial transition. -/
theorem radialFreeField_incomingProfile_on_cone {t : ℝ} {x : ℝ^3} (hx : t + ‖x‖ = 1) :
    radialFreeField incomingProfile (t, x) = 2 * incomingCutoff (2 * t - 1) := by
  have hF1 : incomingProfile 1 = 0 := by
    rw [incomingProfile_eq_linear (by constructor <;> norm_num)]
    norm_num
  by_cases hr : ‖x‖ = 0
  · have ht : t = 1 := by linarith
    simp only [radialFreeField, radialFreeProfile, hr, ht, sub_zero, add_zero, dslope_same,
      hasDerivAt_incomingProfile_one.deriv]
    have hχ : incomingCutoff (2 * 1 - 1) = 1 :=
      Real.smoothTransition.one_of_one_le (by norm_num)
    rw [hχ, mul_one]
  · have hs : t - ‖x‖ ≤ 1 := by linarith [norm_nonneg x]
    rw [radialFreeField, radialFreeProfile_eq_div _ _ hr, hx, hF1, incomingProfile_eq_of_le_one hs]
    have harg : t - ‖x‖ = 2 * t - 1 := by linarith
    rw [harg]
    generalize incomingCutoff (2 * t - 1) = c
    generalize ‖x‖ = r at hx hr ⊢
    have ht : t = 1 - r := by linarith
    rw [ht]
    cas using hr

/-- A zero of the incoming scalar profile with zero derivative gives a positive
full cone-direction derivative of the radial free field. -/
theorem fderiv_radialFreeField_cone_of_zero_jet {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hF1 : F 1 = 0)
    (hD1 : HasDerivAt F 1 1) {t : ℝ} {x : ℝ^3} (hx : t + ‖x‖ = 1) (hr : ‖x‖ ≠ 0)
    (hFs : F (t - ‖x‖) = 0) (hDs : HasDerivAt F 0 (t - ‖x‖)) :
    fderiv ℝ (radialFreeField F) (t, x) (t, x) = 1 / ‖x‖ := by
  let q : ℝ → ℝ × ℝ^3 := fun a ↦ ((1 + a) * t, (1 + a) • x)
  have hq : HasDerivAt q (t, x) 0 := by
    simpa only [one_mul, one_smul, q, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const t).prodMk
        (((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const x)
  have hq0 : q 0 = (t, x) := by simp only [q, add_zero, one_mul, one_smul]
  have hcomp : HasDerivAt (fun a ↦ radialFreeField F (q a))
      (fderiv ℝ (radialFreeField F) (t, x) (t, x)) 0 := by
    have hd := ((contDiff_three_radialFreeField hF).differentiable (by norm_num)
      (q 0)).hasFDerivAt.comp_hasDerivAt 0 hq
    simpa only [Function.comp_def, hq0] using hd
  have hnum : HasDerivAt (fun a : ℝ ↦ F (1 + a) - F ((1 + a) * (t - ‖x‖))) 1 0 := by
    have hleft := hD1.comp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_add 1) (by simp)
    have hright := hDs.comp_of_eq 0
      (((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const (t - ‖x‖)) (by simp)
    simpa only [Function.comp_def, Pi.sub_apply, id_eq, one_mul, mul_one, zero_mul,
      sub_zero] using hleft.fun_sub hright
  have hden : HasDerivAt (fun a : ℝ ↦ (1 + a) * ‖x‖) ‖x‖ 0 := by
    simpa only [one_mul, id_eq] using ((hasDerivAt_id (0 : ℝ)).const_add 1).mul_const ‖x‖
  have hd : HasDerivAt (fun a : ℝ ↦ (F (1 + a) - F ((1 + a) * (t - ‖x‖))) / ((1 + a) * ‖x‖))
      (1 / ‖x‖) 0 := by
    convert hnum.div hden (by simpa only [add_zero, one_mul] using hr) using 1
    simp only [add_zero, one_mul, hF1, hFs, sub_self, zero_mul, sub_zero]
    generalize ‖x‖ = r at hr ⊢
    cas using hr
  have hgerm : (fun a : ℝ ↦ radialFreeField F (q a)) =ᶠ[𝓝 0]
      (fun a : ℝ ↦ (F (1 + a) - F ((1 + a) * (t - ‖x‖))) / ((1 + a) * ‖x‖)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) ∈ Ioi (-1) by norm_num)] with a ha
    have ha1 : 0 < 1 + a := by have ha' : -1 < a := ha; linarith
    have hnorm : ‖(1 + a) • x‖ = (1 + a) * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha1]
    have hne : ‖(1 + a) • x‖ ≠ 0 := by rw [hnorm]; exact mul_ne_zero ha1.ne' hr
    change radialFreeField F ((1 + a) * t, (1 + a) • x) = _
    rw [radialFreeField, radialFreeProfile_eq_div _ _ hne, hnorm]
    have hplus : (1 + a) * t + (1 + a) * ‖x‖ = 1 + a := by
      generalize ‖x‖ = r at hx ⊢
      have ht : t = 1 - r := by linarith
      rw [ht]
      cas
    have hminus : (1 + a) * t - (1 + a) * ‖x‖ = (1 + a) * (t - ‖x‖) := by
      generalize ‖x‖ = r
      cas
    rw [hplus, hminus]
  exact hcomp.unique (hd.congr_of_eventuallyEq hgerm)

/-- Every zero of the baseline on the complete incoming cone has strictly
positive derivative in the full cone direction. -/
theorem fderiv_incomingProfile_pos_on_cone_zeros {t : ℝ} {x : ℝ^3} (hx : t + ‖x‖ = 1)
    (hz : radialFreeField incomingProfile (t, x) = 0) :
    0 < fderiv ℝ (radialFreeField incomingProfile) (t, x) (t, x) := by
  have hχ : incomingCutoff (2 * t - 1) = 0 := by
    rw [radialFreeField_incomingProfile_on_cone hx] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have htle := (incomingCutoff_eq_zero_iff _).mp hχ
  have hr : 0 < ‖x‖ := by linarith
  have harg : t - ‖x‖ = 2 * t - 1 := by linarith
  have hzero := incomingProfile_zero_jet hχ
  have hF1 : incomingProfile 1 = 0 := by
    rw [incomingProfile_eq_linear (by constructor <;> norm_num)]
    norm_num
  have hDs : HasDerivAt incomingProfile 0 (t - ‖x‖) := by
    have hd := (contDiff_incomingProfile.differentiable (by simp) (2 * t - 1)).hasDerivAt
    rw [hzero.2] at hd
    simpa only [harg] using hd
  rw [fderiv_radialFreeField_cone_of_zero_jet contDiff_incomingProfile hF1
    hasDerivAt_incomingProfile_one hx hr.ne' (by simpa only [harg] using hzero.1) hDs]
  exact one_div_pos.mpr hr

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open Set Filter
open PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
open scoped ContDiff Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- Positive homotheties remain in the forward half-space, so the forward
Kirchhoff identity also identifies the full cone-direction derivative at time zero. -/
theorem fderiv_cauchyFreeField_incoming_data_cone {t : ℝ} (ht : 0 ≤ t) (x : ℝ^3) :
    fderiv ℝ (cauchyFreeField incomingDisplacement incomingVelocity) (t, x) (t, x) =
      fderiv ℝ (radialFreeField incomingProfile) (t, x) (t, x) := by
  let q : ℝ → ℝ × ℝ^3 := fun a ↦ (1 + a) • (t, x)
  have hq : HasDerivAt q (t, x) 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const (t, x)
  have hq0 : q 0 = (t, x) := by simp only [q, add_zero, one_smul]
  have hfree : DifferentiableAt ℝ (cauchyFreeField incomingDisplacement incomingVelocity) (t, x) :=
    (contDiff_one_cauchyFreeField
      (contDiff_incomingDisplacement.of_le (by norm_num))
      (contDiff_incomingVelocity.of_le (by norm_num))).differentiable one_ne_zero _
  have hrad : DifferentiableAt ℝ (radialFreeField incomingProfile) (t, x) :=
    (contDiff_three_radialFreeField contDiff_incomingProfile).differentiable (by norm_num) _
  have hleft : HasDerivAt (fun a ↦ cauchyFreeField incomingDisplacement incomingVelocity (q a))
      (fderiv ℝ (cauchyFreeField incomingDisplacement incomingVelocity) (t, x) (t, x)) 0 := by
    have hd : HasFDerivAt (cauchyFreeField incomingDisplacement incomingVelocity)
        (fderiv ℝ (cauchyFreeField incomingDisplacement incomingVelocity) (t, x)) (q 0) :=
      hq0.symm ▸ hfree.hasFDerivAt
    exact hd.comp_hasDerivAt 0 hq
  have hright : HasDerivAt (fun a ↦ radialFreeField incomingProfile (q a))
      (fderiv ℝ (radialFreeField incomingProfile) (t, x) (t, x)) 0 := by
    have hd : HasFDerivAt (radialFreeField incomingProfile)
        (fderiv ℝ (radialFreeField incomingProfile) (t, x)) (q 0) := hq0.symm ▸ hrad.hasFDerivAt
    exact hd.comp_hasDerivAt 0 hq
  have heq : (fun a ↦ cauchyFreeField incomingDisplacement incomingVelocity (q a)) =ᶠ[𝓝 0]
      (fun a ↦ radialFreeField incomingProfile (q a)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show (0 : ℝ) ∈ Ioi (-1) by norm_num)] with a ha
    apply cauchyFreeField_incoming_data
    change 0 ≤ (1 + a) * t
    exact mul_nonneg (by have ha' : -1 < a := ha; linarith) ht
  exact hleft.unique (hright.congr_of_eventuallyEq heq)

/-- The compact-data Kirchhoff baseline has strictly positive full cone derivative
at every zero on the complete forward incoming unit cone. -/
theorem fderiv_incoming_cauchyFreeField_pos_on_cone_zeros {t : ℝ} {x : ℝ^3} (ht : 0 ≤ t)
    (hx : t + ‖x‖ = 1) (hz : cauchyFreeField incomingDisplacement incomingVelocity (t, x) = 0) :
    0 < fderiv ℝ (cauchyFreeField incomingDisplacement incomingVelocity) (t, x) (t, x) := by
  rw [fderiv_cauchyFreeField_incoming_data_cone ht]
  apply fderiv_incomingProfile_pos_on_cone_zeros hx
  rwa [cauchyFreeField_incoming_data ht] at hz

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
