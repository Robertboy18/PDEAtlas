/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Derivatives
public import PDE.Fluid.DeGregorio.Uniqueness.Evolution
import CAS.ExactTactic

/-!
# The H² energy production of a frozen transport step

Differentiation of the three square integrals and spatial integration by parts
give the production of `∫ (w² + w_x² + w_xx²)`. The original transport equation
is the only evolution hypothesis. All third output derivatives disappear from
the production after integration by parts.

The endpoint hypotheses require the output and its first two derivatives to vanish
at `±L`, which holds in a strict support enclosure. No boundary condition is imposed
on the Hilbert velocity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis

namespace DeGregorio

/-- The sum of the three square integrals defining the classical H² energy on
a fixed spatial interval. -/
def sobolevEnergyTwo (w : ℝ → ℝ → ℝ) (L t : ℝ) : ℝ :=
  (∫ x in Icc (-L) L, w x t ^ 2) +
    (∫ x in Icc (-L) L, deriv (fun y ↦ w y t) x ^ 2) +
      ∫ x in Icc (-L) L, deriv (deriv (fun y ↦ w y t)) x ^ 2

/-- Each component of the classical H² energy is nonnegative. -/
theorem sobolevEnergyTwo_nonneg (w : ℝ → ℝ → ℝ) (L t : ℝ) :
    0 ≤ sobolevEnergyTwo w L t :=
  add_nonneg (add_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)
    (integral_nonneg fun _ ↦ sq_nonneg _)) (integral_nonneg fun _ ↦ sq_nonneg _)

private theorem integral_transport_source_energy {d u s : ℝ → ℝ} {L : ℝ}
    (hd : ContDiff ℝ 1 d) (hu : ContDiff ℝ 1 u) (hs : Continuous s)
    (hL : 0 ≤ L) (hleft : d (-L) = 0) (hright : d L = 0) :
    (2 * ∫ x in Icc (-L) L, d x * (s x - u x * deriv d x)) =
      ∫ x in Icc (-L) L, deriv u x * d x ^ 2 + 2 * d x * s x := by
  have hflux := integral_transport_flux_deriv_eq_zero hd hu hL hleft hright
  have hD := hd.continuous_deriv le_rfl
  have hU := hu.continuous_deriv le_rfl
  have hres : Continuous (fun x ↦ 2 * (d x * (s x - u x * deriv d x))) := by
    fun_prop
  have hfluxCont : Continuous (fun x ↦
      deriv u x * d x ^ 2 + 2 * u x * d x * deriv d x) := by fun_prop
  calc
    _ = (∫ x in Icc (-L) L, 2 * (d x * (s x - u x * deriv d x))) +
        ∫ x in Icc (-L) L,
          deriv u x * d x ^ 2 + 2 * u x * d x * deriv d x := by
      rw [integral_const_mul, hflux, add_zero]
    _ = _ := by
      rw [← integral_add hres.integrableOn_Icc hfluxCont.integrableOn_Icc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      cas

/-- The frozen transport equation determines the H² energy derivative.
Its production contains at most two output derivatives and three velocity
derivatives, hence at most two Hilbert-transformed input derivatives. -/
theorem hasDerivAt_sobolevEnergyTwo_of_frozen_transport
    {w u : ℝ → ℝ → ℝ} {L t : ℝ}
    (hw : ContDiff ℝ 3 (Function.uncurry w))
    (hu : ContDiff ℝ 3 (fun y ↦ u y t))
    (htransport : ∀ x, deriv (w x) t + u x t * deriv (fun y ↦ w y t) x =
      deriv (fun y ↦ u y t) x * w x t)
    (hL : 0 ≤ L)
    (hleft : w (-L) t = 0 ∧ deriv (fun y ↦ w y t) (-L) = 0 ∧
      deriv (deriv (fun y ↦ w y t)) (-L) = 0)
    (hright : w L t = 0 ∧ deriv (fun y ↦ w y t) L = 0 ∧
      deriv (deriv (fun y ↦ w y t)) L = 0) :
    HasDerivAt (sobolevEnergyTwo w L)
      (∫ x in Icc (-L) L,
        3 * deriv (fun y ↦ u y t) x * w x t ^ 2 +
          deriv (fun y ↦ u y t) x * deriv (fun y ↦ w y t) x ^ 2 -
          deriv (fun y ↦ u y t) x * deriv (deriv (fun y ↦ w y t)) x ^ 2 +
          2 * deriv (deriv (fun y ↦ u y t)) x * w x t * deriv (fun y ↦ w y t) x +
          2 * deriv (deriv (deriv (fun y ↦ u y t))) x * w x t *
            deriv (deriv (fun y ↦ w y t)) x +
          2 * deriv (deriv (fun y ↦ u y t)) x * deriv (fun y ↦ w y t) x *
            deriv (deriv (fun y ↦ w y t)) x) t := by
  let q := fun x s ↦ deriv (fun y ↦ w y s) x
  let r := fun x s ↦ deriv (fun y ↦ q y s) x
  let v := fun x ↦ u x t
  have hq : ContDiff ℝ 2 (Function.uncurry q) := Calculus.contDiff_spatial_deriv hw
  have hr : ContDiff ℝ 1 (Function.uncurry r) := Calculus.contDiff_spatial_deriv hq
  have hw₁ : ContDiff ℝ 1 (fun x ↦ w x t) :=
    (hw.of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
  have hq₁ : ContDiff ℝ 1 (fun x ↦ q x t) :=
    (hq.of_le (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
  have hr₁ : ContDiff ℝ 1 (fun x ↦ r x t) :=
    hr.comp (contDiff_id.prodMk contDiff_const)
  have hu₁ : ContDiff ℝ 1 v := hu.of_le (by norm_num)
  have hv' := hu.continuous_deriv (by norm_num)
  have hv'' := (hu.deriv' (n := 2)).continuous_deriv (by norm_num)
  have hv''' := ((hu.deriv' (n := 2)).deriv' (n := 1)).continuous_deriv le_rfl
  have hwtime (x : ℝ) :
      deriv (w x) t = deriv v x * w x t - v x * q x t :=
    eq_sub_of_add_eq (htransport x)
  have hqtime (x : ℝ) :
      deriv (q x) t = deriv (deriv v) x * w x t - v x * r x t :=
    (hasDerivAt_slope_of_frozen_transport (x := x)
      (hw.of_le (by norm_num)) (hu.of_le (by norm_num)) htransport).deriv
  have hrtime (x : ℝ) :
      deriv (r x) t = deriv (deriv (deriv v)) x * w x t +
        deriv (deriv v) x * q x t - deriv v x * r x t -
        v x * deriv (fun y ↦ r y t) x :=
    (hasDerivAt_curvature_of_frozen_transport (x := x) hw hu htransport).deriv
  have hE := ((hasDerivAt_integral_sq_Icc_of_contDiff
    (hw.of_le (by norm_num)) (-L) L t).add
      (hasDerivAt_integral_sq_Icc_of_contDiff (hq.of_le (by norm_num)) (-L) L t)).add
        (hasDerivAt_integral_sq_Icc_of_contDiff hr (-L) L t)
  change HasDerivAt (sobolevEnergyTwo w L) _ t at hE
  have hflux₀ := integral_transport_source_energy hw₁ hu₁
    (hv'.mul hw₁.continuous) hL hleft.1 hright.1
  have hflux₁ := integral_transport_source_energy hq₁ hu₁
    (hv''.mul hw₁.continuous) hL hleft.2.1 hright.2.1
  have hflux₂ := integral_transport_source_energy hr₁ hu₁
    (((hv'''.mul hw₁.continuous).add (hv''.mul hq₁.continuous)).sub
      (hv'.mul hr₁.continuous)) hL hleft.2.2 hright.2.2
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply] at hflux₀ hflux₁ hflux₂
  apply hE.congr_deriv
  simp_rw [hwtime, hqtime, hrtime]
  rw [hflux₀, hflux₁, hflux₂]
  have hC₀ : Continuous (fun x ↦ deriv v x * w x t ^ 2 +
      2 * w x t * (deriv v x * w x t)) := by fun_prop
  have hC₁ : Continuous (fun x ↦ deriv v x * q x t ^ 2 +
      2 * q x t * (deriv (deriv v) x * w x t)) := by fun_prop
  have hC₂ : Continuous (fun x ↦ deriv v x * r x t ^ 2 + 2 * r x t *
      (deriv (deriv (deriv v)) x * w x t + deriv (deriv v) x * q x t -
        deriv v x * r x t)) := by fun_prop
  have hC₀₁ : Continuous (fun x ↦
      (deriv v x * w x t ^ 2 + 2 * w x t * (deriv v x * w x t)) +
        (deriv v x * q x t ^ 2 +
          2 * q x t * (deriv (deriv v) x * w x t))) := hC₀.add hC₁
  rw [← integral_add hC₀.integrableOn_Icc hC₁.integrableOn_Icc,
    ← integral_add hC₀₁.integrableOn_Icc hC₂.integrableOn_Icc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  dsimp [q, r, v]
  cas

end DeGregorio
