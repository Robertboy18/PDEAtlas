/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import CAS.ExactTactic

/-!
# Mixed energy estimates with singular endpoint multipliers

The two multiplier inequalities use disjoint parts of the energy interval.
Adding them retains both multipliers in the pointwise denominator. The endpoint
fluxes are limits, so no differentiability of a compact extension is required.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace SobolevSpace.WeightedEndpoint

/-- Completing the square gives the local multiplier estimate. -/
theorem quadratic_le_of_sq_le_mul {A C ξ p q : ℝ}
    (hC : 0 < C) (hξ : ξ ^ 2 ≤ A * C) :
    2 * ξ * p * q ≤ A * p ^ 2 + C * q ^ 2 := by
  have hs := sq_nonneg (C * q - ξ * p)
  have hm := mul_nonneg (sub_nonneg.mpr hξ) (sq_nonneg p)
  have he : C * (A * p ^ 2 + C * q ^ 2 - 2 * ξ * p * q) =
      (C * q - ξ * p) ^ 2 + (A * C - ξ ^ 2) * p ^ 2 := by cas
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hC).mp (by rw [he]; linarith))

/-- The upper-bound form of the fundamental theorem with one-sided endpoint
limits. Only the majorant, not the derivative, needs to be integrable. -/
theorem sub_le_integral_of_tendsto
    {f f' e : ℝ → ℝ} {a b fa fb : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (he : IntegrableOn e (Ioo a b))
    (hbound : ∀ x ∈ Ioo a b, f' x ≤ e x)
    (ha : Tendsto f (𝓝[>] a) (𝓝 fa))
    (hb : Tendsto f (𝓝[<] b) (𝓝 fb)) :
    fb - fa ≤ ∫ x in Ioo a b, e x := by
  classical
  let F := Function.update (Function.update f a fa) b fb
  have hFd : ∀ x ∈ Ioo a b, HasDerivAt F (f' x) x := by
    intro x hx
    apply (hd x hx).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    simp only [F, Function.update_of_ne hy.2.ne, Function.update_of_ne hy.1.ne']
  have hFc : ContinuousOn F (Icc a b) := by
    rw [continuousOn_update_iff, continuousOn_update_iff, Icc_sdiff_right, Ico_sdiff_left]
    refine ⟨⟨fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt, ?_⟩, ?_⟩
    · exact fun _ ↦ ha.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self)
    · rintro -
      refine (hb.congr' ?_).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
      filter_upwards [Ioo_mem_nhdsLT hab] with x hx
      exact (Function.update_of_ne hx.1.ne' _ _).symm
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab.le hFc
    (fun x hx ↦ (hFd x hx).hasDerivWithinAt)
    ((integrableOn_Icc_iff_integrableOn_Ioo).mpr he) hbound
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at h
  simpa [F, hab.ne, hab.ne'] using h

/-- The two Riccati inequalities control a point value by the full mixed energy.
The left and right integrals partition the interval rather than each consuming
the full energy. -/
theorem mixed_sq_le_energy
    {q φ σ ξ₀ ξL : ℝ → ℝ} {L x α₀ αL : ℝ}
    (hx : x ∈ Ioo 0 L) (hα₀ : 0 < α₀) (hαL : 0 < αL)
    (hq : ∀ y ∈ Ioo 0 L, HasDerivAt q (deriv q y) y)
    (hξ₀ : ∀ y ∈ Ioo 0 L, HasDerivAt ξ₀ (deriv ξ₀ y) y)
    (hξL : ∀ y ∈ Ioo 0 L, HasDerivAt ξL (deriv ξL y) y)
    (hσ : ∀ y ∈ Ioo 0 L, 0 < σ y)
    (hleft : ∀ y ∈ Ioo 0 L, ξ₀ y ^ 2 ≤ α₀ * σ y * (α₀ * φ y - deriv ξ₀ y))
    (hright : ∀ y ∈ Ioo 0 L, ξL y ^ 2 ≤ αL * σ y * (αL * φ y + deriv ξL y))
    (hflux₀ : Tendsto (fun y ↦ ξ₀ y * q y ^ 2) (𝓝[>] 0) (𝓝 0))
    (hfluxL : Tendsto (fun y ↦ ξL y * q y ^ 2) (𝓝[<] L) (𝓝 0))
    (he : IntegrableOn (fun y ↦ q y ^ 2 * φ y + deriv q y ^ 2 * σ y) (Ioo 0 L)) :
    (ξ₀ x / α₀ + ξL x / αL) * q x ^ 2 ≤
      ∫ y in Ioo 0 L, q y ^ 2 * φ y + deriv q y ^ 2 * σ y := by
  let e := fun y ↦ q y ^ 2 * φ y + deriv q y ^ 2 * σ y
  have hlsub : Ioo 0 x ⊆ Ioo 0 L := Ioo_subset_Ioo le_rfl hx.2.le
  have hrsub : Ioo x L ⊆ Ioo 0 L := Ioo_subset_Ioo hx.1.le le_rfl
  have hdl (y : ℝ) (hy : y ∈ Ioo 0 L) :=
    (hξ₀ y hy).mul ((hq y hy).pow 2)
  have hdr (y : ℝ) (hy : y ∈ Ioo 0 L) :=
    ((hξL y hy).mul ((hq y hy).pow 2)).neg
  have hl := sub_le_integral_of_tendsto hx.1
    (fun y hy ↦ hdl y (hlsub hy)) ((he.mono_set hlsub).const_mul α₀)
    (fun y hy ↦ by
      have hb := quadratic_le_of_sq_le_mul (A := α₀ * φ y - deriv ξ₀ y)
        (ξ := ξ₀ y) (p := q y) (q := deriv q y)
        (mul_pos hα₀ (hσ y (hlsub hy)))
        (by simpa only [mul_comm] using hleft y (hlsub hy))
      simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      nlinarith only [hb])
    hflux₀ ((hdl x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hr := sub_le_integral_of_tendsto hx.2
    (fun y hy ↦ hdr y (hrsub hy)) ((he.mono_set hrsub).const_mul αL)
    (fun y hy ↦ by
      have hb := quadratic_le_of_sq_le_mul (A := αL * φ y + deriv ξL y)
        (ξ := -ξL y) (p := q y) (q := deriv q y)
        (mul_pos hαL (hσ y (hrsub hy)))
        (by simpa only [neg_sq, mul_comm] using hright y (hrsub hy))
      simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
      nlinarith only [hb])
    ((hdr x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hfluxL.neg
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, neg_zero, sub_zero,
    integral_const_mul, zero_sub, neg_neg] at hl hr
  have hl' : ξ₀ x * q x ^ 2 / α₀ ≤ ∫ y in Ioo 0 x, e y :=
    (div_le_iff₀ hα₀).mpr (by simpa only [e, mul_comm] using hl)
  have hr' : ξL x * q x ^ 2 / αL ≤ ∫ y in Ioo x L, e y :=
    (div_le_iff₀ hαL).mpr (by simpa only [e, mul_comm] using hr)
  have hei : IntervalIntegrable e volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (hx.1.trans hx.2).le).mpr he
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hei.mono_set (uIcc_subset_uIcc_left (by simpa [uIcc_of_le (hx.1.trans hx.2).le] using
      (show x ∈ Icc 0 L from ⟨hx.1.le, hx.2.le⟩))))
    (hei.mono_set (uIcc_subset_uIcc_right (by simpa [uIcc_of_le (hx.1.trans hx.2).le] using
      (show x ∈ Icc 0 L from ⟨hx.1.le, hx.2.le⟩))))
  simp only [intervalIntegral.integral_of_le hx.1.le,
    intervalIntegral.integral_of_le hx.2.le,
    intervalIntegral.integral_of_le (hx.1.trans hx.2).le,
    integral_Ioc_eq_integral_Ioo] at hsplit
  calc
    _ = ξ₀ x * q x ^ 2 / α₀ + ξL x * q x ^ 2 / αL := by ring
    _ ≤ _ := by rw [← hsplit]; exact add_le_add hl' hr'

/-- A vanishing left endpoint flux controls a point value by the full energy.
No flux condition is needed at the other endpoint. -/
theorem mul_sq_le_energy_left
    {q φ σ ξ : ℝ → ℝ} {L x α : ℝ}
    (hx : x ∈ Ioo 0 L) (hα : 0 < α)
    (hq : ∀ y ∈ Ioo 0 L, HasDerivAt q (deriv q y) y)
    (hξ : ∀ y ∈ Ioo 0 L, HasDerivAt ξ (deriv ξ y) y)
    (hφ : ∀ y ∈ Ioo 0 L, 0 ≤ φ y)
    (hσ : ∀ y ∈ Ioo 0 L, 0 < σ y)
    (hleft : ∀ y ∈ Ioo 0 L, ξ y ^ 2 ≤ α * σ y * (α * φ y - deriv ξ y))
    (hflux : Tendsto (fun y ↦ ξ y * q y ^ 2) (𝓝[>] 0) (𝓝 0))
    (he : IntegrableOn (fun y ↦ q y ^ 2 * φ y + deriv q y ^ 2 * σ y) (Ioo 0 L)) :
    ξ x * q x ^ 2 ≤ α * ∫ y in Ioo 0 L, q y ^ 2 * φ y + deriv q y ^ 2 * σ y := by
  have h := mixed_sq_le_energy (ξL := fun _ ↦ 0) (αL := 1)
    hx hα zero_lt_one hq hξ (fun y _ ↦ by simpa using hasDerivAt_const y (0 : ℝ))
    hσ hleft
    (fun y hy ↦ by simpa using mul_nonneg (hσ y hy).le (hφ y hy))
    hflux (by simp) he
  simp only [zero_div, add_zero, div_mul_eq_mul_div] at h
  exact (div_le_iff₀ hα).mp h |>.trans_eq (mul_comm _ _)

/-- The reflected multiplier estimate uses only the flux at the right endpoint.
Positivity of the energy density allows the bound to use the full interval. -/
theorem mul_sq_le_energy_right
    {q φ σ ξ : ℝ → ℝ} {L x α : ℝ}
    (hx : x ∈ Ioo 0 L) (hα : 0 < α)
    (hq : ∀ y ∈ Ioo 0 L, HasDerivAt q (deriv q y) y)
    (hξ : ∀ y ∈ Ioo 0 L, HasDerivAt ξ (deriv ξ y) y)
    (hφ : ∀ y ∈ Ioo 0 L, 0 ≤ φ y)
    (hσ : ∀ y ∈ Ioo 0 L, 0 < σ y)
    (hright : ∀ y ∈ Ioo 0 L, ξ y ^ 2 ≤ α * σ y * (α * φ y + deriv ξ y))
    (hflux : Tendsto (fun y ↦ ξ y * q y ^ 2) (𝓝[<] L) (𝓝 0))
    (he : IntegrableOn (fun y ↦ q y ^ 2 * φ y + deriv q y ^ 2 * σ y) (Ioo 0 L)) :
    ξ x * q x ^ 2 ≤ α * ∫ y in Ioo 0 L, q y ^ 2 * φ y + deriv q y ^ 2 * σ y := by
  have h := mixed_sq_le_energy (ξ₀ := fun _ ↦ 0) (α₀ := 1)
    hx zero_lt_one hα hq (fun y _ ↦ by simpa using hasDerivAt_const y (0 : ℝ)) hξ
    hσ (fun y hy ↦ by simpa using mul_nonneg (hσ y hy).le (hφ y hy)) hright
    (by simp) hflux he
  simp only [zero_div, zero_add, div_mul_eq_mul_div] at h
  exact (div_le_iff₀ hα).mp h |>.trans_eq (mul_comm _ _)

end SobolevSpace.WeightedEndpoint
