/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CAS.ExactTactic

/-!
# Energy comparison for a weighted second-order differential inequality

Multiplying `P' ≥ C (R+t)^(-q) F^p` by the nonnegative velocity `P=F'` gives a
quantitative lower bound for `P²`. The weight is frozen at the right endpoint of each
compact interval. This requires `q ≥ 0` and positive `R+t` on the interval.
-/

@[expose] public noncomputable section

open Set

namespace WaveEquation.SmallData.Kato

/-- Integrating the scalar differential inequality against the velocity. -/
theorem energy_lower_bound {F P : ℝ → ℝ} {C R p q a t : ℝ} (hC : 0 ≤ C) (hp : 1 < p) (hq : 0 ≤ q)
    (hRa : 0 < R + a) (hat : a ≤ t) (hF : ∀ s ∈ Icc a t, HasDerivAt F (P s) s)
    (hP : ∀ s ∈ Icc a t, DifferentiableAt ℝ P s) (hFpos : ∀ s ∈ Icc a t, 0 < F s)
    (hPnonneg : ∀ s ∈ Icc a t, 0 ≤ P s)
    (hineq : ∀ s ∈ Icc a t, C * (R + s) ^ (-q) * F s ^ p ≤ deriv P s) :
    P a ^ 2 + (2 * C / (p + 1)) * (R + t) ^ (-q) * (F t ^ (p + 1) - F a ^ (p + 1)) ≤ P t ^ 2 := by
  let A := (2 * C / (p + 1)) * (R + t) ^ (-q)
  let E := fun s ↦ P s ^ 2 - A * F s ^ (p + 1)
  have hE (s : ℝ) (hs : s ∈ Icc a t) :
      HasDerivAt E (2 * P s * (deriv P s - C * (R + t) ^ (-q) * F s ^ p)) s := by
    have hd := ((hP s hs).hasDerivAt.pow 2).sub
      (((hF s hs).rpow_const (p := p + 1) (Or.inl (hFpos s hs).ne')).const_mul A)
    convert hd using 1
    simp only [Nat.cast_ofNat, add_sub_cancel_right]
    dsimp [A]
    have hp1 : p + 1 ≠ 0 := by linarith
    field_simp
  have hmono : MonotoneOn E (Icc a t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a t)
      (fun s hs ↦ (hE s hs).continuousAt.continuousWithinAt)
    · intro s hs
      rw [interior_Icc] at hs
      exact (hE s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hsI := Ioo_subset_Icc_self hs
      rw [(hE s hsI).deriv]
      have hweight : (R + t) ^ (-q) ≤ (R + s) ^ (-q) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [hs.1])
          (by linarith [hs.2]) (neg_nonpos.mpr hq)
      have hbound : C * (R + t) ^ (-q) * F s ^ p ≤ deriv P s :=
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hweight hC)
          (Real.rpow_nonneg (hFpos s hsI).le p)).trans (hineq s hsI)
      exact mul_nonneg (mul_nonneg (by norm_num) (hPnonneg s hsI)) (sub_nonneg.mpr hbound)
  have h := hmono (left_mem_Icc.mpr hat) (right_mem_Icc.mpr hat) hat
  dsimp [E, A] at h
  nlinarith

/-- Once the mass power doubles, the energy bound controls the full current mass power. -/
theorem energy_lower_bound_of_double {F P : ℝ → ℝ} {C R p q a t : ℝ} (hC : 0 ≤ C) (hp : 1 < p)
    (hq : 0 ≤ q) (hRa : 0 < R + a) (hat : a ≤ t) (hF : ∀ s ∈ Icc a t, HasDerivAt F (P s) s)
    (hP : ∀ s ∈ Icc a t, DifferentiableAt ℝ P s) (hFpos : ∀ s ∈ Icc a t, 0 < F s)
    (hPnonneg : ∀ s ∈ Icc a t, 0 ≤ P s)
    (hineq : ∀ s ∈ Icc a t, C * (R + s) ^ (-q) * F s ^ p ≤ deriv P s)
    (hdouble : 2 * F a ^ (p + 1) ≤ F t ^ (p + 1)) :
    (C / (p + 1)) * (R + t) ^ (-q) * F t ^ (p + 1) ≤ P t ^ 2 := by
  have h := energy_lower_bound hC hp hq hRa hat hF hP hFpos hPnonneg hineq
  have hc : 0 ≤ C / (p + 1) * (R + t) ^ (-q) :=
    mul_nonneg (div_nonneg hC (by linarith))
      (Real.rpow_nonneg (by linarith) _)
  have ha : 2 * C / (p + 1) = 2 * (C / (p + 1)) := by cas
  rw [ha] at h
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hdouble), sq_nonneg (P a)]

end WaveEquation.SmallData.Kato
