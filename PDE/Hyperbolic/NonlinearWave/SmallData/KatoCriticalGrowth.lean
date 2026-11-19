/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.KatoLogarithm
import CAS.ExactTactic

/-!
# Growth forced by the critical mass weight

At `q=p+1`, positive linear mass growth gives `P' ≥ C δ^p/(R+t)`.
Consequently the velocity has a logarithmic lower bound and the mass
divided by `R+t` tends to infinity. These conclusions are derived from the
second-order inequality; they are not additional growth hypotheses.
-/

@[expose] public noncomputable section

open Filter Set

namespace WaveEquation.SmallData.Kato

/-- Substitute linear mass growth into the critical weighted forcing. -/
theorem reciprocal_acceleration_lower_bound {C δ r f p v : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (hr : 0 < r)
    (hp : 0 ≤ p) (hlinear : δ * r ≤ f) (hineq : C * r ^ (-(p + 1)) * f ^ p ≤ v) :
    C * δ ^ p / r ≤ v := by
  have hpow := Real.rpow_le_rpow (mul_nonneg hδ hr.le) hlinear hp
  calc
    C * δ ^ p / r = C * r ^ (-(p + 1)) * (δ * r) ^ p := by
      rw [Real.mul_rpow hδ hr.le]
      have he : r ^ (-(p + 1)) * r ^ p = r⁻¹ := by
        rw [← Real.rpow_add hr, show -(p + 1) + p = -1 by cas, Real.rpow_neg_one]
      calc
        C * δ ^ p / r = C * δ ^ p * (r ^ (-(p + 1)) * r ^ p) := by
          rw [he, div_eq_mul_inv]
        _ = C * r ^ (-(p + 1)) * (δ ^ p * r ^ p) := by ring
    _ ≤ C * r ^ (-(p + 1)) * f ^ p :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hC (Real.rpow_nonneg hr.le _))
    _ ≤ v := hineq

/-- The critical forcing yields an explicit logarithmic lower bound for the velocity. -/
theorem critical_logarithmic_velocity_lower_bound {F P : ℝ → ℝ} {C R p δ a t : ℝ} (hC : 0 ≤ C)
    (hp : 0 ≤ p) (hδ : 0 ≤ δ) (hRa : 0 < R + a) (hat : a ≤ t)
    (hP : ∀ s ∈ Icc a t, DifferentiableAt ℝ P s) (hlinear : ∀ s ∈ Icc a t, δ * (R + s) ≤ F s)
    (hineq : ∀ s ∈ Icc a t, C * (R + s) ^ (-(p + 1)) * F s ^ p ≤ deriv P s) :
    P a + C * δ ^ p * (Real.log (R + t) - Real.log (R + a)) ≤ P t := by
  refine logarithmic_lower_bound hRa hat hP fun s hs ↦ ?_
  exact reciprocal_acceleration_lower_bound hC hδ (by linarith [hs.1]) hp
    (hlinear s hs) (hineq s hs)

/-- Critical forcing makes the velocity and the mass divided by time tend to infinity. -/
theorem critical_velocity_and_mass_ratio_tendsto_atTop {F P : ℝ → ℝ} {C R p δ a : ℝ} (hC : 0 < C)
    (hp : 0 ≤ p) (hδ : 0 < δ) (hRa : 0 < R + a) (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t)
    (hP : ∀ t, a ≤ t → DifferentiableAt ℝ P t) (hlinear : ∀ t, a ≤ t → δ * (R + t) ≤ F t)
    (hineq : ∀ t, a ≤ t → C * (R + t) ^ (-(p + 1)) * F t ^ p ≤ deriv P t) :
    Tendsto P atTop atTop ∧ Tendsto (fun t ↦ F t / (R + t)) atTop atTop := by
  have hD : 0 < C * δ ^ p := mul_pos hC (Real.rpow_pos_of_pos hδ p)
  have hlog : Tendsto
      (fun t : ℝ ↦ Real.log (R + t) - Real.log (R + a)) atTop atTop := by
    simpa only [sub_eq_add_neg, Function.comp_apply, id_eq] using
      tendsto_atTop_add_const_right atTop (-Real.log (R + a)) (Real.tendsto_log_atTop.comp
          (tendsto_atTop_add_const_left atTop R tendsto_id))
  have htop : Tendsto
      (fun t ↦ P a + C * δ ^ p * (Real.log (R + t) - Real.log (R + a))) atTop atTop :=
    tendsto_atTop_add_const_left atTop (P a) (hlog.const_mul_atTop hD)
  have hPtop : Tendsto P atTop atTop := by
    apply tendsto_atTop_mono' atTop _ htop
    filter_upwards [eventually_ge_atTop a] with t ht
    exact critical_logarithmic_velocity_lower_bound hC.le hp hδ.le hRa ht
      (fun s hs ↦ hP s hs.1) (fun s hs ↦ hlinear s hs.1) (fun s hs ↦ hineq s hs.1)
  exact ⟨hPtop, tendsto_div_affine_atTop_of_velocity hF hPtop⟩

end WaveEquation.SmallData.Kato
