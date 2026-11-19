/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.KatoCriticalGrowth
public import PDE.Hyperbolic.NonlinearWave.SmallData.Kato
import CAS.ExactTactic

/-!
# The critical linear-growth Kato contradiction

The endpoint `q=p+1` also rules out positive linearly growing global trajectories.
Critical forcing first makes `W=F/(R+t)` tend to infinity. The scalar energy
estimate then gives `P ≥ c W^((p+1)/2)`. Once `W` is large, its derivative
dominates a positive multiple of `W^((p+1)/2)/(R+t)`, contradicting the logarithmic
negative-power obstruction.
-/

@[expose] public noncomputable section

open Filter Set

namespace WaveEquation.SmallData.Kato

/-- The critical weight is incompatible with global positive linear mass growth. -/
theorem not_critical_second_order_on_Ici {F P : ℝ → ℝ} {C R p δ a : ℝ} (hC : 0 < C) (hp : 1 < p)
    (hδ : 0 < δ) (hRa : 0 < R + a) (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t)
    (hP : ∀ t, a ≤ t → DifferentiableAt ℝ P t) (hPnonneg : ∀ t, a ≤ t → 0 ≤ P t)
    (hlinear : ∀ t, a ≤ t → δ * (R + t) ≤ F t)
    (hineq : ∀ t, a ≤ t → C * (R + t) ^ (-(p + 1)) * F t ^ p ≤ deriv P t) :
    False := by
  let W := fun t ↦ F t / (R + t)
  let V := fun t ↦ (P t - W t) / (R + t)
  let e := (p - 1) / 2
  let c := (C / (p + 1)) ^ (1 / 2 : ℝ)
  have he : 0 < e := by dsimp [e]; linarith
  have hA : 0 < C / (p + 1) := div_pos hC (by linarith)
  have hc : 0 < c := Real.rpow_pos_of_pos hA _
  have hpos (t : ℝ) (ht : a ≤ t) : 0 < F t :=
    (mul_pos hδ (by linarith)).trans_le (hlinear t ht)
  have hWpos (t : ℝ) (ht : a ≤ t) : 0 < W t :=
    div_pos (hpos t ht) (by linarith)
  have hW (t : ℝ) (ht : a ≤ t) : HasDerivAt W (V t) t := by
    have hRt : R + t ≠ 0 := ne_of_gt (by linarith : 0 < R + t)
    have hd : HasDerivAt W ((P t * (R + t) - F t) / (R + t) ^ 2) t := by
      simpa only [id_eq, mul_one] using (hF t ht).fun_div ((hasDerivAt_id t).const_add R) hRt
    convert hd using 1
    change (P t - F t / (R + t)) / (R + t) = _
    field_simp
  have hWtop : Tendsto W atTop atTop :=
    (critical_velocity_and_mass_ratio_tendsto_atTop hC (by linarith) hδ hRa hF hP hlinear hineq).2
  have hFtop : Tendsto F atTop atTop := by
    apply tendsto_atTop_mono' atTop ((eventually_ge_atTop a).mono (fun t ht ↦ hlinear t ht))
    exact (tendsto_atTop_add_const_left atTop R tendsto_id).const_mul_atTop hδ
  have hdouble := ((tendsto_rpow_atTop (by linarith : 0 < p + 1)).comp hFtop).eventually
    (eventually_ge_atTop (2 * F a ^ (p + 1)))
  have hlarge := ((tendsto_rpow_atTop he).comp hWtop).eventually (eventually_ge_atTop (2 / c))
  obtain ⟨b, hb⟩ := eventually_atTop.mp (hdouble.and hlarge)
  apply not_log_velocity_lower_bound (F := W) (P := V) (R := R) (a := max a b)
    (c := c / 2) (div_pos hc (by norm_num)) he (by linarith [le_max_left a b])
    (fun t ht ↦ hW t ((le_max_left a b).trans ht)) (fun t ht ↦ hWpos t ((le_max_left a b).trans ht))
  intro t ht
  have hat : a ≤ t := (le_max_left a b).trans ht
  have hbt : b ≤ t := (le_max_right a b).trans ht
  have hRt : 0 < R + t := by linarith
  have henergy := energy_lower_bound_of_double hC.le hp (by linarith : 0 ≤ p + 1)
    hRa hat (fun s hs ↦ hF s hs.1) (fun s hs ↦ hP s hs.1)
    (fun s hs ↦ hpos s hs.1) (fun s hs ↦ hPnonneg s hs.1) (fun s hs ↦ hineq s hs.1) (hb t hbt).1
  have hvelocity := velocity_lower_bound hA.le hRt (hpos t hat) (hPnonneg t hat) henergy
  have hnormalized : c * W t ^ (1 + e) ≤ P t := by
    have hexp : 1 + e = (p + 1) / 2 := by dsimp [e]; cas
    change c * W t ^ (1 + e) ≤ _
    rw [hexp]
    change c * (F t / (R + t)) ^ ((p + 1) / 2) ≤ _
    rw [Real.div_rpow (hpos t hat).le hRt.le]
    convert hvelocity using 1
    rw [show -(p + 1) / 2 = -((p + 1) / 2) by cas, Real.rpow_neg hRt.le]
    ring
  have hsmall : W t ≤ (c / 2) * W t ^ (1 + e) := by
    have hcprod : 1 ≤ (c / 2) * W t ^ e := by
      have hh := (div_le_iff₀ hc).mp (hb t hbt).2
      change 2 ≤ W t ^ e * c at hh
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hcprod (hWpos t hat).le
    rw [Real.rpow_add (hWpos t hat), Real.rpow_one]
    nlinarith
  have hvbound : (c / 2) * W t ^ (1 + e) ≤ P t - W t := by
    nlinarith
  have hneg : 0 ≤ W t ^ (-1 - e) := Real.rpow_nonneg (hWpos t hat).le _
  have hh := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hvbound hRt.le) hneg
  have hcancel : W t ^ (1 + e) * W t ^ (-1 - e) = 1 := by
    rw [← Real.rpow_add (hWpos t hat), show 1 + e + (-1 - e) = 0 by cas, Real.rpow_zero]
  change (c / 2) / (R + t) ≤ ((P t - W t) / (R + t)) * W t ^ (-1 - e)
  convert hh using 1
  linear_combination -(c / 2 / (R + t)) * hcancel

/-- The strict and critical linear-growth arguments cover every `q ≤ p+1`. -/
theorem not_weighted_second_order_on_Ici_of_le {F P : ℝ → ℝ} {C R p q δ a : ℝ} (hC : 0 < C)
    (hp : 1 < p) (hq : 0 ≤ q) (hcrit : q ≤ p + 1) (hδ : 0 < δ) (hRa : 0 < R + a)
    (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t) (hP : ∀ t, a ≤ t → DifferentiableAt ℝ P t)
    (hPnonneg : ∀ t, a ≤ t → 0 ≤ P t) (hlinear : ∀ t, a ≤ t → δ * (R + t) ≤ F t)
    (hineq : ∀ t, a ≤ t → C * (R + t) ^ (-q) * F t ^ p ≤ deriv P t) :
    False := by
  rcases lt_or_eq_of_le hcrit with hlt | rfl
  · exact not_weighted_second_order_on_Ici hC hp hq hlt hδ hRa hF hP hPnonneg hlinear hineq
  · exact not_critical_second_order_on_Ici hC hp hδ hRa hF hP hPnonneg hlinear hineq

end WaveEquation.SmallData.Kato
