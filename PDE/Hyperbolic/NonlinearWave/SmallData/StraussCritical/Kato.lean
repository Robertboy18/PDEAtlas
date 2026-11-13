/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.KatoPolynomial
public import PDE.Hyperbolic.NonlinearWave.SmallData.KatoLogarithm
import CAS.ExactTactic

/-!
# Critical polynomial Kato obstruction

At the balance `(p-1)*α = q-2`, a fixed polynomial seed is insufficient.
An unbounded normalized mass `F/(R+t)^α` does give a contradiction: the energy
estimate dominates the derivative of this quotient, and a negative power
cannot decrease by a positive multiple of reciprocal time forever.
The PDE application must derive the unbounded quotient.
-/

@[expose] public noncomputable section

open Filter Set

namespace WaveEquation.SmallData.Kato

/-- Normalizing at the critical polynomial exponent removes the time weight
from the scalar energy estimate. -/
theorem critical_polynomial_velocity_normalization {c r f v p q α : ℝ} (hr : 0 < r) (hf : 0 < f)
    (hbalance : q = α * (p - 1) + 2) (hvelocity : c * r ^ (-q / 2) * f ^ ((p + 1) / 2) ≤ v) :
    c * (f / r ^ α) ^ ((p + 1) / 2) ≤ v * r ^ (1 - α) := by
  have h := mul_le_mul_of_nonneg_right hvelocity (Real.rpow_nonneg hr.le (1 - α))
  convert h using 1
  rw [Real.div_rpow hf.le (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le,
    div_eq_mul_inv, ← Real.rpow_neg hr.le]
  calc
    c * (f ^ ((p + 1) / 2) * r ^ (-(α * ((p + 1) / 2)))) =
        c * f ^ ((p + 1) / 2) * r ^ (-q / 2 + (1 - α)) := by
      rw [show -(α * ((p + 1) / 2)) = -q / 2 + (1 - α) by rw [hbalance]; cas]
      ring
    _ = _ := by rw [Real.rpow_add hr]; ring

/-- At critical polynomial balance, an unbounded mass quotient rules out
an entire future half-line. This is a scalar ingredient, not a supplied PDE estimate. -/
theorem not_critical_polynomial_second_order_on_Ici {F P : ℝ → ℝ} {C R p q a α : ℝ} (hC : 0 < C)
    (hp : 1 < p) (hq : 0 ≤ q) (hα : 0 < α) (hbalance : q = α * (p - 1) + 2) (hRa : 0 < R + a)
    (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t) (hP : ∀ t, a ≤ t → DifferentiableAt ℝ P t)
    (hpos : ∀ t, a ≤ t → 0 < F t) (hPnonneg : ∀ t, a ≤ t → 0 ≤ P t)
    (hgrowth : Tendsto (fun t ↦ F t / (R + t) ^ α) atTop atTop)
    (hineq : ∀ t, a ≤ t → C * (R + t) ^ (-q) * F t ^ p ≤ deriv P t) :
    False := by
  let W := fun t ↦ F t / (R + t) ^ α
  let Z := fun t ↦ P t * (R + t) ^ (1 - α)
  let V := fun t ↦ (Z t - α * W t) / (R + t)
  let e := (p - 1) / 2
  let c := (C / (p + 1)) ^ (1 / 2 : ℝ)
  have he : 0 < e := by dsimp [e]; linarith
  have hA : 0 < C / (p + 1) := div_pos hC (by linarith)
  have hc : 0 < c := Real.rpow_pos_of_pos hA _
  have hWpos (t : ℝ) (ht : a ≤ t) : 0 < W t :=
    div_pos (hpos t ht) (Real.rpow_pos_of_pos (by linarith) _)
  have hW (t : ℝ) (ht : a ≤ t) : HasDerivAt W (V t) t := by
    have hRt : 0 < R + t := by linarith
    have hd : HasDerivAt (fun s : ℝ ↦ (R + s) ^ α)
        (α * (R + t) ^ (α - 1)) t := by
      cas using hRt
    have hdF := (hF t ht).fun_div hd (Real.rpow_pos_of_pos hRt α).ne'
    convert hdF using 1
    dsimp [V, Z, W]
    rw [Real.rpow_sub hRt, Real.rpow_one, Real.rpow_sub hRt, Real.rpow_one]
    field_simp
  have hFtop : Tendsto F atTop atTop := by
    have hmul := hgrowth.atTop_mul_atTop₀
      ((tendsto_rpow_atTop hα).comp (tendsto_atTop_add_const_left atTop R tendsto_id))
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop a] with t ht
    exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos (by linarith : 0 < R + t) α).ne'
  have hdouble := ((tendsto_rpow_atTop (by linarith : 0 < p + 1)).comp hFtop).eventually
    (eventually_ge_atTop (2 * F a ^ (p + 1)))
  have hlarge := ((tendsto_rpow_atTop he).comp hgrowth).eventually (eventually_ge_atTop (2 * α / c))
  obtain ⟨b, hb⟩ := eventually_atTop.mp (hdouble.and hlarge)
  apply not_log_velocity_lower_bound (F := W) (P := V) (R := R) (a := max a b)
    (c := c / 2) (div_pos hc (by norm_num)) he (by linarith [le_max_left a b])
    (fun t ht ↦ hW t ((le_max_left a b).trans ht)) (fun t ht ↦ hWpos t ((le_max_left a b).trans ht))
  intro t ht
  have hat : a ≤ t := (le_max_left a b).trans ht
  have hbt : b ≤ t := (le_max_right a b).trans ht
  have hRt : 0 < R + t := by linarith
  have henergy := energy_lower_bound_of_double hC.le hp hq hRa hat
    (fun s hs ↦ hF s hs.1) (fun s hs ↦ hP s hs.1)
    (fun s hs ↦ hpos s hs.1) (fun s hs ↦ hPnonneg s hs.1) (fun s hs ↦ hineq s hs.1) (hb t hbt).1
  have hvelocity := velocity_lower_bound hA.le hRt (hpos t hat) (hPnonneg t hat) henergy
  have hnormalized : c * W t ^ (1 + e) ≤ Z t := by
    rw [show 1 + e = (p + 1) / 2 by dsimp [e]; cas]
    exact critical_polynomial_velocity_normalization hRt (hpos t hat) hbalance hvelocity
  have hsmall : α * W t ≤ (c / 2) * W t ^ (1 + e) := by
    have hcprod : α ≤ (c / 2) * W t ^ e := by
      have hh := (div_le_iff₀ hc).mp (hb t hbt).2
      change 2 * α ≤ W t ^ e * c at hh
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hcprod (hWpos t hat).le
    rw [Real.rpow_add (hWpos t hat), Real.rpow_one]
    nlinarith
  have hvbound : (c / 2) * W t ^ (1 + e) ≤ Z t - α * W t := by nlinarith
  have hh := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hvbound hRt.le)
    (Real.rpow_nonneg (hWpos t hat).le (-1 - e))
  have hcancel : W t ^ (1 + e) * W t ^ (-1 - e) = 1 := by
    rw [← Real.rpow_add (hWpos t hat), show 1 + e + (-1 - e) = 0 by cas, Real.rpow_zero]
  change (c / 2) / (R + t) ≤ ((Z t - α * W t) / (R + t)) * W t ^ (-1 - e)
  convert hh using 1
  linear_combination -(c / 2 / (R + t)) * hcancel

end WaveEquation.SmallData.Kato
