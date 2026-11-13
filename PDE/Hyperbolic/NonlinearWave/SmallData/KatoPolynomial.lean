/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Kato
import CAS.ExactTactic

/-!
# Kato's contradiction from polynomial mass growth

For `F ≥ δ (R+t)^α`, the strict condition is `(p-1)*α > q-2`.
The proof reuses the scalar energy and negative-power estimates. This is a
conditional scalar ingredient: applying it to the Strauss range still requires
deriving the stronger exponent `α` from the wave equation and initial data.
-/

@[expose] public noncomputable section

open Filter Set

namespace WaveEquation.SmallData.Kato

/-- Polynomial growth transfers a positive mass power into the time weight. -/
theorem polynomial_power_velocity_lower_bound {c r f v δ p q e α : ℝ} (hc : 0 ≤ c) (hr : 0 < r)
    (hδ : 0 ≤ δ) (hf : 0 < f) (he : e ≤ (p - 1) / 2) (hgrowth : δ * r ^ α ≤ f)
    (hvelocity : c * r ^ (-q / 2) * f ^ ((p + 1) / 2) ≤ v) :
    c * δ ^ ((p - 1) / 2 - e) * r ^ (-q / 2 + α * ((p - 1) / 2 - e)) ≤ v * f ^ (-1 - e) := by
  let z := (p - 1) / 2 - e
  have hz : 0 ≤ z := sub_nonneg.mpr he
  have hpow : (δ * r ^ α) ^ z ≤ f ^ z :=
    Real.rpow_le_rpow (mul_nonneg hδ (Real.rpow_nonneg hr.le _)) hgrowth hz
  calc
    c * δ ^ ((p - 1) / 2 - e) * r ^ (-q / 2 + α * ((p - 1) / 2 - e)) =
        c * r ^ (-q / 2) * (δ * r ^ α) ^ z := by
      rw [Real.mul_rpow hδ (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le, Real.rpow_add hr]
      ring
    _ ≤ c * r ^ (-q / 2) * f ^ z :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hc (Real.rpow_nonneg hr.le _))
    _ = (c * r ^ (-q / 2) * f ^ ((p + 1) / 2)) * f ^ (-1 - e) := by
      rw [mul_assoc (c * r ^ (-q / 2)), ← Real.rpow_add hf]
      congr 1
      congr 1
      dsimp [z]
      cas
    _ ≤ v * f ^ (-1 - e) := mul_le_mul_of_nonneg_right hvelocity (Real.rpow_nonneg hf.le _)

/-- The case of `not_polynomial_second_order_on_Ici` with `0 ≤ q`, `0 < R + a` and `P`
differentiable and nonnegative from `a` on. -/
private theorem not_polynomial_second_order_on_Ici_of_nonneg {F P : ℝ → ℝ} {C R p q δ a α : ℝ}
    (hC : 0 < C)
    (hp : 1 < p) (hq : 0 ≤ q) (hα : 0 < α) (hcrit : q - 2 < (p - 1) * α) (hδ : 0 < δ)
    (hRa : 0 < R + a) (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t)
    (hP : ∀ t, a ≤ t → DifferentiableAt ℝ P t) (hPnonneg : ∀ t, a ≤ t → 0 ≤ P t)
    (hgrowth : ∀ t, a ≤ t → δ * (R + t) ^ α ≤ F t)
    (hineq : ∀ t, a ≤ t → C * (R + t) ^ (-q) * F t ^ p ≤ deriv P t) :
    False := by
  have hpos (t : ℝ) (ht : a ≤ t) : 0 < F t :=
    (mul_pos hδ (Real.rpow_pos_of_pos (by linarith : 0 < R + t) _)).trans_le (hgrowth t ht)
  have hFtop : Tendsto F atTop atTop := by
    apply tendsto_atTop_mono' atTop ((eventually_ge_atTop a).mono (fun t ht ↦ hgrowth t ht))
    exact ((tendsto_rpow_atTop hα).comp
      (tendsto_atTop_add_const_left atTop R tendsto_id)).const_mul_atTop hδ
  have hdouble := ((tendsto_rpow_atTop (by linarith : 0 < p + 1)).comp hFtop).eventually
    (eventually_ge_atTop (2 * F a ^ (p + 1)))
  obtain ⟨b, hb⟩ := eventually_atTop.mp hdouble
  have hgap : 0 < (α * (p - 1) - q + 2) / (2 * α) :=
    div_pos (by nlinarith) (mul_pos (by norm_num) hα)
  obtain ⟨e, he, hemin⟩ := exists_between
    (lt_min (by linarith : 0 < (p - 1) / 2) hgap)
  have hep : e < (p - 1) / 2 := hemin.trans_le (min_le_left _ _)
  have heq : e < (α * (p - 1) - q + 2) / (2 * α) := hemin.trans_le (min_le_right _ _)
  let c := (C / (p + 1)) ^ (1 / 2 : ℝ)
  have hA : 0 < C / (p + 1) := div_pos hC (by linarith)
  have hc : 0 < c := Real.rpow_pos_of_pos hA _
  let k := 1 - q / 2 + α * ((p - 1) / 2 - e)
  have hk : 0 < k := by
    have h := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hα)).mp heq
    dsimp [k]
    nlinarith
  apply not_power_velocity_lower_bound (F := F) (P := P) (R := R) (a := max a b)
    (c := c * δ ^ ((p - 1) / 2 - e)) (mul_pos hc (Real.rpow_pos_of_pos hδ _)) he hk
    (by linarith [le_max_left a b]) (fun t ht ↦ hF t ((le_max_left a b).trans ht))
    (fun t ht ↦ hpos t ((le_max_left a b).trans ht))
  intro t ht
  have hat : a ≤ t := (le_max_left a b).trans ht
  have hbt : b ≤ t := (le_max_right a b).trans ht
  have hRt : 0 < R + t := by linarith
  have henergy := energy_lower_bound_of_double hC.le hp hq hRa hat
    (fun s hs ↦ hF s hs.1) (fun s hs ↦ hP s hs.1)
    (fun s hs ↦ hpos s hs.1) (fun s hs ↦ hPnonneg s hs.1) (fun s hs ↦ hineq s hs.1) (hb t hbt)
  have hvelocity := velocity_lower_bound hA.le hRt (hpos t hat) (hPnonneg t hat) henergy
  have hpower := polynomial_power_velocity_lower_bound hc.le hRt hδ.le (hpos t hat)
    hep.le (hgrowth t hat) hvelocity
  convert hpower using 1
  congr 2
  dsimp [k]
  cas

/-- A weighted second-order inequality cannot persist with the stated polynomial growth
when `(p-1)*α > q-2`. The growth hypothesis must be proved in any PDE application. Starting
late enough gives `R + t ≥ 1`, which lets a negative `q` be replaced by `0`; the inequality
makes `P'` positive, so `P` is differentiable and increasing there, and it becomes positive
because `F` is unbounded. -/
theorem not_polynomial_second_order_on_Ici {F P : ℝ → ℝ} {C R p q δ a α : ℝ} (hC : 0 < C)
    (hp : 1 < p) (hα : 0 < α) (hcrit : q - 2 < (p - 1) * α) (hδ : 0 < δ)
    (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t)
    (hgrowth : ∀ t, a ≤ t → δ * (R + t) ^ α ≤ F t)
    (hineq : ∀ t, a ≤ t → C * (R + t) ^ (-q) * F t ^ p ≤ deriv P t) :
    False := by
  set a₁ := max a (1 - R)
  have ha₁ : a ≤ a₁ := le_max_left _ _
  have hR₁ (t : ℝ) (ht : a₁ ≤ t) : 1 ≤ R + t := by linarith [le_max_right a (1 - R)]
  have hpos (t : ℝ) (ht : a₁ ≤ t) : 0 < F t :=
    (mul_pos hδ (Real.rpow_pos_of_pos (by linarith [hR₁ t ht]) _)).trans_le
      (hgrowth t (ha₁.trans ht))
  have hineq' (t : ℝ) (ht : a₁ ≤ t) : C * (R + t) ^ (-max q 0) * F t ^ p ≤ deriv P t :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (hR₁ t ht) (neg_le_neg (le_max_left q 0))) hC.le)
      (Real.rpow_pos_of_pos (hpos t ht) p).le) (hineq t (ha₁.trans ht))
  have hdpos (t : ℝ) (ht : a₁ ≤ t) : 0 < deriv P t :=
    lt_of_lt_of_le (mul_pos (mul_pos hC (Real.rpow_pos_of_pos (by linarith [hR₁ t ht]) _))
      (Real.rpow_pos_of_pos (hpos t ht) p)) (hineq' t ht)
  have hP (t : ℝ) (ht : a₁ ≤ t) : DifferentiableAt ℝ P t := by
    by_contra hnd
    exact (hdpos t ht).ne' (deriv_zero_of_not_differentiableAt hnd)
  have hmono : MonotoneOn P (Ici a₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici a₁)
      (fun t ht ↦ (hP t ht).continuousAt.continuousWithinAt) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    · rw [interior_Ici] at ht
      exact (hP t (le_of_lt ht)).differentiableWithinAt
    · rw [interior_Ici] at ht
      exact (hdpos t (le_of_lt ht)).le
  obtain ⟨t₀, ht₀, hP₀⟩ : ∃ t₀, a₁ ≤ t₀ ∧ 0 < P t₀ := by
    by_contra hnone
    simp only [not_exists, not_and, not_lt] at hnone
    have hanti : AntitoneOn F (Ici a₁) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici a₁)
        (fun t ht ↦ (hF t (ha₁.trans ht)).continuousAt.continuousWithinAt) (fun t ht ↦ ?_)
        (fun t ht ↦ ?_)
      · rw [interior_Ici] at ht
        exact (hF t (ha₁.trans (le_of_lt ht))).differentiableAt.differentiableWithinAt
      · rw [interior_Ici] at ht
        rw [(hF t (ha₁.trans (le_of_lt ht))).deriv]
        exact hnone t (le_of_lt ht)
    have hFtop : Tendsto F atTop atTop := by
      apply tendsto_atTop_mono' atTop ((eventually_ge_atTop a).mono (fun t ht ↦ hgrowth t ht))
      exact ((tendsto_rpow_atTop hα).comp
        (tendsto_atTop_add_const_left atTop R tendsto_id)).const_mul_atTop hδ
    obtain ⟨t, hFt, ht⟩ := ((hFtop.eventually (eventually_gt_atTop (F a₁))).and
      (eventually_ge_atTop a₁)).exists
    exact (hanti le_rfl ht ht).not_gt hFt
  have hq' : max q 0 - 2 < (p - 1) * α := by
    have : 0 < (p - 1) * α := mul_pos (by linarith) hα
    rcases le_total q 0 with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h]
      exact hcrit
  exact not_polynomial_second_order_on_Ici_of_nonneg hC hp (le_max_right q 0) hα hq' hδ
    (by linarith [hR₁ t₀ ht₀]) (fun t ht ↦ hF t (ha₁.trans (ht₀.trans ht)))
    (fun t ht ↦ hP t (ht₀.trans ht))
    (fun t ht ↦ hP₀.le.trans (hmono ht₀ (ht₀.trans ht) ht))
    (fun t ht ↦ hgrowth t (ha₁.trans (ht₀.trans ht)))
    (fun t ht ↦ hineq' t (ht₀.trans ht))

end WaveEquation.SmallData.Kato
