/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import CAS.ExactTactic

/-!
# Logarithmic growth and obstruction on a half-line

A reciprocal-time lower bound for a derivative integrates to logarithmic
growth. An unbounded velocity forces the trajectory divided by time to become
unbounded. Conversely, a positive reciprocal-time lower bound for the derivative
of a negative trajectory power is incompatible with a whole future half-line.
-/

@[expose] public noncomputable section

open Filter Set

namespace WaveEquation.SmallData.Kato

/-- Integrate a reciprocal-time derivative bound from the left endpoint. -/
theorem logarithmic_lower_bound {P : ℝ → ℝ} {D R a t : ℝ} (hRa : 0 < R + a) (hat : a ≤ t)
    (hP : ∀ s ∈ Icc a t, DifferentiableAt ℝ P s) (hineq : ∀ s ∈ Icc a t, D / (R + s) ≤ deriv P s) :
    P a + D * (Real.log (R + t) - Real.log (R + a)) ≤ P t := by
  let G := fun s ↦ P s - D * Real.log (R + s)
  have hG (s : ℝ) (hs : s ∈ Icc a t) :
      HasDerivAt G (deriv P s - D / (R + s)) s := by
    have hRs : 0 < R + s := by linarith [hs.1]
    have hd : HasDerivAt (fun r : ℝ ↦ Real.log (R + r)) (1 / (R + s)) s := by
      cas using hRs
    simpa only [mul_one_div] using (hP s hs).hasDerivAt.fun_sub (hd.const_mul D)
  have hmono : MonotoneOn G (Icc a t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a t)
      (fun s hs ↦ (hG s hs).continuousAt.continuousWithinAt)
    · exact fun s hs ↦ (hG s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hG s (interior_subset hs)).deriv]
      exact sub_nonneg.mpr (hineq s (interior_subset hs))
  have h := hmono (left_mem_Icc.mpr hat) (right_mem_Icc.mpr hat) hat
  dsimp [G] at h
  linarith

/-- If the velocity tends to infinity, so does the trajectory divided by
an affine time coordinate. No sign assumption on the trajectory is required. -/
theorem tendsto_div_affine_atTop_of_velocity {F P : ℝ → ℝ} {R a : ℝ}
    (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t) (hP : Tendsto P atTop atTop) :
    Tendsto (fun t ↦ F t / (R + t)) atTop atTop := by
  refine tendsto_atTop.2 fun M ↦ ?_
  obtain ⟨b, hb⟩ := eventually_atTop.mp (hP.eventually (eventually_ge_atTop (M + 1)))
  let d := max a b
  let G := fun t ↦ F t - (M + 1) * t
  have hG (t : ℝ) (ht : d ≤ t) :
      HasDerivAt G (P t - (M + 1)) t := by
    simpa only [mul_one, id_eq] using
      (hF t ((le_max_left a b).trans ht)).fun_sub ((hasDerivAt_id t).const_mul (M + 1))
  have hmono : MonotoneOn G (Ici d) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici d)
      (fun t ht ↦ (hG t ht).continuousAt.continuousWithinAt)
    · intro t ht
      rw [interior_Ici] at ht
      exact (hG t ht.le).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hG t ht.le).deriv]
      exact sub_nonneg.mpr (hb t ((le_max_right a b).trans ht.le))
  filter_upwards [eventually_ge_atTop d, eventually_ge_atTop (-R + 1),
    eventually_ge_atTop (M * R - F d + (M + 1) * d)] with t htd htr hlarge
  have hbound := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr htd) htd
  have hRt : 0 < R + t := by linarith
  apply (le_div_iff₀ hRt).2
  dsimp [G] at hbound
  nlinarith

/-- The logarithmic version of the negative-power obstruction: the lower
time weight is exactly reciprocal time, including its divergent endpoint. -/
theorem not_log_velocity_lower_bound {F P : ℝ → ℝ} {R a c e : ℝ} (hc : 0 < c) (he : 0 < e)
    (hRa : 0 < R + a) (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t) (hpos : ∀ t, a ≤ t → 0 < F t)
    (hlower : ∀ t, a ≤ t → c / (R + t) ≤ P t * F t ^ (-1 - e)) :
    False := by
  let G := fun t ↦ F t ^ (-e) + e * c * Real.log (R + t)
  have hG (t : ℝ) (ht : a ≤ t) :
      HasDerivAt G (e * (c / (R + t) - P t * F t ^ (-1 - e))) t := by
    have hRt : 0 < R + t := by linarith
    have hd : HasDerivAt (fun s : ℝ ↦ Real.log (R + s)) (1 / (R + t)) t := by
      cas using hRt
    have h := ((hF t ht).rpow_const (p := -e) (Or.inl (hpos t ht).ne')).add (hd.const_mul (e * c))
    convert h using 1
    rw [show -e - 1 = -1 - e by cas]
    ring
  have hanti : AntitoneOn G (Ici a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici a)
      (fun t ht ↦ (hG t ht).continuousAt.continuousWithinAt)
    · intro t ht
      rw [interior_Ici] at ht
      exact (hG t ht.le).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hG t ht.le).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos he.le (sub_nonpos.mpr (hlower t ht.le))
  have htend : Tendsto (fun t : ℝ ↦ e * c * Real.log (R + t)) atTop atTop :=
    (Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_left atTop R tendsto_id)).const_mul_atTop (mul_pos he hc)
  obtain ⟨t, hta, htG⟩ :=
    ((eventually_ge_atTop a).and (htend.eventually (eventually_gt_atTop (G a)))).exists
  have hbound := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hta) hta
  have hnonneg := Real.rpow_nonneg (hpos t hta).le (-e)
  dsimp [G] at hbound htG
  linarith

end WaveEquation.SmallData.Kato
