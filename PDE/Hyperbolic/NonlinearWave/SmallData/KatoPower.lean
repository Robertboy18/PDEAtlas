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
# A negative-power obstruction on a future half-line

For a positive trajectory, a lower bound on `F' F^(-1-e)` with `e > 0` makes
`F^(-e)` decrease. Adding the explicit time primitive yields an antitone function
with a lower bound tending to infinity, which is impossible.
-/

@[expose] public noncomputable section

open Filter Set

namespace WaveEquation.SmallData.Kato

/-- A nonintegrable positive lower bound for the derivative of a negative mass power
cannot hold on an entire future half-line. -/
theorem not_power_velocity_lower_bound {F P : ℝ → ℝ} {R a c e k : ℝ} (hc : 0 < c) (he : 0 < e)
    (hk : 0 < k) (hRa : 0 < R + a) (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t)
    (hpos : ∀ t, a ≤ t → 0 < F t)
    (hlower : ∀ t, a ≤ t → c * (R + t) ^ (k - 1) ≤ P t * F t ^ (-1 - e)) :
    False := by
  let d := e * c / k
  have hdpos : 0 < d := div_pos (mul_pos he hc) hk
  let G := fun t ↦ F t ^ (-e) + d * (R + t) ^ k
  have hG (t : ℝ) (ht : a ≤ t) : HasDerivAt G
        (e * (c * (R + t) ^ (k - 1) - P t * F t ^ (-1 - e))) t := by
    have hRt : 0 < R + t := by linarith
    have htime : HasDerivAt (fun s : ℝ ↦ (R + s) ^ k)
        (k * (R + t) ^ (k - 1)) t := by
      cas using hRt
    have h := ((hF t ht).rpow_const (p := -e) (Or.inl (hpos t ht).ne')).add (htime.const_mul d)
    convert h using 1
    rw [show -e - 1 = -1 - e by cas]
    dsimp [d]
    have hk0 := hk.ne'
    field_simp
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
  have htend : Tendsto (fun t : ℝ ↦ d * (R + t) ^ k) atTop atTop := ((tendsto_rpow_atTop hk).comp
      (tendsto_atTop_add_const_left atTop R tendsto_id)).const_mul_atTop hdpos
  obtain ⟨t, hta, htG⟩ :=
    ((eventually_ge_atTop a).and (htend.eventually (eventually_gt_atTop (G a)))).exists
  have hbound := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hta) hta
  have hnonneg := Real.rpow_nonneg (hpos t hta).le (-e)
  dsimp [G] at hbound htG
  linarith

end WaveEquation.SmallData.Kato
