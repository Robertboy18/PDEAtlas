/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.KatoEnergy
public import PDE.Hyperbolic.NonlinearWave.SmallData.KatoPower
public import PDE.Hyperbolic.NonlinearWave.SmallData.KatoVelocity
import CAS.ExactTactic

/-!
# A weighted Kato contradiction from linear growth

Positive linear growth and the relations `F'=P`,
`P' ≥ C (R+t)^(-q) F^p` cannot persist on a future half-line when
`p > 1`, `q ≥ 0`, and `q < p+1`. The energy estimate is derived by multiplying
by the nonnegative velocity; a negative mass power then gives the contradiction.

For the wave mass weight `q=n*(p-1)`, this gives the strict elementary range
`(n-1)*(p-1)<2`. No critical John/Strauss assertion is made.

The argument is step 3 of the proof of Evans, §12.5.2, Theorem 2, for the mass `F = I`:
multiplying by `I' = P` gives a lower bound for `P²` as in (14), and a negative power of the
mass then contradicts the growth. Evans combines (10) with the growth (12) and needs
`0 < μ < 2` in (13); we use linear growth.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.2, proof of Theorem 2, steps 1 and 3, equations
  (10) and (12)-(14).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set

namespace WaveEquation.SmallData.Kato

/-- The weighted second-order inequality is incompatible with global linear mass growth
in the strict range `q < p+1`. All derivatives are derivatives of the trajectories. -/
theorem not_weighted_second_order_on_Ici {F P : ℝ → ℝ} {C R p q δ a : ℝ} (hC : 0 < C) (hp : 1 < p)
    (hq : 0 ≤ q) (hcrit : q < p + 1) (hδ : 0 < δ) (hRa : 0 < R + a)
    (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t) (hP : ∀ t, a ≤ t → DifferentiableAt ℝ P t)
    (hPnonneg : ∀ t, a ≤ t → 0 ≤ P t) (hlinear : ∀ t, a ≤ t → δ * (R + t) ≤ F t)
    (hineq : ∀ t, a ≤ t → C * (R + t) ^ (-q) * F t ^ p ≤ deriv P t) :
    False := by
  have hpos (t : ℝ) (ht : a ≤ t) : 0 < F t :=
    (mul_pos hδ (by linarith)).trans_le (hlinear t ht)
  have hFtop : Tendsto F atTop atTop := by
    apply tendsto_atTop_mono' atTop ((eventually_ge_atTop a).mono (fun t ht ↦ hlinear t ht))
    exact (tendsto_atTop_add_const_left atTop R tendsto_id).const_mul_atTop hδ
  have hdouble : ∀ᶠ t in atTop, 2 * F a ^ (p + 1) ≤ F t ^ (p + 1) :=
    ((tendsto_rpow_atTop (by linarith : 0 < p + 1)).comp hFtop).eventually (eventually_ge_atTop _)
  obtain ⟨b, hb⟩ := eventually_atTop.mp hdouble
  obtain ⟨e, he, hemin⟩ := exists_between
    (lt_min (by linarith : 0 < (p - 1) / 2) (by linarith : 0 < (p + 1 - q) / 2))
  have hep : e < (p - 1) / 2 := hemin.trans_le (min_le_left _ _)
  have heq : e < (p + 1 - q) / 2 := hemin.trans_le (min_le_right _ _)
  let c := (C / (p + 1)) ^ (1 / 2 : ℝ)
  have hA : 0 < C / (p + 1) := div_pos hC (by linarith)
  have hc : 0 < c := Real.rpow_pos_of_pos hA _
  let k := (p + 1 - q) / 2 - e
  have hk : 0 < k := sub_pos.mpr heq
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
  have hpower := weighted_power_velocity_lower_bound hc.le hRt hδ.le (hpos t hat)
    hep.le (hlinear t hat) hvelocity
  convert hpower using 1
  congr 2
  dsimp [k]
  cas

end WaveEquation.SmallData.Kato
