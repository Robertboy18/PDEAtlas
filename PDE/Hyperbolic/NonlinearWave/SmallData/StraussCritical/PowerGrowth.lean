/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.PolynomialGrowth
import CAS.ExactTactic

/-!
# Integrating an unbounded power coefficient

If a derivative divided by its expected power tends to infinity, its primitive
divided by the integrated power also tends to infinity. Thus the logarithmic
source gain persists after both mass integrations.
-/

@[expose] public noncomputable section

open Filter Set

namespace WaveEquation.SmallData.Kato

/-- An unbounded coefficient in a derivative's power lower bound survives integration. -/
theorem tendsto_div_rpow_atTop_of_deriv {F : ℝ → ℝ} {α : ℝ} (hα : 0 < α)
    (hgrowth : Tendsto (fun t ↦ deriv F t / t ^ (α - 1)) atTop atTop) :
    Tendsto (fun t ↦ F t / t ^ α) atTop atTop := by
  refine tendsto_atTop.2 fun M ↦ ?_
  let c := 2 * α * (max M 0 + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨b, hb⟩ := eventually_atTop.mp (hgrowth.eventually (eventually_ge_atTop c))
  let d := max b 1
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have he := eventually_power_lower_bound_of_deriv hd hc hα
    (fun t ht ↦ by
      have htpos : 0 < t := hd.trans_le ht
      exact (le_div_iff₀ (Real.rpow_pos_of_pos htpos _)).mp
        (hb t ((le_max_left b 1).trans ht)))
  filter_upwards [he, eventually_ge_atTop d] with t ht htd
  apply (le_div_iff₀ (Real.rpow_pos_of_pos (hd.trans_le htd) α)).mpr
  have hcoef : c / (2 * α) = max M 0 + 1 := by
    dsimp [c]
    exact mul_div_cancel_left₀ _ (by positivity)
  rw [hcoef] at ht
  exact (mul_le_mul_of_nonneg_right (by linarith [le_max_left M 0])
    (Real.rpow_nonneg (hd.trans_le htd).le α)).trans ht

/-- Two derivatives integrate an unbounded acceleration coefficient twice. -/
theorem tendsto_div_rpow_atTop_of_acceleration {F P : ℝ → ℝ} {a p : ℝ} (hp : p < 3)
    (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t)
    (hgrowth : Tendsto (fun t ↦ deriv P t / t ^ (2 - p)) atTop atTop) :
    Tendsto (fun t ↦ F t / t ^ (4 - p)) atTop atTop := by
  have hfirst : Tendsto (fun t ↦ P t / t ^ (3 - p)) atTop atTop := by
    apply tendsto_div_rpow_atTop_of_deriv (by linarith : 0 < 3 - p)
    convert hgrowth using 1
    funext t
    congr 2
    cas
  apply tendsto_div_rpow_atTop_of_deriv (by linarith : 0 < 4 - p)
  apply hfirst.congr'
  filter_upwards [eventually_ge_atTop a] with t ht
  rw [(hF t ht).deriv]
  congr 2
  cas

end WaveEquation.SmallData.Kato
