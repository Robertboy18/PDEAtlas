/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.KatoPolynomial
import CAS.ExactTactic

/-!
# Polynomial growth from an acceleration bound

A positive lower bound of order `t^(2-p)` for the second derivative forces
mass growth of order `t^(4-p)` when `p<3`. Both integrations use
derivatives and absorb arbitrary integration constants at a later time.
-/

@[expose] public noncomputable section

open Filter Set

namespace WaveEquation.SmallData.Kato

/-- Integrating a positive power lower bound gives an eventual power lower bound,
with an explicit coefficient. The initial value may have either sign. -/
theorem eventually_power_lower_bound_of_deriv {F : ℝ → ℝ} {a c α : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hα : 0 < α) (hlower : ∀ t, a ≤ t → c * t ^ (α - 1) ≤ deriv F t) :
    ∀ᶠ t in atTop, c / (2 * α) * t ^ α ≤ F t := by
  have hF (t : ℝ) (ht : a ≤ t) : DifferentiableAt ℝ F t := by
    by_contra h
    have h₁ := hlower t ht
    rw [deriv_zero_of_not_differentiableAt h] at h₁
    linarith [mul_pos hc (Real.rpow_pos_of_pos (ha.trans_le ht) (α - 1))]
  let G := fun t ↦ F t - c / α * t ^ α
  have hG (t : ℝ) (ht : a ≤ t) :
      HasDerivAt G (deriv F t - c * t ^ (α - 1)) t := by
    have htpos : 0 < t := ha.trans_le ht
    have hd : HasDerivAt (fun s : ℝ ↦ c / α * s ^ α)
        (c * t ^ (α - 1)) t := by
      cas using And.intro htpos hα
    exact (hF t ht).hasDerivAt.fun_sub hd
  have hmono : MonotoneOn G (Ici a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici a)
      (fun t ht ↦ (hG t ht).continuousAt.continuousWithinAt)
    · intro t ht
      rw [interior_Ici] at ht
      exact (hG t ht.le).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hG t ht.le).deriv]
      exact sub_nonneg.mpr (hlower t ht.le)
  have htop : Tendsto (fun t : ℝ ↦ c / (2 * α) * t ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).const_mul_atTop (div_pos hc (by positivity))
  filter_upwards [eventually_ge_atTop a, htop.eventually (eventually_ge_atTop (-G a))]
    with t ht hlarge
  have h := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  have hcα : c / α = 2 * (c / (2 * α)) := by field_simp
  dsimp [G] at hlarge h
  rw [hcα] at h hlarge
  linarith

/-- A source bound of order `t^(2-p)` forces a positive mass lower bound
of order `t^(4-p)`, rather than assuming it as an ODE input. -/
theorem eventually_power_lower_bound_of_acceleration {F P : ℝ → ℝ} {a c p : ℝ} (ha : 0 < a)
    (hc : 0 < c) (hp : p < 3) (hF : ∀ t, a ≤ t → HasDerivAt F (P t) t)
    (hlower : ∀ t, a ≤ t → c * t ^ (2 - p) ≤ deriv P t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ t in atTop, δ * t ^ (4 - p) ≤ F t := by
  have hfirst : ∀ᶠ t in atTop, c / (2 * (3 - p)) * t ^ (3 - p) ≤ P t := by
    apply eventually_power_lower_bound_of_deriv ha hc (by linarith)
    simpa only [show 3 - p - 1 = 2 - p by cas] using hlower
  obtain ⟨b, hb⟩ := eventually_atTop.mp hfirst
  let d := max a b
  have hd : 0 < d := ha.trans_le (le_max_left a b)
  have hc' : 0 < c / (2 * (3 - p)) := div_pos hc (by linarith)
  refine ⟨c / (2 * (3 - p)) / (2 * (4 - p)), div_pos hc' (by linarith), ?_⟩
  apply eventually_power_lower_bound_of_deriv hd hc' (by linarith)
  intro t ht
  rw [(hF t ((le_max_left a b).trans ht)).deriv,
    show 4 - p - 1 = 3 - p by cas]
  exact hb t ((le_max_right a b).trans ht)

end WaveEquation.SmallData.Kato
