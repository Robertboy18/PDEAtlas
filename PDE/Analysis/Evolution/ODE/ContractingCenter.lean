/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.AmplitudeClock

/-!
# Convergence of a center with exponentially decaying velocity

For a continuous coefficient `C` with `|C| ≤ K` on `[0, ∞)` and `λ > 0`, the
velocity `-C(t) s₀ e^{-λ t}` is integrable on `(0, ∞)`. A center with this velocity
converges to `center 0 + ∫₀^∞ velocity`, and its distance from the limit at time
`t` is at most `K s₀ e^{-λ t} / λ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution.ODE

/-- The center velocity `-C(t) s₀ e^{-λ t}` for a coefficient `C` and the
exponentially contracting spatial scale `s₀ e^{-λ t}`. -/
def travelingCenterVelocity (C : ℝ → ℝ) (sr₀ lam : ℝ) (t : ℝ) : ℝ :=
  -C t * sr₀ * Real.exp (-lam * t)

/-- The contracting center moves with the modulated exponential spatial scale. -/
add_decl_doc travelingCenterVelocity.eq_1

/-- Bounded modulation gives an exponential bound on the center speed. -/
theorem abs_travelingCenterVelocity_le
    (C : ℝ → ℝ) (sr₀ lam K t : ℝ) (hsr : 0 ≤ sr₀) (hC : |C t| ≤ K) :
    |travelingCenterVelocity C sr₀ lam t| ≤ K * sr₀ * Real.exp (-lam * t) := by
  unfold travelingCenterVelocity
  simp only [abs_mul, abs_neg, abs_of_nonneg hsr, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hsr)
    (Real.exp_pos _).le

/-- The center velocity is integrable on the entire nonnegative rescaled-time axis. -/
theorem integrableOn_travelingCenterVelocity
    (C : ℝ → ℝ) (sr₀ lam K : ℝ) (hsr : 0 ≤ sr₀) (hlam : 0 < lam)
    (hcontinuous : ContinuousOn C (Ici (0 : ℝ)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), |C t| ≤ K) :
    IntegrableOn (travelingCenterVelocity C sr₀ lam) (Ioi (0 : ℝ)) := by
  have hvelocity : ContinuousOn (travelingCenterVelocity C sr₀ lam) (Ioi (0 : ℝ)) := by
    unfold travelingCenterVelocity
    exact ((hcontinuous.mono Ioi_subset_Ici_self).neg.mul_const sr₀).mul
      (by fun_prop)
  have hexp : IntegrableOn (fun t : ℝ ↦ (K * sr₀) * Real.exp (-lam * t))
      (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hlam) 0).const_mul _
  apply hexp.mono' (hvelocity.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  exact abs_travelingCenterVelocity_le C sr₀ lam K t hsr
    (hbound t (Ioi_subset_Ici_self ht))

/-- Integrating the center ODE identifies the physical displacement. -/
theorem travelingCenter_eq_initial_add_integral
    (center C : ℝ → ℝ) (sr₀ lam t : ℝ) (ht : 0 ≤ t)
    (hcontinuous : ContinuousOn C (Ici (0 : ℝ)))
    (hcenter : ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt center (travelingCenterVelocity C sr₀ lam s) s) :
    center t = center 0 + ∫ s in (0 : ℝ)..t, travelingCenterVelocity C sr₀ lam s := by
  have hvelocity : ContinuousOn (travelingCenterVelocity C sr₀ lam) (Icc (0 : ℝ) t) := by
    unfold travelingCenterVelocity
    exact ((hcontinuous.mono Icc_subset_Ici_self).neg.mul_const sr₀).mul (by fun_prop)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (fun s hs ↦ (hcenter s (Icc_subset_Ici_self hs)).continuousAt.continuousWithinAt)
    (fun s hs ↦ hcenter s (show 0 ≤ s from hs.1.le))
    (hvelocity.intervalIntegrable_of_Icc ht)
  rw [hFTC, add_sub_cancel]

/-- The physical center converges to the initial center plus the total center velocity. -/
theorem tendsto_travelingCenter_atTop
    (center C : ℝ → ℝ) (sr₀ lam K : ℝ) (hsr : 0 ≤ sr₀) (hlam : 0 < lam)
    (hcontinuous : ContinuousOn C (Ici (0 : ℝ)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), |C t| ≤ K)
    (hcenter : ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt center (travelingCenterVelocity C sr₀ lam s) s) :
    Filter.Tendsto center Filter.atTop
      (𝓝 (center 0 + ∫ s in Ioi (0 : ℝ), travelingCenterVelocity C sr₀ lam s)) := by
  have hint := integrableOn_travelingCenterVelocity C sr₀ lam K hsr hlam
    hcontinuous hbound
  have hlimit :=
    (intervalIntegral_tendsto_integral_Ioi 0 hint Filter.tendsto_id).const_add (center 0)
  apply hlimit.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  exact (travelingCenter_eq_initial_add_integral center C sr₀ lam t ht
    hcontinuous hcenter).symm

/-- The remaining distance to the limiting center decays exponentially. -/
theorem abs_travelingCenter_limit_sub_le
    (center C : ℝ → ℝ) (sr₀ lam K t : ℝ)
    (hsr : 0 ≤ sr₀) (hlam : 0 < lam) (ht : 0 ≤ t)
    (hcontinuous : ContinuousOn C (Ici (0 : ℝ)))
    (hbound : ∀ s ∈ Ici (0 : ℝ), |C s| ≤ K)
    (hcenter : ∀ s ∈ Ici (0 : ℝ),
      HasDerivAt center (travelingCenterVelocity C sr₀ lam s) s) :
    |(center 0 + ∫ s in Ioi (0 : ℝ), travelingCenterVelocity C sr₀ lam s) - center t| ≤
      K * sr₀ * Real.exp (-lam * t) / lam := by
  have hint := integrableOn_travelingCenterVelocity C sr₀ lam K hsr hlam
    hcontinuous hbound
  rw [travelingCenter_eq_initial_add_integral center C sr₀ lam t ht hcontinuous hcenter,
    add_sub_add_left_eq_sub, ← intervalIntegral.integral_Ioi_sub_Ioi hint ht,
    sub_sub_cancel]
  apply abs_integral_le_integral_abs.trans
  apply physical_clock_tail_le (fun s ↦ |travelingCenterVelocity C sr₀ lam s|)
    (K * sr₀) lam t hlam
  · exact (hint.mono_set (Ioi_subset_Ioi ht)).abs
  · intro s hs
    exact ⟨abs_nonneg _, abs_travelingCenterVelocity_le C sr₀ lam K s hsr
      (hbound s (ht.trans hs.le))⟩

end PDE.Analysis.Evolution.ODE
