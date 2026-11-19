/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Logarithmic convexity of nonnegative energies

The differential inequality `E'² ≤ E E''` yields convexity of
`log (E + ε)` when `E'' ≥ 0`. Keeping this sign condition is essential
at zeros of the energy. Letting the positive regularization tend to zero
then permits zero endpoint values.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace PDE.Analysis

variable {E E₁ E₂ : ℝ → ℝ} {a b : ℝ}

/-- Convexity of the regularized logarithm, including zeros of the energy. -/
theorem convexOn_log_add_of_energy_derivatives
    (hc : ContinuousOn E (Icc a b)) (hE : ∀ t ∈ Icc a b, 0 ≤ E t)
    (h₁ : ∀ t ∈ Ioo a b, HasDerivAt E (E₁ t) t)
    (h₂ : ∀ t ∈ Ioo a b, HasDerivAt E₁ (E₂ t) t)
    (h₂nonneg : ∀ t ∈ Ioo a b, 0 ≤ E₂ t)
    (hCS : ∀ t ∈ Ioo a b, E₁ t ^ 2 ≤ E t * E₂ t)
    {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ (Icc a b) (fun t ↦ Real.log (E t + ε)) := by
  have hpos {t : ℝ} (ht : t ∈ Icc a b) : 0 < E t + ε :=
    add_pos_of_nonneg_of_pos (hE t ht) hε
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    ((hc.add continuousOn_const).log (fun t ht ↦ (hpos ht).ne'))
    (f' := fun t ↦ E₁ t / (E t + ε))
    (f'' := fun t ↦ (E₂ t * (E t + ε) - E₁ t ^ 2) / (E t + ε) ^ 2)
  · intro t ht
    rw [interior_Icc] at ht
    exact (((h₁ t ht).add_const ε).log
      (hpos (Ioo_subset_Icc_self ht)).ne').hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    simpa only [pow_two, Pi.div_apply] using!
      ((h₂ t ht).div ((h₁ t ht).add_const ε)
        (hpos (Ioo_subset_Icc_self ht)).ne').hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    apply div_nonneg _ (sq_nonneg _)
    nlinarith [hCS t ht, mul_nonneg (h₂nonneg t ht) hε.le]

/-- The multiplicative chord inequality for a nonnegative energy.
Both endpoints may vanish. -/
theorem energy_le_rpow_mul_rpow
    (hc : ContinuousOn E (Icc a b)) (hE : ∀ t ∈ Icc a b, 0 ≤ E t)
    (h₁ : ∀ t ∈ Ioo a b, HasDerivAt E (E₁ t) t)
    (h₂ : ∀ t ∈ Ioo a b, HasDerivAt E₁ (E₂ t) t)
    (h₂nonneg : ∀ t ∈ Ioo a b, 0 ≤ E₂ t)
    (hCS : ∀ t ∈ Ioo a b, E₁ t ^ 2 ≤ E t * E₂ t)
    (hab : a ≤ b) {c d : ℝ} (hc0 : 0 ≤ c) (hd0 : 0 ≤ d) (hcd : c + d = 1) :
    E (c * a + d * b) ≤ E a ^ c * E b ^ d := by
  have ht : c * a + d * b ∈ Icc a b :=
    (convex_Icc a b) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hc0 hd0 hcd
  have hε (ε : ℝ) (hε : 0 < ε) :
      E (c * a + d * b) + ε ≤ (E a + ε) ^ c * (E b + ε) ^ d := by
    have hlog := (convexOn_log_add_of_energy_derivatives hc hE h₁ h₂ h₂nonneg hCS hε).2
      ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hc0 hd0 hcd
    have h := Real.exp_le_exp.mpr hlog
    simp only [smul_eq_mul] at h
    rw [Real.exp_log (add_pos_of_nonneg_of_pos (hE _ ht) hε), Real.exp_add] at h
    simpa only [mul_comm c, mul_comm d, Real.exp_mul,
      Real.exp_log (add_pos_of_nonneg_of_pos (hE a ⟨le_rfl, hab⟩) hε),
      Real.exp_log (add_pos_of_nonneg_of_pos (hE b ⟨hab, le_rfl⟩) hε)] using h
  have hleft : Tendsto (fun ε : ℝ ↦ E (c * a + d * b) + ε) (𝓝[>] 0)
      (𝓝 (E (c * a + d * b))) := by
    have hc : Continuous (fun ε : ℝ ↦ E (c * a + d * b) + ε) :=
      continuous_const.add continuous_id
    simpa using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
  have hright : Tendsto (fun ε : ℝ ↦ (E a + ε) ^ c * (E b + ε) ^ d) (𝓝[>] 0)
      (𝓝 (E a ^ c * E b ^ d)) := by
    have hc : Continuous (fun ε : ℝ ↦ (E a + ε) ^ c * (E b + ε) ^ d) :=
      ((Real.continuous_rpow_const hc0).comp (continuous_const.add continuous_id)).mul
        ((Real.continuous_rpow_const hd0).comp (continuous_const.add continuous_id))
    simpa using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 0) (a := (0 : ℝ)))
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with ε hεpos using hε ε hεpos

/-- A nonnegative log-convex energy cannot become zero in finite time unless
it was zero throughout the closed interval. -/
theorem energy_eq_zero_of_terminal_eq_zero
    (hc : ContinuousOn E (Icc a b)) (hE : ∀ t ∈ Icc a b, 0 ≤ E t)
    (h₁ : ∀ t ∈ Ioo a b, HasDerivAt E (E₁ t) t)
    (h₂ : ∀ t ∈ Ioo a b, HasDerivAt E₁ (E₂ t) t)
    (h₂nonneg : ∀ t ∈ Ioo a b, 0 ≤ E₂ t)
    (hCS : ∀ t ∈ Ioo a b, E₁ t ^ 2 ≤ E t * E₂ t)
    (hab : a < b) (hb : E b = 0) :
    EqOn E (fun _ ↦ 0) (Icc a b) := by
  have hz : EqOn E (fun _ ↦ 0) (Ioo a b) := by
    intro t ht
    have hd : 0 < b - a := sub_pos.mpr hab
    have hc0 : 0 ≤ (b - t) / (b - a) := div_nonneg (sub_nonneg.mpr ht.2.le) hd.le
    have hd0 : 0 < (t - a) / (b - a) := div_pos (sub_pos.mpr ht.1) hd
    have hsum : (b - t) / (b - a) + (t - a) / (b - a) = 1 := by
      rw [← add_div]
      convert div_self hd.ne' using 1
      ring
    have htime : (b - t) / (b - a) * a + (t - a) / (b - a) * b = t := by
      field_simp
      ring
    have h := energy_le_rpow_mul_rpow hc hE h₁ h₂ h₂nonneg hCS hab.le hc0 hd0.le hsum
    rw [htime, hb, Real.zero_rpow hd0.ne', mul_zero] at h
    exact le_antisymm h (hE t (Ioo_subset_Icc_self ht))
  exact hz.of_subset_closure hc continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo hab.ne])

end PDE.Analysis
