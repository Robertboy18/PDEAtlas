/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SymbolDecay
public import PDE.Analysis.Calculus.Radial.DecayMajorants

/-!
# Lebesgue integrability from symbol decay

A smooth function on a finite-dimensional space with symbol decay of order `d` has its `k`th
derivative bounded by a multiple of `(1 + ‖x‖)^{d - k}` everywhere, so the derivative lies in
`Lᵖ` for every additive Haar measure as soon as `(k - d) p` exceeds the dimension.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth function with symbol decay of order `d ≤ k` has its `k`th derivative bounded by a
multiple of `(1 + ‖x‖)^{d - k}` on the whole space. -/
theorem HasSymbolDecay.exists_bound_one_add_norm {d : ℤ} {f : E → F}
    (hf : HasSymbolDecay d f) (hfc : ContDiff ℝ ∞ f) {k : ℕ} (hdk : d ≤ k) :
    ∃ C ≥ 0, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ C / (1 + ‖x‖) ^ ((k : ℤ) - d).toNat := by
  obtain ⟨C, hC0, hC⟩ := hf.exists_bound_nonneg
  set n : ℕ := ((k : ℤ) - d).toNat with hn
  have hnz : (n : ℤ) = k - d := by rw [hn]; omega
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn
    (hfc.continuous_iteratedFDeriv (m := k) (by simp)).norm.continuousOn
  refine PDE.Analysis.Radial.exists_one_add_norm_pow_bound_of_near_far n
    (fun x ↦ norm_nonneg _) ⟨K, fun x hx ↦ ?_⟩
    ⟨C k + max K 0, add_nonneg (hC0 k) (le_max_right _ _), fun x hx ↦ ?_⟩
  · have h := hK x (by rwa [Metric.mem_closedBall, dist_zero_right])
    rwa [Real.norm_of_nonneg (norm_nonneg _)] at h
  · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [le_div_iff₀ (pow_pos hpos n)]
    by_cases hx1 : 1 ≤ ‖x‖
    · have hz : ‖x‖ ^ (d - (k : ℤ)) * ‖x‖ ^ n = 1 := by
        rw [← zpow_natCast, ← zpow_add₀ hpos.ne', hnz, sub_add_sub_cancel, sub_self, zpow_zero]
      calc ‖iteratedFDeriv ℝ k f x‖ * ‖x‖ ^ n ≤ C k * ‖x‖ ^ (d - (k : ℤ)) * ‖x‖ ^ n :=
            mul_le_mul_of_nonneg_right (hC k x hx1) (by positivity)
        _ = C k := by rw [mul_assoc, hz, mul_one]
        _ ≤ C k + max K 0 := le_add_of_nonneg_right (le_max_right _ _)
    · have hle : ‖x‖ ^ n ≤ 1 := pow_le_one₀ hpos.le (not_le.mp hx1).le
      have hKx : ‖iteratedFDeriv ℝ k f x‖ ≤ max K 0 := by
        have h := hK x (by rw [Metric.mem_closedBall, dist_zero_right]; exact (not_le.mp hx1).le)
        rw [Real.norm_of_nonneg (norm_nonneg _)] at h
        exact h.trans (le_max_left _ _)
      calc ‖iteratedFDeriv ℝ k f x‖ * ‖x‖ ^ n ≤ max K 0 * 1 :=
            mul_le_mul hKx hle (by positivity) (le_max_right _ _)
        _ ≤ C k + max K 0 := by rw [mul_one]; exact le_add_of_nonneg_left (hC0 k)

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The `k`th derivative of a smooth function with symbol decay of order `d` lies in `Lᵖ` when
`(k - d) p` exceeds the dimension. -/
theorem HasSymbolDecay.memLp_iteratedFDeriv {d : ℤ} {f : E → F} (hf : HasSymbolDecay d f)
    (hfc : ContDiff ℝ ∞ f) {p : ENNReal} (k : ℕ)
    (hk : (Module.finrank ℝ E : ℝ) < ((k : ℝ) - d) * p.toReal) :
    MemLp (iteratedFDeriv ℝ k f) p μ := by
  have hdk : d ≤ k := by
    by_contra h
    have hneg : (k : ℝ) - d < 0 := by
      rw [sub_neg]
      exact_mod_cast not_le.mp h
    have : ((k : ℝ) - d) * p.toReal ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg.le ENNReal.toReal_nonneg
    linarith [(Nat.cast_nonneg (Module.finrank ℝ E) : (0 : ℝ) ≤ _)]
  obtain ⟨C, hC0, hC⟩ := hf.exists_bound_one_add_norm hfc hdk
  have hcast : ((((k : ℤ) - d).toNat : ℕ) : ℝ) = (k : ℝ) - d := by
    have h : ((((k : ℤ) - d).toNat : ℕ) : ℤ) = (k : ℤ) - d := by omega
    exact_mod_cast h
  exact PDE.Analysis.Radial.memLp_of_one_add_norm_pow_bound
    (hfc.continuous_iteratedFDeriv (m := k) (by simp)).aestronglyMeasurable hC0
    (Filter.Eventually.of_forall hC) (by rwa [hcast])

/-- A smooth function with symbol decay of order `d` lies in `Lᵖ` when `-d p` exceeds the
dimension. -/
theorem HasSymbolDecay.memLp {d : ℤ} {f : E → F} (hf : HasSymbolDecay d f)
    (hfc : ContDiff ℝ ∞ f) {p : ENNReal} (hk : (Module.finrank ℝ E : ℝ) < -(d : ℝ) * p.toReal) :
    MemLp f p μ := by
  have h := hf.memLp_iteratedFDeriv (μ := μ) hfc 0 (by simpa using hk)
  refine (memLp_norm_iff hfc.continuous.aestronglyMeasurable).mp ?_
  have heq : (fun x ↦ ‖f x‖) = fun x ↦ ‖iteratedFDeriv ℝ 0 f x‖ :=
    funext fun x ↦ (norm_iteratedFDeriv_zero).symm
  rw [heq]
  exact h.norm

end PDE.Analysis
