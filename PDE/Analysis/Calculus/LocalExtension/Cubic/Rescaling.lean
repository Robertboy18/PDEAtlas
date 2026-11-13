/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

import CAS.ExactTactic

/-!
# Cubic rescaling of a fixed scalar profile

For a fixed profile `φ`, the rescaling `ε³ * φ(s / ε)` has value, first derivative,
and second derivative of sizes `ε³`, `ε²`, and `ε`, respectively. Uniform bounds
on the three jets of `φ` therefore give one bound `C * ε` for all Fréchet jets of
orders at most two when `0 < ε ≤ 1`.

The profile bounds are explicit hypotheses, independent of `ε`. Compact support
is not needed for these estimates. State-space composition and scalar-vector
multiplication can use Mathlib's `norm_iteratedFDeriv_comp_le` and
`norm_iteratedFDeriv_smul_le` directly.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace PDE.Analysis

/-- Cubic amplitude with linear rescaling of a fixed scalar profile. -/
def cubicRescale (φ : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  ε ^ 3 * φ (s / ε)

/-- Rescaling by a fixed constant preserves every available order of smoothness. -/
theorem contDiff_cubicRescale {φ : ℝ → ℝ} {n : ℕ∞ω}
    (hφ : ContDiff ℝ n φ) (ε : ℝ) : ContDiff ℝ n (cubicRescale φ ε) := by
  exact contDiff_const.mul (hφ.comp (contDiff_id.div_const ε))

/-- The actual first derivative loses one power of the rescaling parameter. -/
theorem deriv_cubicRescale {φ : ℝ → ℝ} {ε s : ℝ}
    (hε : ε ≠ 0) (hφ : DifferentiableAt ℝ φ (s / ε)) :
    deriv (cubicRescale φ ε) s = ε ^ 2 * deriv φ (s / ε) := by
  have hscale : ε ^ 3 * (1 / ε) = ε ^ 2 := by cas using [hε]
  calc
    deriv (cubicRescale φ ε) s =
        ε ^ 3 * (deriv φ (s / ε) * (1 / ε)) := by
      exact ((hφ.hasDerivAt.comp s ((hasDerivAt_id s).div_const ε)).const_mul
        (ε ^ 3)).deriv
    _ = (ε ^ 3 * (1 / ε)) * deriv φ (s / ε) := by ac_rfl
    _ = ε ^ 2 * deriv φ (s / ε) := by rw [hscale]

/-- The actual second derivative loses two powers of the rescaling parameter. -/
theorem deriv_deriv_cubicRescale {φ : ℝ → ℝ} {ε : ℝ}
    (hε : ε ≠ 0) (hφ : ContDiff ℝ 2 φ) (s : ℝ) :
    deriv (deriv (cubicRescale φ ε)) s = ε * deriv (deriv φ) (s / ε) := by
  have hfirst : deriv (cubicRescale φ ε) =
      fun u ↦ ε ^ 2 * deriv φ (u / ε) := by
    funext u
    exact deriv_cubicRescale hε (hφ.differentiable two_ne_zero (u / ε))
  have hscale : ε ^ 2 * (1 / ε) = ε := by cas using [hε]
  rw [hfirst]
  calc
    deriv (fun u ↦ ε ^ 2 * deriv φ (u / ε)) s =
        ε ^ 2 * (deriv (deriv φ) (s / ε) * (1 / ε)) := by
      exact (((hφ.differentiable_deriv_two (s / ε)).hasDerivAt.comp s
        ((hasDerivAt_id s).div_const ε)).const_mul (ε ^ 2)).deriv
    _ = (ε ^ 2 * (1 / ε)) * deriv (deriv φ) (s / ε) := by ac_rfl
    _ = ε * deriv (deriv φ) (s / ε) := by rw [hscale]

/-- The sharp powers of `ε` follow from bounds on the fixed profile's three jets.
This estimate does not require `ε ≤ 1`. -/
theorem cubicRescale_jet_bounds {φ : ℝ → ℝ} {C ε : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hε : 0 < ε)
    (hφ0 : ∀ s, ‖φ s‖ ≤ C)
    (hφ1 : ∀ s, ‖deriv φ s‖ ≤ C)
    (hφ2 : ∀ s, ‖deriv (deriv φ) s‖ ≤ C) (s : ℝ) :
    ‖cubicRescale φ ε s‖ ≤ C * ε ^ 3 ∧
      ‖deriv (cubicRescale φ ε) s‖ ≤ C * ε ^ 2 ∧
      ‖deriv (deriv (cubicRescale φ ε)) s‖ ≤ C * ε := by
  have hmul (k : ℕ) {a : ℝ} (ha : ‖a‖ ≤ C) : ‖ε ^ k * a‖ ≤ C * ε ^ k := by
    calc
      ‖ε ^ k * a‖ = ε ^ k * ‖a‖ := by
        simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hε]
      _ ≤ ε ^ k * C := mul_le_mul_of_nonneg_left ha (pow_nonneg hε.le k)
      _ = C * ε ^ k := mul_comm _ _
  refine ⟨?_, ?_, ?_⟩
  · exact hmul 3 (hφ0 (s / ε))
  · rw [deriv_cubicRescale hε.ne' (hφ.differentiable two_ne_zero (s / ε))]
    exact hmul 2 (hφ1 (s / ε))
  · rw [deriv_deriv_cubicRescale hε.ne' hφ s]
    simpa only [pow_one] using hmul 1 (hφ2 (s / ε))

/-- All scalar Fréchet jets of orders zero, one, and two are bounded by `C * ε`.
The same fixed constant works for every `0 < ε ≤ 1` and every signed input `s`. -/
theorem norm_iteratedFDeriv_cubicRescale_le {φ : ℝ → ℝ} {C ε : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (hφ0 : ∀ s, ‖φ s‖ ≤ C)
    (hφ1 : ∀ s, ‖deriv φ s‖ ≤ C)
    (hφ2 : ∀ s, ‖deriv (deriv φ) s‖ ≤ C)
    {n : ℕ} (hn : n ≤ 2) (s : ℝ) :
    ‖iteratedFDeriv ℝ n (cubicRescale φ ε) s‖ ≤ C * ε := by
  have hC : 0 ≤ C := (norm_nonneg (φ 0)).trans (hφ0 0)
  obtain ⟨h0, h1, h2⟩ := cubicRescale_jet_bounds hφ hε hφ0 hφ1 hφ2 s
  have hε2 : ε ^ 2 ≤ ε := by cas using [hε, hεone]
  have hε3 : ε ^ 3 ≤ ε := by
    calc
      ε ^ 3 = ε ^ 2 * ε := by cas
      _ ≤ ε * ε := mul_le_mul_of_nonneg_right hε2 hε.le
      _ = ε ^ 2 := by cas
      _ ≤ ε := hε2
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  interval_cases n
  · simpa only [iteratedDeriv_zero] using
      h0.trans (mul_le_mul_of_nonneg_left hε3 hC)
  · simpa only [iteratedDeriv_one] using
      h1.trans (mul_le_mul_of_nonneg_left hε2 hC)
  · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using h2

/-- Vanishing value and first two derivatives at the origin survive rescaling. -/
theorem cubicRescale_zero_jets {φ : ℝ → ℝ} {ε : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hε : ε ≠ 0)
    (h0 : φ 0 = 0) (h1 : deriv φ 0 = 0) (h2 : deriv (deriv φ) 0 = 0) :
    cubicRescale φ ε 0 = 0 ∧
      deriv (cubicRescale φ ε) 0 = 0 ∧
      deriv (deriv (cubicRescale φ ε)) 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [cubicRescale, zero_div, h0, mul_zero]
  · rw [deriv_cubicRescale hε (hφ.differentiable two_ne_zero (0 / ε))]
    simp only [zero_div, h1, mul_zero]
  · rw [deriv_deriv_cubicRescale hε hφ 0]
    simp only [zero_div, h2, mul_zero]

end PDE.Analysis
