/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core

/-!
# Nonnegative test functions with small Sobolev norm

Multiplying a fixed mollifier by a small positive constant preserves its support
and the sign of its integral. Linearity of the smooth Sobolev embedding then makes
its norm as small as prescribed. The support stays inside the ball of radius two,
independently of the norm bound and derivative order.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.GraphSpace

/-- There are nonnegative smooth compactly supported functions of positive integral
and arbitrarily small `W^{k,p}` norm. A single fixed support ball works for every
positive norm bound. -/
theorem exists_nonneg_testFunction_sobolevNorm_lt
    (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      (∀ x, 0 ≤ φ x) ∧
      (∀ x, 2 ≤ ‖x‖ → φ x = 0) ∧
      0 < ∫ x, φ x ∧
      ‖globalTestFunctionToWkpOn (k := k) (p := p) (Ω := univ) φ‖ < ε := by
  let μ := Approximation.standardMollifier n
  let φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    TestFunction.mk μ.ρ μ.smooth μ.compactSupport (subset_univ _)
  let U := globalTestFunctionToWkpOn (k := k) (p := p) (Ω := univ) φ
  let c := ε / (1 + ‖U‖)
  have hden : 0 < 1 + ‖U‖ := by positivity
  have hc : 0 < c := div_pos hε hden
  refine ⟨c • φ, ?_, ?_, ?_, ?_⟩
  · intro x
    change 0 ≤ c * μ.ρ x
    exact mul_nonneg hc.le (μ.nonneg x)
  · intro x hx
    change c * (Approximation.standardMollifier n).ρ x = 0
    rw [Approximation.standardMollifier_eq_norm,
      Real.smoothTransition.zero_iff_nonpos.mpr (by linarith), zero_div, mul_zero]
  · change 0 < ∫ x, c * μ.ρ x
    rw [integral_const_mul, μ.integral_one, mul_one]
    exact hc
  · rw [globalTestFunctionToWkpOn_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    change c * ‖U‖ < ε
    have hsmall : ε * ‖U‖ / (1 + ‖U‖) < ε :=
      (div_lt_iff₀ hden).2 (by nlinarith)
    simpa only [c, div_mul_eq_mul_div] using hsmall

end SobolevSpace.GraphSpace
