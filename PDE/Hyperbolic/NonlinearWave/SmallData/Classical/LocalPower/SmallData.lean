/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Power
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.StraussLifespan
public import PDE.Spaces.Sobolev.Approximation.Density.SmallNorm

/-!
# Small noninteger-power waves with finite classical lifespan

The local construction gives the existence hypothesis in the range `2 < p < 1 + √2`. The Strauss
contradiction and classical gluing theorem then give a finite maximal solution. Positive multiples
of a fixed smooth mollifier supply nonzero data arbitrarily small in any prescribed integer-order
Sobolev norm.

The conclusion is failure of classical continuation at a finite time.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace.GraphSpace TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace WaveEquation.SmallData.Classical.LocalPower

/-- Compact C² velocity of positive integral gives a finite maximal
classical power wave in the upper part of the strict three-dimensional Strauss
range. Its local existence is constructed from the data. -/
theorem exists_finite_maximalSolution_abs_rpow_three {p R : ℝ} (hp : 2 < p)
    (hcrit : p < 1 + Real.sqrt 2) {h : ℝ^3 → ℝ} (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h)
    (hs : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R) (hpositive : 0 < ∫ x, h x) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ, IsMaximalSolutionBefore (fun z ↦ -|z| ^ p) (fun _ ↦ 0) h T u := by
  obtain ⟨a, u₀, _, h₀⟩ := exists_solutionBefore_abs_rpow_three hp hh hhc
  obtain ⟨T, u, hu, _⟩ := exists_maximalSolution_three_of_lt_strauss
    contDiff_const hh (fun _ _ ↦ rfl) hs hR (by linarith) hcrit (by simp) hpositive h₀
  exact ⟨T, u, hu⟩

/-- Arbitrarily small smooth compact velocity constructs a
finite maximal noninteger-power wave for `2 < p < 1 + √2`. The positive
integral ensures that the constructed velocity is nontrivial. -/
theorem exists_small_data_finite_maximalSolution_abs_rpow_three {p : ℝ} (hp : 2 < p)
    (hcrit : p < 1 + Real.sqrt 2) (k : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] {ε : ℝ} (hε : 0 < ε) :
    ∃ h : 𝓓((⊤ : Opens (ℝ^3)), ℝ),
      (∀ x, 0 ≤ h x) ∧
      (∀ x, 2 ≤ ‖x‖ → h x = 0) ∧
      0 < ∫ x, h x ∧
      ‖globalTestFunctionToWkpOn (k := k) (p := q) (Ω := univ) h‖ < ε ∧
      ∃ T : ℝ, ∃ u : ℝ^4 → ℝ,
        IsMaximalSolutionBefore (fun z ↦ -|z| ^ p) (fun _ ↦ 0) h T u := by
  obtain ⟨h, hnonneg, hsupport, hpositive, hnorm⟩ :=
    exists_nonneg_testFunction_sobolevNorm_lt 3 k q hε
  refine ⟨h, hnonneg, hsupport, hpositive, hnorm, ?_⟩
  exact exists_finite_maximalSolution_abs_rpow_three hp hcrit
    (h.contDiff.of_le (by simp)) h.hasCompactSupport
    (fun x hx ↦ hsupport x hx.le) (by norm_num) hpositive

end WaveEquation.SmallData.Classical.LocalPower
