/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Power
public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.Lifespan
public import PDE.Spaces.Sobolev.Approximation.Density.SmallNorm

/-!
# Constructed classical solutions at the critical Strauss exponent

At `p = 1 + √2`, the power reaction is C². The local cone construction
therefore gives a classical solution from compact C² velocity and zero
displacement. For nonnegative velocity of positive integral, the critical
Strauss argument bounds every classical existence interval. Local uniqueness
and gluing extend the constructed solution to a positive finite maximal time.

A scaled smooth mollifier gives such data with arbitrarily small norm in any
prescribed integer-order Sobolev space. These results establish finite failure
of classical continuation; divergence of a particular norm requires its own
continuation criterion.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace.GraphSpace TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace WaveEquation.SmallData.Classical

/-- Nonnegative compact C² velocity with positive integral constructs a wave
with positive finite maximal classical lifespan at `p = 1 + √2` in three
dimensions. The initial displacement is zero. -/
theorem exists_finite_maximalSolution_three_at_strauss {h : ℝ^3 → ℝ} {R : ℝ} (hh : ContDiff ℝ 2 h)
    (hhn : ∀ x, 0 ≤ h x) (hs : ∀ x, R < ‖x‖ → h x = 0) (hR : 0 < R) (hpositive : 0 < ∫ x, h x) :
    ∃ T : ℝ, ∃ u : ℝ^4 → ℝ,
      IsMaximalSolutionBefore (fun z ↦ -|z| ^ (1 + Real.sqrt 2)) (fun _ ↦ 0) h T u := by
  have hhc : HasCompactSupport h := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^3) R) fun x hx ↦ ?_
    exact hs x (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx)
  obtain ⟨a, u₀, _, h₀⟩ :=
    LocalPower.exists_solutionBefore_abs_rpow_three two_lt_one_add_sqrt_two.le hh hhc
  obtain ⟨T, u, hu, _⟩ := exists_maximalSolution_three_at_strauss hh hhn hs hR hpositive h₀
  exact ⟨T, u, hu⟩

/-- Arbitrarily small smooth compact velocities in any prescribed `W^{k,q}`
space construct finite maximal classical waves at the three-dimensional
critical Strauss exponent. The positive integral keeps the data nontrivial. -/
theorem exists_small_data_finite_maximalSolution_three_at_strauss
    (k : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] {ε : ℝ} (hε : 0 < ε) :
    ∃ h : 𝓓((⊤ : Opens (ℝ^3)), ℝ),
      (∀ x, 0 ≤ h x) ∧
      (∀ x, 2 ≤ ‖x‖ → h x = 0) ∧
      0 < ∫ x, h x ∧
      ‖globalTestFunctionToWkpOn (k := k) (p := q) (Ω := univ) h‖ < ε ∧
      ∃ T : ℝ, ∃ u : ℝ^4 → ℝ,
        IsMaximalSolutionBefore (fun z ↦ -|z| ^ (1 + Real.sqrt 2))
          (fun _ ↦ 0) h T u := by
  obtain ⟨h, hnonneg, hsupport, hpositive, hnorm⟩ :=
    exists_nonneg_testFunction_sobolevNorm_lt 3 k q hε
  refine ⟨h, hnonneg, hsupport, hpositive, hnorm, ?_⟩
  exact exists_finite_maximalSolution_three_at_strauss
    (h.contDiff.of_le (by simp)) hnonneg
    (fun x hx ↦ hsupport x hx.le) (by norm_num) hpositive

end WaveEquation.SmallData.Classical
