/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.FinitePropagation
import PDE.FDeriv.SpaceTime

/-!
# Amplitude bounds from a compactly supported classical wave

Finite propagation confines every proper finite time horizon to a fixed spatial
ball. Continuity on the resulting compact cylinder bounds the amplitude on the
whole space. No norm or range bound on the solution is a hypothesis.
-/

@[expose] public noncomputable section

open PDE.Common Set

namespace WaveEquation.SmallData.Classical

variable {n : ℕ} [Fact (0 < n)]

/-- Compact Cauchy data give a uniform amplitude bound on every proper closed
time horizon of a classical solution. The bound follows from the PDE,
finite propagation and compactness. -/
theorem IsSolutionBefore.exists_norm_le_before_of_compact_data {f : ℝ → ℝ} (hf : LocallyLipschitz f)
    (hf0 : f 0 = 0) {g h : ℝ^n → ℝ} {R S T : ℝ} {u : ℝ^(n + 1) → ℝ}
    (hu : IsSolutionBefore f g h T u) (hg : ∀ x, R < ‖x‖ → g x = 0) (hh : ∀ x, R < ‖x‖ → h x = 0)
    (hST : S < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 S, ∀ x, ‖u (timeSpaceCons t x)‖ ≤ B := by
  obtain ⟨v, hv, he⟩ := exists_contDiff_eventuallyEq_before hu.regular hST
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_le_on_timeSpaceCylinder v hv.continuous 0 S (0 : ℝ^n) (R + S)
  refine ⟨B, hB, fun t ht x ↦ ?_⟩
  by_cases hx : ‖x‖ ≤ R + S
  · rw [← (he (timeSpaceCons t x) (by simpa using ht.2)).eq_of_nhds]
    exact hbound t ht x (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  · have hxt : R + t < ‖x‖ := by linarith [ht.2, lt_of_not_ge hx]
    rw [hu.eq_zero_of_norm_gt hf hf0 hg hh ⟨ht.1, ht.2.trans_lt hST⟩ x hxt, norm_zero]
    exact hB

end WaveEquation.SmallData.Classical
