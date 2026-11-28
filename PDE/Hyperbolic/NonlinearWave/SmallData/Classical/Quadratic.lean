/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.SmoothReaction

/-!
# Local quadratic power waves

The smooth cutoff of `-z²` agrees with the original focusing reaction while the
constructed displacement remains in `[-1,1]`. Thus local existence is proved for the
quadratic power, in every positive dimension (`exists_solutionBefore_quadratic_zero`).
This argument uses smoothness of the polynomial square.

In three dimensions the finite maximal classical solution for compact velocity with positive
integral is the exponent `p = 2` of `LocalPower.exists_finite_maximalSolution_abs_rpow_three`,
which holds for `2 ≤ p < 1 + √2` and asks only for a `C²` velocity.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common Set
open scoped NNReal

namespace WaveEquation.SmallData.Classical

private theorem exists_smooth_quadratic_cutoff :
    ∃ (f : ℝ → ℝ) (K : ℝ≥0), ContDiff ℝ (⊤ : ℕ∞) f ∧ LipschitzWith K f ∧
      f 0 = 0 ∧ ∀ z, |z| ≤ 1 → f z = -|z| ^ (2 : ℝ) := by
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := 2
      rOut := 3
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let f : ℝ → ℝ := fun z ↦ b z * (-(z ^ 2))
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := b.contDiff.mul (contDiff_id.pow 2).neg
  have hc : HasCompactSupport f := b.hasCompactSupport.mul_right
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by simp)
  refine ⟨f, K, hf, hK, by simp [f], fun z hz ↦ ?_⟩
  have hb : z ∈ Metric.closedBall 0 b.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hz.trans (by norm_num [b])
  change b z * (-(z ^ 2)) = -|z| ^ (2 : ℝ)
  rw [b.one_of_mem_closedBall hb, one_mul, Real.rpow_two, sq_abs]

/-- Local existence for the quadratic focusing wave, in every positive
dimension, with zero displacement and arbitrary smooth compact velocity.
The solution has joint C² regularity across its ordinary initial traces. -/
theorem exists_solutionBefore_quadratic_zero {n : ℕ} [NeZero n] (h : ℝ^n → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h) :
    ∃ T : ℝ, ∃ u : ℝ^(n + 1) → ℝ, IsSolutionBefore (fun z ↦ -|z| ^ (2 : ℝ)) (fun _ ↦ 0) h T u := by
  obtain ⟨f, K, hs, hf, hf0, heq⟩ := exists_smooth_quadratic_cutoff
  obtain ⟨T, u, hu, hb⟩ := exists_solutionBefore_smoothReaction_zero hs hf hf0 h hh hhc
  refine ⟨T, u, hu.time_pos, hu.regular, ?_, hu.position, hu.velocity⟩
  intro p hp
  rw [hu.equation p hp, heq]
  simpa only [timeSpaceCons_spatialPart] using hb (p 0) ⟨hp.1, hp.2.le⟩ (spatialPart p)

end WaveEquation.SmallData.Classical
