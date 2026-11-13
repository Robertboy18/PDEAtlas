/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Bounded C¹ reaction cutoffs

Multiplying a C¹ reaction by a smooth bump preserves it on any prescribed
bounded interval and produces a bounded, globally Lipschitz C¹ reaction.
This supplies the source needed by the global classical constructor.
-/

@[expose] public noncomputable section

open Set Function

namespace WaveEquation

/-- A C¹ reaction has a bounded, globally Lipschitz C¹ replacement agreeing on
`[-R, R]`. -/
theorem exists_bounded_lipschitz_contDiff_reaction {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (R : ℝ) :
    ∃ (F : ℝ → ℝ) (K : NNReal) (C : ℝ), ContDiff ℝ 1 F ∧ LipschitzWith K F ∧
      (∀ z, |z| ≤ R → F z = f z) ∧ ∀ z, ‖F z‖ ≤ C := by
  let b : ContDiffBump (0 : ℝ) :=
    { rIn := max R 0 + 1
      rOut := max R 0 + 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let F : ℝ → ℝ := fun z ↦ b z * f z
  have hF : ContDiff ℝ 1 F := b.contDiff.mul hf
  have hsupport : HasCompactSupport F := b.hasCompactSupport.mul_right
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupport hF (by simp)
  obtain ⟨C, hC⟩ := hsupport.exists_bound_of_continuous hF.continuous
  refine ⟨F, K, C, hF, hK, ?_, hC⟩
  intro z hz
  have hzb : z ∈ Metric.closedBall 0 b.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hz.trans ((le_max_left R 0).trans (le_add_of_nonneg_right zero_le_one))
  change b z * f z = f z
  rw [b.one_of_mem_closedBall hzb, one_mul]

end WaveEquation
