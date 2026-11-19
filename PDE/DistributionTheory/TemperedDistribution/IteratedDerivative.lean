/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import PDE.DistributionTheory.Schwartz.Commutation

/-!
# Iterated derivatives of tempered distributions

Each derivative moved onto a test function contributes a minus sign. Smooth mixed
derivatives commute, so the test can retain the original order of directions.
-/

@[expose] public noncomputable section

open LineDeriv
open scoped SchwartzMap

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Evaluate an iterated distributional derivative by differentiating its Schwartz test. -/
theorem iteratedLineDerivOp_apply_apply {k : ℕ} (m : Fin k → E)
    (T : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    (∂^{m} T) φ = (-1 : ℂ) ^ k • T (∂^{m} φ) := by
  induction k generalizing φ with
  | zero => simp
  | succ k ih =>
    rw [iteratedLineDerivOp_succ_left, lineDerivOp_apply_apply, ih,
      iteratedLineDerivOp_neg, map_neg,
      ← SchwartzMap.lineDerivOp_iteratedLineDerivOp,
      iteratedLineDerivOp_succ_left, pow_succ, mul_smul, neg_one_smul]

end TemperedDistribution
