/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Smooth Lipschitz cutoffs on a prescribed ball

Multiplying by a smooth bump preserves a map on a closed ball and gives compact
support. If the map is at least once continuously differentiable, the resulting
map is globally Lipschitz. This lets a local evolution use a global existence
theorem while retaining the original equation throughout a controlled range.
-/

@[expose] public noncomputable section

open Set
open scoped NNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth map has a compactly supported globally Lipschitz replacement that
agrees with it on a prescribed positive-radius closed ball. The construction
preserves the original differentiability order. -/
theorem ContDiff.exists_lipschitzWith_compactSupport_eqOn_closedBall
    {m : ℕ∞} {f : E → F} (hf : ContDiff ℝ m f) (hm : m ≠ 0)
    (x : E) {R : ℝ} (hR : 0 < R) :
    ∃ (g : E → F) (K : ℝ≥0),
      ContDiff ℝ m g ∧ HasCompactSupport g ∧ LipschitzWith K g ∧
        EqOn g f (Metric.closedBall x R) := by
  let _ : FiniteDimensional ℝ E := .of_locallyCompactSpace ℝ
  let b : ContDiffBump x :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hR
      rIn_lt_rOut := lt_add_one R }
  let g : E → F := fun y ↦ b y • f y
  have hg : ContDiff ℝ m g := b.contDiff.smul hf
  have hc : HasCompactSupport g := b.hasCompactSupport.smul_right
  obtain ⟨K, hK⟩ := hg.lipschitzWith_of_hasCompactSupport hc (by simpa using hm)
  refine ⟨g, K, hg, hc, hK, ?_⟩
  intro y hy
  change b y • f y = f y
  rw [b.one_of_mem_closedBall hy, one_smul]
