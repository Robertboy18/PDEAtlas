/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.MaximalClassical
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Persistence.SmoothMaximal

import PDE.Common.Euclidean.SpaceTime

/-!
# Initial smoothness of the canonical maximal classical wave

Smooth compact Cauchy data give all-orders regularity of the canonical maximal
field on its entire preterminal domain, including time zero. The same field
satisfies the interior wave equation supplied by the finite-trajectory classical
theory.
-/

@[expose] public noncomputable section

open Filter PDE.Common Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis.Evolution
open scoped NNReal ENNReal Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n] {f : ℝ → ℝ}

/-- The canonical maximal classical wave from smooth compact data is jointly
smooth on its preterminal domain, including the initial face. -/
theorem contDiffOn_infty_higherSmoothMaximalField_of_smoothCompact (hn : n < 4)
    (hv : (n : ℝ) < 2 * (((k + 1 : ℕ) : ℝ) - 1)) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (g h : ℝ^n → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    let x : W^{k + 2,2}(ℝ^n) × W^{k + 1,2}(ℝ^n) :=
      (mkWkpSpaceOnOfContDiff g hg hgc, mkWkpSpaceOnOfContDiff h hh hhc)
    ContDiffOn ℝ (⊤ : ℕ∞) (higherSmoothMaximalField hv hq hs hf0 x)
      {p | 0 ≤ p 0 ∧ ENNReal.ofReal (p 0) <
        (higherLinearSemigroup n (k + 1)).mildLifespan (higherSmoothMap hv hs hf0) x} := by
  intro x
  have hprod := contDiffOn_infty_maximalHigherSmooth_of_smoothCompact
    hn hv hq hs hf0 g h hg hh hgc hhc
  have hc := hprod.comp (timeSpaceContinuousLinearEquiv n).contDiff.contDiffOn
    (fun _ hp ↦ ⟨hp, mem_univ _⟩)
  simp only [Function.comp_def, timeSpaceContinuousLinearEquiv_apply, time_apply] at hc
  refine hc.congr fun p _ ↦ ?_
  rfl

end PDE.Hyperbolic.NonlinearWave.Cauchy
