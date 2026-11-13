/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.General.TimeDerivatives
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.Pointwise

/-!
# Pointwise acceleration for a general smooth reaction

The represented higher acceleration is the classical Laplacian minus the
prescribed scalar reaction at every spatial point.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

variable {n k : ℕ} [NeZero n]
variable {f : ℝ → ℝ}

/-- The higher acceleration is the classical Laplacian minus the
pointwise reaction, with no exceptional spatial set. -/
theorem classicalRepresentative_higherSmoothAcceleration (hk : (n : ℝ) < 2 * ((k : ℝ) - 1))
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) (hf0 : f 0 = 0) (hq : (n : ℝ) < 2 * (((k + 2 : ℕ) : ℝ) - 1))
    (q : W^{k + 2,2}(ℝ^n)) (x : ℝ^n) :
    classicalRepresentativeCLM hk (higherSmoothAcceleration hk hs hf0 q) x = Δ
      (classicalRepresentativeCLM hq q : ℝ^n → ℝ) x - f (classicalRepresentativeCLM hq q x) := by
  rw [higherSmoothAcceleration, map_sub, BoundedContinuousFunction.sub_apply,
    classicalRepresentative_higherComposition, classicalRepresentativeCLM_lowerOrderCLM hk hq,
    laplacian_classicalRepresentative hq hk le_rfl]

end PDE.Hyperbolic.NonlinearWave.Cauchy
