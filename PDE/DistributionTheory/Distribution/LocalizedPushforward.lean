/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution
public import PDE.DistributionTheory.TestFunction.LocalizedPrecomposition

/-!
# Localized pushforward of distributions

A fixed compactly supported cutoff turns pullback along an arbitrary smooth map into a continuous
operator on test functions. Transposing that operator gives a continuous map on distributions.

Independence from the cutoff and support transport need a carrier hypothesis on the input
distribution; they are proved in `Distribution/Support/LocalizedPushforward.lean`.
-/

@[expose] public section

open TopologicalSpace
open scoped Distributions

noncomputable section

namespace Distribution

variable {D E F : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Push distributions forward along a smooth map after localizing by a fixed cutoff. -/
def pushforwardLocalizedCLM
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ)) :
    𝓓'((⊤ : Opens D), F) →L[ℝ] 𝓓'((⊤ : Opens E), F) :=
  (TestFunction.precompLocalizedCLM (D := D) (E := E) f hf χ)
    |>.precompCompactConvergenceCLM F

/-- Localized pushforward acts by localized pullback of the test function. -/
@[simp]
theorem pushforwardLocalizedCLM_apply_apply
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ))
    (T : 𝓓'((⊤ : Opens D), F))
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    pushforwardLocalizedCLM f hf χ T φ =
      T (TestFunction.precompLocalized (D := D) (E := E) f hf χ φ) :=
  rfl

end Distribution
