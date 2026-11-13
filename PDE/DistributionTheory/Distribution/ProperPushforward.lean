/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution
public import PDE.DistributionTheory.TestFunction.ProperPrecomposition

/-!
# Proper pushforward of distributions

A smooth proper map `f : D → E` pulls test functions on `E` back continuously to test functions
on `D`. Transposing that pullback gives a continuous pushforward from `F`-valued distributions on
`D` to `F`-valued distributions on `E`.

The properness hypothesis is what preserves compact support of test functions. Continuity for the
LF test-function topology comes from `TestFunction.precompProperCLM`; here we apply Mathlib's
compact-convergence transpose and prove the action and functoriality laws.
-/

@[expose] public section

open Function TopologicalSpace
open scoped Distributions

noncomputable section

namespace Distribution

variable {D E G F : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Push `F`-valued distributions forward along a smooth proper map. -/
def pushforwardProperCLM
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper : IsProperMap f) :
    𝓓'((⊤ : Opens D), F) →L[ℝ] 𝓓'((⊤ : Opens E), F) :=
  (TestFunction.precompProperCLM f hf hproper).precompCompactConvergenceCLM F

/-- Proper pushforward acts by pulling the test function back. -/
@[simp]
theorem pushforwardProperCLM_apply_apply
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper : IsProperMap f)
    (T : 𝓓'((⊤ : Opens D), F)) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    pushforwardProperCLM f hf hproper T φ =
      T (TestFunction.precompProper f hf hproper φ) := by
  rfl

/-- Pushing a distribution forward along the identity map does nothing. -/
@[simp]
theorem pushforwardProperCLM_id
    (T : 𝓓'((⊤ : Opens D), F)) :
    pushforwardProperCLM (id : D → D) contDiff_id isProperMap_id T = T := by
  ext φ
  rfl

/-- Proper pushforward is functorial under composition. -/
@[simp]
theorem pushforwardProperCLM_comp
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper_f : IsProperMap f)
    (g : E → G) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hproper_g : IsProperMap g)
    (T : 𝓓'((⊤ : Opens D), F)) :
    pushforwardProperCLM g hg hproper_g
        (pushforwardProperCLM f hf hproper_f T) =
      pushforwardProperCLM (g ∘ f) (hg.comp hf) (hproper_g.comp hproper_f) T := by
  ext φ
  rfl

end Distribution
