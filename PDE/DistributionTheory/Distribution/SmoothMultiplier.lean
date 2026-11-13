/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution
public import PDE.DistributionTheory.TestFunction.SmoothMultiplier

/-!
# Smooth multipliers of distributions

Multiplication by a smooth scalar coefficient on distributions is the compact-convergence
transpose of the corresponding continuous operator on LF test-function spaces. The
distributional Leibniz rule follows from the test-function Leibniz rule.
-/

@[expose] public section

open TopologicalSpace
open scoped Distributions

noncomputable section

namespace Distribution

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Multiplication of distributions by a fixed smooth scalar coefficient. -/
def smoothMultiplierCLM
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    𝓓'((⊤ : Opens E), F) →L[ℝ] 𝓓'((⊤ : Opens E), F) :=
  (TestFunction.smoothMultiplierCLM g hg).precompCompactConvergenceCLM F

/-- Duality formula `⟨g T, φ⟩ = ⟨T, g φ⟩`: multiplying a distribution by `g` is the transpose of
multiplying test functions by `g`. -/
@[simp]
theorem smoothMultiplierCLM_apply_apply
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (T : 𝓓'((⊤ : Opens E), F)) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    smoothMultiplierCLM g hg T φ =
      T (TestFunction.smoothMultiplierCLM g hg φ) :=
  rfl

/-- Distributional differentiation satisfies the Leibniz rule for smooth multipliers. -/
theorem lineDerivCLM_smoothMultiplierCLM
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v : E) (T : 𝓓'((⊤ : Opens E), F)) :
    lineDerivCLM v (smoothMultiplierCLM g hg T) =
      smoothMultiplierCLM g hg (lineDerivCLM v T) +
        smoothMultiplierCLM (fun x ↦ fderiv ℝ g x v)
          ((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const) T := by
  ext φ
  rw [lineDerivCLM_apply]
  simp only [smoothMultiplierCLM_apply_apply, add_apply]
  rw [lineDerivCLM_apply]
  rw [TestFunction.lineDerivCLM_smoothMultiplierCLM]
  simp

end Distribution
