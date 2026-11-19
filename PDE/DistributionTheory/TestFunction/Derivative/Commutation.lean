/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Commuting directional derivatives of test functions

The symmetry of the second Fréchet derivative gives commutation for the
continuous operators on smooth test functions. No bound on the order of a
distribution is needed when these identities are transposed.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω : Opens E}

/-- Directional differentiation on smooth tests is represented pointwise by the
Fréchet derivative, with no loss of smoothness. -/
theorem lineDerivCLM_apply_eq_fderiv (v : E) (φ : 𝓓(Ω, F)) (x : E) :
    (lineDerivCLM ℝ v φ : 𝓓(Ω, F)) x = fderiv ℝ φ x v := by
  rw [lineDerivCLM_eq_fderivCLM, fderivCLM_apply_of_le φ (by simp)]

/-- Two constant directional derivatives commute on the smooth test
space. The open set is arbitrary. -/
theorem lineDerivCLM_commute (v w : E) :
    Commute (lineDerivCLM ℝ v : 𝓓(Ω, F) →L[ℝ] 𝓓(Ω, F))
      (lineDerivCLM ℝ w) := by
  ext φ x
  change (lineDerivCLM ℝ v (lineDerivCLM ℝ w φ) : 𝓓(Ω, F)) x =
    (lineDerivCLM ℝ w (lineDerivCLM ℝ v φ) : 𝓓(Ω, F)) x
  simp only [lineDerivCLM_apply_eq_fderiv]
  have heq (a : E) :
      (lineDerivCLM ℝ a φ : 𝓓(Ω, F)) = fun y ↦ fderiv ℝ φ y a := by
    funext y
    exact lineDerivCLM_apply_eq_fderiv a φ y
  rw [heq w, heq v]
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (φ.contDiff.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero
  rw [fderiv_clm_apply (hd x) (differentiableAt_const w),
    fderiv_clm_apply (hd x) (differentiableAt_const v)]
  simpa using (φ.contDiff.contDiffAt.isSymmSndFDerivAt (by simp)).eq v w

end TestFunction
