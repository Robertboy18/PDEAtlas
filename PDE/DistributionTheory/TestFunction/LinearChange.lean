/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.TestFunction.ProperPrecomposition
import PDE.DistributionTheory.TestFunction.Derivative.Commutation

/-!
# Linear changes of coordinates for test functions

Invertible continuous linear changes of coordinates preserve compact tests,
transform their supports by inverse image, and intertwine directional derivatives.
-/

@[expose] public noncomputable section

open Set TopologicalSpace
open scoped Distributions

namespace TestFunction

variable {D E : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pullback by an invertible linear change of coordinates. -/
def precompLinearEquiv (e : D ≃L[ℝ] E) :
    𝓓((⊤ : Opens E), ℝ) ≃ₗ[ℝ] 𝓓((⊤ : Opens D), ℝ) where
  toLinearMap := (precompProperCLM e e.contDiff e.toHomeomorph.isProperMap).toLinearMap
  invFun := precompProper e.symm e.symm.contDiff e.symm.toHomeomorph.isProperMap
  left_inv φ := by
    ext x
    change φ (e (e.symm x)) = φ x
    rw [e.apply_symm_apply]
  right_inv φ := by
    ext x
    change φ (e.symm (e x)) = φ x
    rw [e.symm_apply_apply]

/-- Pullback is composition with the change of coordinates. -/
@[simp]
theorem precompLinearEquiv_apply (e : D ≃L[ℝ] E)
    (φ : 𝓓((⊤ : Opens E), ℝ)) (x : D) :
    precompLinearEquiv e φ x = φ (e x) :=
  rfl

/-- The support of a linear pullback lies in the inverse image of the original support. -/
theorem tsupport_precompLinearEquiv_subset (e : D ≃L[ℝ] E)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    tsupport (precompLinearEquiv e φ) ⊆ e ⁻¹' tsupport φ :=
  tsupport_comp_subset_preimage φ e.continuous

/-- Directional differentiation commutes with a linear change of coordinates. -/
theorem lineDerivCLM_precompLinearEquiv (e : D ≃L[ℝ] E) (v : D)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    lineDerivCLM ℝ v (precompLinearEquiv e φ) =
      precompLinearEquiv e (lineDerivCLM ℝ (e v) φ) := by
  ext x
  rw [lineDerivCLM_apply_eq_fderiv, precompLinearEquiv_apply,
    lineDerivCLM_apply_eq_fderiv]
  exact congrArg (fun A : D →L[ℝ] ℝ ↦ A v)
    (((φ.contDiff.differentiable (by simp) (e x)).hasFDerivAt.comp x
      e.hasFDerivAt).fderiv)

end TestFunction
