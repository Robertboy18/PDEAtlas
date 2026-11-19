/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Smooth multipliers of test functions

A fixed smooth scalar coefficient acts continuously on the canonical LF space of test functions.
Mathlib proves continuity on every fixed compact-support stage through
`ContDiffMapSupportedIn.bilinLeftCLM`, and `TestFunction.limitCLM` lifts those operators to the
LF space.

The pointwise product of two test functions and its Leibniz rule are special cases of the
smooth-multiplier operator.
-/

@[expose] public section

open Set TopologicalSpace
open scoped Distributions

noncomputable section

namespace TestFunction

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Multiply a test function by a fixed smooth scalar coefficient. -/
def smoothMultiplier
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (φ : 𝓓((⊤ : Opens E), ℝ)) : 𝓓((⊤ : Opens E), ℝ) where
  toFun := fun x ↦ g x * φ x
  contDiff' := hg.mul φ.contDiff
  hasCompactSupport' := φ.hasCompactSupport.mul_left
  tsupport_subset' := subset_univ _

/-- Pointwise formula for the multiplied test function: `(g φ)(x) = g x * φ x`. -/
@[simp]
theorem smoothMultiplier_apply
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (φ : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    smoothMultiplier g hg φ x = g x * φ x :=
  rfl

/-- Multiplication by a fixed smooth coefficient as a continuous linear map of LF test-function
spaces. -/
def smoothMultiplierCLM
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    𝓓((⊤ : Opens E), ℝ) →L[ℝ] 𝓓((⊤ : Opens E), ℝ) :=
  TestFunction.limitCLM ℝ
    (smoothMultiplier g hg)
    (fun _K _Ksub ↦
      TestFunction.ofSupportedInCLM ℝ (subset_univ _) ∘L
        ContDiffMapSupportedIn.bilinLeftCLM
          (ContinuousLinearMap.lsmul ℝ ℝ).flip hg)
    (by
      intro K _Ksub φ
      ext x
      rfl)

/-- The continuous linear multiplier agrees with the plain product `smoothMultiplier g hg φ`. -/
@[simp]
theorem smoothMultiplierCLM_apply
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    smoothMultiplierCLM g hg φ = smoothMultiplier g hg φ := by
  ext x
  rfl

/-- Multiplication by a smooth coefficient does not enlarge topological support. -/
theorem tsupport_smoothMultiplier_subset
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (φ : 𝓓((⊤ : Opens E), ℝ)) :
    tsupport (smoothMultiplierCLM g hg φ) ⊆ tsupport φ := by
  change tsupport (fun x ↦ g x * φ x) ⊆ tsupport (fun x ↦ φ x)
  exact tsupport_mul_subset_right

/-- Directional differentiation satisfies the Leibniz rule for smooth multipliers. -/
theorem lineDerivCLM_smoothMultiplierCLM
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v : E) (φ : 𝓓((⊤ : Opens E), ℝ)) :
    lineDerivCLM ℝ v (smoothMultiplierCLM g hg φ) =
      smoothMultiplierCLM g hg (lineDerivCLM ℝ v φ) +
        smoothMultiplierCLM (fun x ↦ fderiv ℝ g x v)
          ((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const) φ := by
  ext x
  change fderiv ℝ (fun y ↦ g y * φ y) x v =
    g x * fderiv ℝ (fun y ↦ φ y) x v +
      fderiv ℝ g x v * φ x
  rw [fderiv_fun_mul
    ((hg.differentiable (by simp)).differentiableAt)
    ((φ.contDiff.differentiable (by simp)).differentiableAt)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Pointwise multiplication of test functions. -/
def mul
    (φ ψ : 𝓓((⊤ : Opens E), ℝ)) : 𝓓((⊤ : Opens E), ℝ) :=
  smoothMultiplierCLM (fun x ↦ φ x) φ.contDiff ψ

/-- Pointwise formula for the product of two test functions. -/
@[simp]
theorem mul_apply
    (φ ψ : 𝓓((⊤ : Opens E), ℝ)) (x : E) :
    mul φ ψ x = φ x * ψ x :=
  rfl

/-- Directional differentiation satisfies the Leibniz rule on test functions. -/
theorem lineDerivCLM_mul
    (v : E) (φ ψ : 𝓓((⊤ : Opens E), ℝ)) :
    lineDerivCLM ℝ v (mul φ ψ) =
      mul (lineDerivCLM ℝ v φ) ψ +
        mul φ (lineDerivCLM ℝ v ψ) := by
  rw [mul, lineDerivCLM_smoothMultiplierCLM]
  ext x
  change
    φ x * (lineDerivCLM ℝ v ψ) x +
        fderiv ℝ (fun y ↦ φ y) x v * ψ x =
      (lineDerivCLM ℝ v φ) x * ψ x +
        φ x * (lineDerivCLM ℝ v ψ) x
  rw [lineDerivCLM_apply_of_le (by simp),
    lineDerivCLM_apply_of_le (by simp)]
  rw [(φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  ring

end TestFunction
