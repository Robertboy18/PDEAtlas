/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import PDE.Analysis.Geometry.AffineEquiv

/-!
# Affine precomposition on Schwartz space

Precomposition of Schwartz functions by a continuous affine equivalence
combines Mathlib's translation and continuous-linear precomposition operators,
so no separate Schwartz decay estimate is required.
-/

@[expose] public section

noncomputable section

namespace SchwartzMap

variable {𝕜 D E G F : Type*}
variable [RCLike 𝕜]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

/-- Precomposition by a continuous real-affine equivalence as a continuous linear map on
Schwartz space. -/
def compCLMOfContinuousAffineEquiv (A : D ≃ᴬ[ℝ] E) :
    𝓢(E, F) →L[𝕜] 𝓢(D, F) :=
  (compCLMOfContinuousLinearEquiv 𝕜 A.continuousLinearPart).comp
    (compSubConstCLM 𝕜 (-(A 0)))

/-- Precomposition by `A` is literally `φ ∘ A`: writing `A x = L x + A 0` with `L` the linear
part, the translation and linear precomposition operators compose to evaluation at `A x`. -/
@[simp]
theorem compCLMOfContinuousAffineEquiv_apply
    (A : D ≃ᴬ[ℝ] E) (φ : 𝓢(E, F)) (x : D) :
    compCLMOfContinuousAffineEquiv (𝕜 := 𝕜) A φ x = φ (A x) := by
  simp only [compCLMOfContinuousAffineEquiv, ContinuousLinearMap.comp_apply,
    compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, compSubConstCLM_apply,
    sub_neg_eq_add]
  rw [← A.apply_eq_continuousLinearPart_add]

/-- Precomposition by the identity affine map is the identity on Schwartz space. -/
@[simp]
theorem compCLMOfContinuousAffineEquiv_refl :
    compCLMOfContinuousAffineEquiv (𝕜 := 𝕜) (ContinuousAffineEquiv.refl ℝ D) =
      ContinuousLinearMap.id 𝕜 𝓢(D, F) := by
  ext φ x
  simp

/-- Precomposition is contravariantly functorial: pulling back along `B` and then along `A` is
pulling back along `A.trans B` (that is, `B ∘ A`). -/
@[simp]
theorem compCLMOfContinuousAffineEquiv_comp
    (A : D ≃ᴬ[ℝ] E) (B : E ≃ᴬ[ℝ] G) (φ : 𝓢(G, F)) :
    compCLMOfContinuousAffineEquiv (𝕜 := 𝕜) A
        (compCLMOfContinuousAffineEquiv (𝕜 := 𝕜) B φ) =
      compCLMOfContinuousAffineEquiv (𝕜 := 𝕜) (A.trans B) φ := by
  ext x
  simp

end SchwartzMap
