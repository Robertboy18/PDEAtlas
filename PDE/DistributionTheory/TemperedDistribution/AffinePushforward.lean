/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Schwartz.Affine
public import PDE.DistributionTheory.TemperedDistribution.Pushforward
public import PDE.DistributionTheory.TemperedDistribution.Translation

/-!
# Affine pushforward of tempered distributions

Pushforward along a continuous real-affine equivalence is the
composition of linear pushforward with translation, so its functoriality, derivative law, and
support transport reuse the corresponding linear and translation results.
-/

@[expose] public section

noncomputable section

open LineDeriv
open scoped SchwartzMap

namespace TemperedDistribution

open Distribution

variable {D E G F : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-- Pushforward of tempered distributions along a continuous real-affine equivalence. -/
def affinePushforwardCLM (A : D ≃ᴬ[ℝ] E) : 𝓢'(D, F) →L[ℂ] 𝓢'(E, F) :=
  (translateCLM (F := F) (-(A 0))).comp
    (pushforwardCLM (F := F) A.continuousLinearPart)

/-- Defining pairing of the affine pushforward: `⟨A_* T, φ⟩ = ⟨T, φ ∘ A⟩`. This unfolds the
composite of translation by `-A 0` and linear pushforward along the linear part of `A`. -/
@[simp]
theorem affinePushforwardCLM_apply_apply
    (A : D ≃ᴬ[ℝ] E) (T : 𝓢'(D, F)) (φ : 𝓢(E, ℂ)) :
    affinePushforwardCLM A T φ =
      T (SchwartzMap.compCLMOfContinuousAffineEquiv (𝕜 := ℂ) A φ) :=
  rfl

/-- Pushforward along the identity affine equivalence is the identity. -/
@[simp]
theorem affinePushforwardCLM_refl :
    affinePushforwardCLM (F := F) (ContinuousAffineEquiv.refl ℝ D) =
      ContinuousLinearMap.id ℂ 𝓢'(D, F) := by
  ext T φ
  simp only [affinePushforwardCLM_apply_apply,
    SchwartzMap.compCLMOfContinuousAffineEquiv_refl, ContinuousLinearMap.id_apply]

/-- Pushforward is covariantly functorial: `B_* (A_* T) = (B ∘ A)_* T`. -/
@[simp]
theorem affinePushforwardCLM_trans
    (A : D ≃ᴬ[ℝ] E) (B : E ≃ᴬ[ℝ] G) (T : 𝓢'(D, F)) :
    affinePushforwardCLM B (affinePushforwardCLM A T) =
      affinePushforwardCLM (A.trans B) T := by
  ext φ
  simp only [affinePushforwardCLM_apply_apply,
    SchwartzMap.compCLMOfContinuousAffineEquiv_comp]

/-- Affine pushforward as a continuous complex-linear equivalence of tempered distributions. -/
def affinePushforwardCLE (A : D ≃ᴬ[ℝ] E) : 𝓢'(D, F) ≃L[ℂ] 𝓢'(E, F) where
  toLinearEquiv :=
    { toFun := affinePushforwardCLM A
      invFun := affinePushforwardCLM A.symm
      left_inv := by
        intro T
        ext φ
        simp only [affinePushforwardCLM_apply_apply]
        congr 1
        ext x
        simp
      right_inv := by
        intro T
        ext φ
        simp only [affinePushforwardCLM_apply_apply]
        congr 1
        ext x
        simp
      map_add' := (affinePushforwardCLM A).map_add
      map_smul' := (affinePushforwardCLM A).map_smul }
  continuous_toFun := (affinePushforwardCLM A).continuous
  continuous_invFun := (affinePushforwardCLM A.symm).continuous

/-- The forward map of the equivalence `affinePushforwardCLE A` is `affinePushforwardCLM A`. -/
@[simp]
theorem affinePushforwardCLE_apply (A : D ≃ᴬ[ℝ] E) (T : 𝓢'(D, F)) :
    affinePushforwardCLE A T = affinePushforwardCLM A T :=
  rfl

/-- The inverse of `affinePushforwardCLE A` is pushforward along `A.symm`. -/
@[simp]
theorem affinePushforwardCLE_symm_apply (A : D ≃ᴬ[ℝ] E) (T : 𝓢'(E, F)) :
    (affinePushforwardCLE A).symm T = affinePushforwardCLM A.symm T :=
  rfl

/-- Directional derivatives transform by the inverse linear part under affine pushforward. -/
@[simp]
theorem lineDerivOp_affinePushforwardCLM
    (A : D ≃ᴬ[ℝ] E) (T : 𝓢'(D, F)) (m : E) :
    ∂_{m} (affinePushforwardCLM A T) =
      affinePushforwardCLM A (∂_{A.continuousLinearPart.symm m} T) := by
  simp [affinePushforwardCLM]

/-- Affine pushforward maps distributional support by the underlying affine equivalence. -/
theorem dsupport_affinePushforwardCLM (A : D ≃ᴬ[ℝ] E) (T : 𝓢'(D, F)) :
    dsupport (affinePushforwardCLM A T) = A '' dsupport T := by
  change
    dsupport (translateCLM (-(A 0)) (pushforwardCLM A.continuousLinearPart T)) =
      A '' dsupport T
  rw [dsupport_translateCLM, dsupport_pushforwardCLM]
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [Homeomorph.subRight_apply, sub_neg_eq_add,
      ← A.apply_eq_continuousLinearPart_add]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨A.continuousLinearPart x, ⟨x, hx, rfl⟩, ?_⟩
    rw [Homeomorph.subRight_apply, sub_neg_eq_add,
      ← A.apply_eq_continuousLinearPart_add]

end TemperedDistribution
