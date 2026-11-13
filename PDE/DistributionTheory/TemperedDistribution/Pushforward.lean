/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Support

/-!
# Linear pushforward of tempered distributions

For a continuous real-linear equivalence `A : D ≃L[ℝ] E`, precomposition `φ ↦ φ ∘ A` is a
continuous linear map `𝓢(E, ℂ) → 𝓢(D, ℂ)` (Mathlib's `compCLMOfContinuousLinearEquiv`), and
its transpose is the pushforward

`⟨A_* T, φ⟩ = ⟨T, φ ∘ A⟩`

from `𝓢'(D, F)` to `𝓢'(E, F)`. When `D = E = ℝ^n` and `T` is the regular distribution of an
integrable function `u`, `A_* T` is the regular distribution of `|det A|⁻¹ · u ∘ A⁻¹`, the image
of the measure `u dx` under `A`; the pairing above is the definition that makes sense for every
distribution.

## Main results

* `pushforwardCLM`, `pushforwardCLE`: the pushforward as a continuous linear map and as a
  continuous linear equivalence, with inverse the pushforward along `A.symm`.
* `pushforwardCLM_refl`, `pushforwardCLM_trans`: functoriality.
* `lineDerivOp_pushforwardCLM`: `∂_m (A_* T) = A_* (∂_{A⁻¹ m} T)`, the chain rule in dual form.
* `isVanishingOn_pushforwardCLM_iff`, `dsupport_pushforwardCLM`: `A_* T` vanishes on `s` iff `T`
  vanishes on `A⁻¹ s`, so `supp (A_* T) = A (supp T)`.
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

/-- Pushforward of tempered distributions along a continuous real-linear equivalence. -/
def pushforwardCLM (A : D ≃L[ℝ] E) : 𝓢'(D, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A)

/-- Defining pairing of the pushforward: `⟨A_* T, φ⟩ = ⟨T, φ ∘ A⟩`. -/
@[simp]
theorem pushforwardCLM_apply_apply (A : D ≃L[ℝ] E) (T : 𝓢'(D, F)) (φ : 𝓢(E, ℂ)) :
    pushforwardCLM A T φ = T (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A φ) :=
  rfl

/-- Pushforward along the identity is the identity. -/
@[simp]
theorem pushforwardCLM_refl :
    pushforwardCLM (F := F) (ContinuousLinearEquiv.refl ℝ D) =
      ContinuousLinearMap.id ℂ 𝓢'(D, F) := by
  ext T φ
  rfl

/-- Pushforward is covariantly functorial: `B_* (A_* T) = (B ∘ A)_* T`. -/
@[simp]
theorem pushforwardCLM_trans (A : D ≃L[ℝ] E) (B : E ≃L[ℝ] G) (T : 𝓢'(D, F)) :
    pushforwardCLM B (pushforwardCLM A T) = pushforwardCLM (A.trans B) T := by
  ext φ
  rfl

/-- Pushforward along a continuous real-linear equivalence as a continuous complex-linear
equivalence on tempered distributions. -/
def pushforwardCLE (A : D ≃L[ℝ] E) : 𝓢'(D, F) ≃L[ℂ] 𝓢'(E, F) where
  toLinearEquiv :=
    { toFun := pushforwardCLM A
      invFun := pushforwardCLM A.symm
      left_inv := by
        intro T
        ext φ
        change T _ = T φ
        congr 1
        ext x
        simp
      right_inv := by
        intro T
        ext φ
        change T _ = T φ
        congr 1
        ext x
        simp
      map_add' := (pushforwardCLM A).map_add
      map_smul' := (pushforwardCLM A).map_smul }
  continuous_toFun := (pushforwardCLM A).continuous
  continuous_invFun := (pushforwardCLM A.symm).continuous

/-- The forward map of the equivalence `pushforwardCLE A` is `pushforwardCLM A`. -/
@[simp]
theorem pushforwardCLE_apply (A : D ≃L[ℝ] E) (T : 𝓢'(D, F)) :
    pushforwardCLE A T = pushforwardCLM A T :=
  rfl

/-- The inverse of `pushforwardCLE A` is pushforward along `A.symm`. -/
@[simp]
theorem pushforwardCLE_symm_apply (A : D ≃L[ℝ] E) (T : 𝓢'(E, F)) :
    (pushforwardCLE A).symm T = pushforwardCLM A.symm T :=
  rfl

/-- Directional derivatives transform contravariantly under linear pushforward. -/
@[simp]
theorem lineDerivOp_pushforwardCLM (A : D ≃L[ℝ] E) (T : 𝓢'(D, F)) (m : E) :
    ∂_{m} (pushforwardCLM A T) = pushforwardCLM A (∂_{A.symm m} T) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, pushforwardCLM_apply_apply,
    map_neg]
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
  simp

/-- A pushforward vanishes on a set exactly when the original distribution vanishes on its
preimage. -/
theorem isVanishingOn_pushforwardCLM_iff
    (A : D ≃L[ℝ] E) (T : 𝓢'(D, F)) (s : Set E) :
    IsVanishingOn (pushforwardCLM A T) s ↔ IsVanishingOn T (A ⁻¹' s) := by
  constructor
  · intro h ψ hψ
    let φ : 𝓢(E, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm ψ
    have hφ : tsupport φ ⊆ s := by
      change tsupport (ψ ∘ A.symm) ⊆ s
      have hts :
          tsupport (ψ ∘ A.symm) = A.symm ⁻¹' tsupport ψ := by
        simpa using tsupport_comp_eq_preimage ψ A.symm.toHomeomorph
      rw [hts]
      intro x hx
      simpa using hψ hx
    have hz := h φ hφ
    change T _ = 0 at hz
    have hcomp :
        SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A
            (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm ψ) = ψ := by
      ext x
      simp
    simpa [φ, hcomp] using hz
  · intro h φ hφ
    apply h (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A φ)
    change tsupport (φ ∘ A) ⊆ A ⁻¹' s
    have hts : tsupport (φ ∘ A) = A ⁻¹' tsupport φ := by
      simpa using tsupport_comp_eq_preimage φ A.toHomeomorph
    rw [hts]
    exact Set.preimage_mono hφ

/-- Pointwise complement-of-support characterization under linear pushforward. -/
theorem notMem_dsupport_pushforwardCLM_iff
    (A : D ≃L[ℝ] E) (T : 𝓢'(D, F)) (y : E) :
    y ∉ dsupport (pushforwardCLM A T) ↔ A.symm y ∉ dsupport T := by
  rw [notMem_dsupport_iff, notMem_dsupport_iff]
  constructor
  · rintro ⟨s, hs, hopen, hy⟩
    refine ⟨A ⁻¹' s, ?_, hopen.preimage A.continuous, ?_⟩
    · exact (isVanishingOn_pushforwardCLM_iff A T s).mp hs
    · simpa using hy
  · rintro ⟨s, hs, hopen, hy⟩
    let u : Set E := A.symm ⁻¹' s
    refine ⟨u, ?_, hopen.preimage A.symm.continuous, hy⟩
    have hpre : A ⁻¹' u = s := by
      ext x
      simp [u]
    apply (isVanishingOn_pushforwardCLM_iff A T u).mpr
    simpa only [hpre] using hs

/-- Linear pushforward maps the distributional support by the underlying equivalence. -/
theorem dsupport_pushforwardCLM (A : D ≃L[ℝ] E) (T : 𝓢'(D, F)) :
    dsupport (pushforwardCLM A T) = A '' dsupport T := by
  ext y
  have hnot :
      y ∉ dsupport (pushforwardCLM A T) ↔ A.symm y ∉ dsupport T :=
    notMem_dsupport_pushforwardCLM_iff A T y
  have hmem : y ∈ dsupport (pushforwardCLM A T) ↔ A.symm y ∈ dsupport T := by
    constructor
    · intro hy
      by_contra hAy
      exact hnot.mpr hAy hy
    · intro hAy
      by_contra hy
      exact hnot.mp hy hAy
  rw [hmem]
  constructor
  · intro hy
    exact ⟨A.symm y, hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    simpa

end TemperedDistribution
