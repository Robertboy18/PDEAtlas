/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Support

/-!
# Translation of tempered distributions

Translation on tempered distributions is the transpose of translation on Schwartz
functions. The convention agrees with LeanPDE's translation on function spaces: translation by
`a` corresponds to `u(x + a)` for a regular distribution induced by a function `u`.
-/

@[expose] public section

noncomputable section

open Distribution
open LineDeriv
open scoped SchwartzMap

namespace TemperedDistribution

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-- Translation by `a` on tempered distributions, obtained by transposing the Schwartz-space map
`φ ↦ (x ↦ φ (x - a))`. -/
def translateCLM (a : E) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  PointwiseConvergenceCLM.precomp F (SchwartzMap.compSubConstCLM ℂ a)

/-- Defining pairing of translation: `⟨τₐ T, φ⟩ = ⟨T, φ(· - a)⟩`. For a regular distribution `u`
this is `∫ u(x) φ(x − a) dx = ∫ u(y + a) φ(y) dy`, so `τₐ u = u(· + a)`. -/
@[simp]
theorem translateCLM_apply_apply (a : E) (T : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    translateCLM a T φ = T (φ.compSubConstCLM ℂ a) :=
  rfl

/-- Translation by `0` is the identity. -/
@[simp]
theorem translateCLM_zero :
    translateCLM (F := F) (0 : E) = ContinuousLinearMap.id ℂ 𝓢'(E, F) := by
  ext T φ
  simp

/-- Translations compose additively: `τₐ (τ_b T) = τ_{a+b} T`. -/
@[simp]
theorem translateCLM_apply_translateCLM (a b : E) (T : 𝓢'(E, F)) :
    translateCLM a (translateCLM b T) = translateCLM (a + b) T := by
  ext φ
  simp

/-- Translation by `a` as a continuous linear equivalence of tempered distributions. Its inverse
is translation by `-a`. -/
def translateCLE (a : E) : 𝓢'(E, F) ≃L[ℂ] 𝓢'(E, F) where
  toLinearEquiv :=
    { toFun := translateCLM a
      invFun := translateCLM (-a)
      left_inv := by
        intro T
        simp
      right_inv := by
        intro T
        simp
      map_add' := (translateCLM a).map_add
      map_smul' := (translateCLM a).map_smul }
  continuous_toFun := (translateCLM a).continuous
  continuous_invFun := (translateCLM (-a)).continuous

/-- The forward map of the equivalence `translateCLE a` is `translateCLM a`. -/
@[simp]
theorem translateCLE_apply (a : E) (T : 𝓢'(E, F)) :
    translateCLE a T = translateCLM a T :=
  rfl

/-- The inverse of `translateCLE a` is translation by `-a`. -/
@[simp]
theorem translateCLE_symm_apply (a : E) (T : 𝓢'(E, F)) :
    (translateCLE a).symm T = translateCLM (-a) T :=
  rfl

/-- Distributional directional derivatives commute with translation. -/
@[simp]
theorem lineDerivOp_translateCLM (a m : E) (T : 𝓢'(E, F)) :
    ∂_{m} (translateCLM a T) = translateCLM a (∂_{m} T) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, translateCLM_apply_apply,
    map_neg]
  apply congrArg (fun z : F ↦ -z)
  apply congrArg T
  ext x
  simp only [SchwartzMap.compSubConstCLM_apply]
  rw [SchwartzMap.lineDerivOp_apply, SchwartzMap.lineDerivOp_apply]
  rw [φ.differentiableAt.lineDeriv_eq_fderiv,
    ((φ.compSubConstCLM ℂ a).differentiableAt).lineDeriv_eq_fderiv]
  change (fderiv ℝ (⇑φ) (x - a)) m =
    (fderiv ℝ (fun y : E ↦ φ (y - a)) x) m
  rw [fderiv_comp_sub]

/-- A translated distribution vanishes on a set exactly when the original distribution vanishes
on its preimage under `x ↦ x - a`. -/
theorem isVanishingOn_translateCLM_iff (a : E) (T : 𝓢'(E, F)) (s : Set E) :
    IsVanishingOn (translateCLM a T) s ↔
      IsVanishingOn T ((Homeomorph.subRight a) ⁻¹' s) := by
  constructor
  · intro h ψ hψ
    let φ : 𝓢(E, ℂ) := ψ.compSubConstCLM ℂ (-a)
    have hφ : tsupport φ ⊆ s := by
      change tsupport (ψ ∘ (fun x ↦ x - (-a))) ⊆ s
      have hts :
          tsupport (ψ ∘ (fun x ↦ x - (-a))) =
            (Homeomorph.subRight (-a)) ⁻¹' tsupport ψ := by
        simpa using tsupport_comp_eq_preimage ψ (Homeomorph.subRight (-a))
      rw [hts]
      intro x hx
      have hψx : x - (-a) ∈ (Homeomorph.subRight a) ⁻¹' s :=
        hψ hx
      simpa using hψx
    have hz := h φ hφ
    change T _ = 0 at hz
    have hcomp : φ.compSubConstCLM ℂ a = ψ := by
      ext x
      simp [φ]
    simpa [hcomp] using hz
  · intro h φ hφ
    apply h (φ.compSubConstCLM ℂ a)
    change tsupport (φ ∘ (fun x ↦ x - a)) ⊆ (Homeomorph.subRight a) ⁻¹' s
    have hts :
        tsupport (φ ∘ (fun x ↦ x - a)) =
          (Homeomorph.subRight a) ⁻¹' tsupport φ := by
      simpa using tsupport_comp_eq_preimage φ (Homeomorph.subRight a)
    rw [hts]
    exact Set.preimage_mono hφ

/-- Translation carries distributional support by the geometric translation `x ↦ x - a`. -/
theorem dsupport_translateCLM (a : E) (T : 𝓢'(E, F)) :
    dsupport (translateCLM a T) = (Homeomorph.subRight a) '' dsupport T := by
  ext y
  have hmem :
      y ∈ dsupport (translateCLM a T) ↔ y + a ∈ dsupport T := by
    simp only [mem_dsupport_iff_not_isVanishingOn]
    constructor
    · intro hy s hys hs
      let u := (Homeomorph.subRight (-a)) ⁻¹' s
      have hyu : y ∈ u := by simpa [u] using hys
      have hu : IsOpen u := hs.preimage (Homeomorph.subRight (-a)).continuous
      intro hvan
      have hpre : (Homeomorph.subRight a) ⁻¹' u = s := by
        ext x
        simp [u]
      apply hy u hyu hu
      apply (isVanishingOn_translateCLM_iff a T u).mpr
      simpa only [hpre] using hvan
    · intro hy s hys hs
      let u := (Homeomorph.subRight a) ⁻¹' s
      have hyu : y + a ∈ u := by simpa [u] using hys
      have hu : IsOpen u := hs.preimage (Homeomorph.subRight a).continuous
      intro hvan
      exact hy u hyu hu ((isVanishingOn_translateCLM_iff a T s).mp hvan)
  constructor
  · intro hy
    exact ⟨y + a, hmem.mp hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    apply hmem.mpr
    simpa using hx

end TemperedDistribution
