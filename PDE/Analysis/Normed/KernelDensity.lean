/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Dense regular vectors with a scalar constraint

A dense linear subspace remains dense after imposing a continuous scalar linear
constraint, when density is measured inside the constraint's kernel. A fixed
regular vector corrects the constraint without changing the limiting state.

This is useful for Galerkin approximations with a normalization: the approximating
vectors can satisfy the normalization exactly at every finite stage.
-/

@[expose] public section

namespace Submodule

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Intersecting a dense linear subspace with the kernel of a continuous scalar
functional gives a dense subspace of that kernel. -/
theorem dense_comap_ker (D : Submodule 𝕜 E) (hD : Dense (D : Set E))
    (L : E →L[𝕜] 𝕜) :
    Dense (D.comap L.ker.subtype : Set L.ker) := by
  classical
  by_cases hzero : L = 0
  · let P : E →L[𝕜] L.ker := (ContinuousLinearMap.id 𝕜 E).codRestrict L.ker
      (fun x ↦ by simp [hzero])
    have hP : Function.Surjective P := by
      intro x
      exact ⟨x, Subtype.ext rfl⟩
    refine Dense.mono ?_ (hP.denseRange.comp hD.denseRange_val P.continuous)
    rintro _ ⟨d, rfl⟩
    exact d.property
  · have hnonzero : ∃ c : D, L c ≠ 0 := by
      by_contra! hc
      apply hzero
      apply ContinuousLinearMap.ext
      have heq : (fun x : E ↦ L x) = (fun _ ↦ 0) :=
        hD.denseRange_val.equalizer L.continuous continuous_const (funext hc)
      exact fun x ↦ congrFun heq x
    obtain ⟨c, hc⟩ := hnonzero
    let correction : E := (L c)⁻¹ • (c : E)
    have hcorrection : L correction = 1 := by
      simp [correction, hc]
    let Q : E →L[𝕜] E := ContinuousLinearMap.id 𝕜 E - L.smulRight correction
    have hQ (x : E) : Q x ∈ L.ker := by
      change L (x - L x • correction) = 0
      simp [hcorrection]
    let P : E →L[𝕜] L.ker := Q.codRestrict L.ker hQ
    have hP : Function.Surjective P := by
      intro x
      refine ⟨x, Subtype.ext ?_⟩
      change (x : E) - L x • correction = x
      simp [show L x = 0 from x.property]
    refine Dense.mono ?_ (hP.denseRange.comp hD.denseRange_val P.continuous)
    rintro _ ⟨d, rfl⟩
    change (d : E) - L d • correction ∈ D
    exact D.sub_mem d.property (D.smul_mem _ (D.smul_mem _ c.property))

end Submodule
