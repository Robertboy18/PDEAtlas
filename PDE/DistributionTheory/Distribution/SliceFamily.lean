/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.SliceFamily.Continuity

/-!
# Continuous application of distributions to fiber slices

Applying a fixed distribution to moving right slices is a continuous linear map between the
canonical LF test-function spaces.
-/

@[expose] public section

open Set TopologicalSpace
open scoped Distributions

noncomputable section

namespace TestFunction

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Apply a fixed distribution to moving right slices as a continuous linear map between the
canonical LF test-function spaces. -/
def applyDistributionToSliceRightCLM
    [FiniteDimensional ℝ E]
    (T : 𝓓'((⊤ : Opens F), G)) :
    𝓓((⊤ : Opens (E × F)), ℝ) →L[ℝ]
      𝓓((⊤ : Opens E), G) :=
  TestFunction.limitCLM ℝ
    (applyDistributionToSliceRight T)
    (fun K _Ksub ↦
      TestFunction.ofSupportedInCLM ℝ (subset_univ _) ∘L
        applyDistributionToSliceRightSupportedCLM T K)
    (by
      intro K _Ksub φ
      ext x
      rfl)

/-- The continuous linear map agrees pointwise with the underlying slice family: at `x` it is
`T` applied to the slice `Φ(x, ·)`. -/
@[simp]
theorem applyDistributionToSliceRightCLM_apply
    [FiniteDimensional ℝ E]
    (T : 𝓓'((⊤ : Opens F), G))
    (Φ : 𝓓((⊤ : Opens (E × F)), ℝ)) :
    applyDistributionToSliceRightCLM T Φ =
      applyDistributionToSliceRight T Φ := by
  ext x
  rfl

end TestFunction
