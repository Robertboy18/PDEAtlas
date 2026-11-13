/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.SmoothMultiplier
public import PDE.DistributionTheory.Distribution.Support.CompactCarrier

/-!
# Support under smooth multiplication

Multiplication by a smooth coefficient preserves every vanishing region of a distribution.
Consequently, it cannot enlarge distributional support and it preserves compact carriers.
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

/-- Multiplication by a smooth coefficient preserves every vanishing region. -/
theorem IsVanishingOn.smoothMultiplierCLM
    {T : 𝓓'((⊤ : Opens E), F)} {s : Set E}
    (hT : IsVanishingOn T s)
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    IsVanishingOn (smoothMultiplierCLM g hg T) s := by
  intro φ hφ
  rw [smoothMultiplierCLM_apply_apply]
  apply hT
  exact (TestFunction.tsupport_smoothMultiplier_subset g hg φ).trans hφ

/-- Multiplication by a smooth coefficient cannot enlarge distributional support. -/
theorem dsupport_smoothMultiplierCLM_subset
    (T : 𝓓'((⊤ : Opens E), F))
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    dsupport (smoothMultiplierCLM g hg T) ⊆ dsupport T :=
  dsupport_subset_dsupport fun _s _hs hT ↦ hT.smoothMultiplierCLM g hg

/-- Multiplication by a smooth coefficient preserves compact carriers. -/
theorem HasCompactCarrier.smoothMultiplierCLM
    {T : 𝓓'((⊤ : Opens E), F)}
    (hT : HasCompactCarrier T)
    (g : E → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    HasCompactCarrier (smoothMultiplierCLM g hg T) := by
  rcases hT with ⟨K, hK, hvan⟩
  exact ⟨K, hK, hvan.smoothMultiplierCLM g hg⟩

end Distribution
