/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.ProperPushforward
public import PDE.DistributionTheory.Distribution.Support.CompactCarrier

/-!
# Support under proper pushforward

If an `F`-valued distribution vanishes outside `K`, then its pushforward along a smooth proper
map `f` vanishes outside `f '' K`. Consequently, closed carriers transport to closed carriers,
distributional support lies in the image carrier, and compact carriers remain compact.

The proof uses Mathlib's support-of-composition inclusion for the pulled-back test function and
the closed-map property of proper maps.
-/

@[expose] public section

open TopologicalSpace
open scoped Distributions

noncomputable section

namespace Distribution

variable {D E F : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Proper pushforward transports a carrier to its image. -/
theorem IsVanishingOn.pushforwardProperCLM
    {T : 𝓓'((⊤ : Opens D), F)} {K : Set D}
    (hT : IsVanishingOn T Kᶜ)
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper : IsProperMap f) :
    IsVanishingOn (pushforwardProperCLM f hf hproper T) (f '' K)ᶜ := by
  intro φ hφ
  rw [pushforwardProperCLM_apply_apply]
  apply hT
  intro x hx
  change x ∈ tsupport (⇑φ ∘ f) at hx
  have hfx : f x ∈ tsupport φ :=
    tsupport_comp_subset_preimage φ hf.continuous hx
  exact fun hxK ↦ hφ hfx ⟨x, hxK, rfl⟩

/-- The support of a proper pushforward lies in the image of every closed carrier. -/
theorem dsupport_pushforwardProperCLM_subset_image
    {T : 𝓓'((⊤ : Opens D), F)} {K : Set D}
    (hT : IsVanishingOn T Kᶜ) (hK : IsClosed K)
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper : IsProperMap f) :
    dsupport (pushforwardProperCLM f hf hproper T) ⊆ f '' K := by
  apply dsupport_subset_of_isVanishingOn_compl
    (hT.pushforwardProperCLM f hf hproper)
  exact hproper.isClosedMap K hK

/-- Proper pushforward preserves the existence of a compact carrier. -/
theorem HasCompactCarrier.pushforwardProperCLM
    {T : 𝓓'((⊤ : Opens D), F)}
    (hT : HasCompactCarrier T)
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hproper : IsProperMap f) :
    HasCompactCarrier (pushforwardProperCLM f hf hproper T) := by
  rcases hT with ⟨K, hK, hvan⟩
  exact ⟨f '' K, hK.image hf.continuous, hvan.pushforwardProperCLM f hf hproper⟩

end Distribution
