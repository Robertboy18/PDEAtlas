/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.LocalizedPushforward
public import PDE.DistributionTheory.Distribution.Support.CompactCarrier
import PDE.DistributionTheory.TestFunction.SmoothMultiplier

/-!
# Support under localized pushforward

Localized pushforward along an arbitrary smooth map transports a carrier to its image. If two
cutoffs agree on neighborhoods of that carrier, the resulting pushed distributions coincide.
Consequently, a compactly carried distribution has a well-defined pushforward independent of the
chosen cutoff near its carrier.
-/

@[expose] public section

open Set TopologicalSpace
open scoped Distributions Topology

noncomputable section

namespace Distribution

variable {D E F : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Localized pushforward transports a carrier to its image. -/
theorem IsVanishingOn.pushforwardLocalizedCLM
    {T : 𝓓'((⊤ : Opens D), F)} {K : Set D}
    (hT : IsVanishingOn T Kᶜ)
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ)) :
    IsVanishingOn (pushforwardLocalizedCLM f hf χ T) (f '' K)ᶜ := by
  intro φ hφ
  rw [pushforwardLocalizedCLM_apply_apply]
  apply hT
  intro x hx
  change x ∈ tsupport (fun y ↦ χ y * φ (f y)) at hx
  have hxcomp : x ∈ tsupport (fun y ↦ φ (f y)) :=
    tsupport_mul_subset_right hx
  have hfx : f x ∈ tsupport φ := by
    change x ∈ tsupport (⇑φ ∘ f) at hxcomp
    exact tsupport_comp_subset_preimage φ hf.continuous hxcomp
  exact fun hxK ↦ hφ hfx ⟨x, hxK, rfl⟩

/-- The support of a localized pushforward lies in the image of every compact carrier. -/
theorem dsupport_pushforwardLocalizedCLM_subset_image
    {T : 𝓓'((⊤ : Opens D), F)} {K : Set D}
    (hT : IsVanishingOn T Kᶜ) (hK : IsCompact K)
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ)) :
    dsupport (pushforwardLocalizedCLM f hf χ T) ⊆ f '' K := by
  apply dsupport_subset_of_isVanishingOn_compl
    (hT.pushforwardLocalizedCLM f hf χ)
  exact (hK.image hf.continuous).isClosed

/-- Localized pushforward preserves the existence of a compact carrier. -/
theorem HasCompactCarrier.pushforwardLocalizedCLM
    {T : 𝓓'((⊤ : Opens D), F)}
    (hT : HasCompactCarrier T)
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : 𝓓((⊤ : Opens D), ℝ)) :
    HasCompactCarrier (pushforwardLocalizedCLM f hf χ T) := by
  rcases hT with ⟨K, hK, hvan⟩
  exact ⟨f '' K, hK.image hf.continuous, hvan.pushforwardLocalizedCLM f hf χ⟩

/-- Localized pushforward is independent of cutoffs that agree near a carrier. -/
theorem pushforwardLocalizedCLM_eq_of_eventuallyEq_on
    {T : 𝓓'((⊤ : Opens D), F)} {K : Set D}
    (hT : IsVanishingOn T Kᶜ)
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ ψ : 𝓓((⊤ : Opens D), ℝ))
    (hχψ : ∀ x ∈ K, (χ : D → ℝ) =ᶠ[𝓝 x] (ψ : D → ℝ)) :
    pushforwardLocalizedCLM f hf χ T =
      pushforwardLocalizedCLM f hf ψ T := by
  ext φ
  rw [pushforwardLocalizedCLM_apply_apply, pushforwardLocalizedCLM_apply_apply]
  let φχ := TestFunction.precompLocalized f hf χ φ
  let φψ := TestFunction.precompLocalized f hf ψ φ
  have hsupp : tsupport (φχ - φψ) ⊆ Kᶜ := by
    intro x hx
    by_contra hxK
    have hχψx := hχψ x (by simpa using hxK)
    have hzero : ((φχ - φψ : 𝓓((⊤ : Opens D), ℝ)) : D → ℝ) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hχψx] with y hy
      change χ y * φ (f y) - ψ y * φ (f y) = 0
      rw [hy]
      ring
    exact (notMem_tsupport_iff_eventuallyEq.2 hzero) hx
  have hzero := hT (φχ - φψ) hsupp
  have hsub : T φχ - T φψ = 0 := by
    simpa [map_sub] using hzero
  exact sub_eq_zero.mp hsub

/-- Cutoffs equal to one near a carrier define the same localized pushforward. -/
theorem pushforwardLocalizedCLM_eq_of_eq_one_near
    {T : 𝓓'((⊤ : Opens D), F)} {K : Set D}
    (hT : IsVanishingOn T Kᶜ)
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ ψ : 𝓓((⊤ : Opens D), ℝ))
    (hχ : ∀ x ∈ K, (χ : D → ℝ) =ᶠ[𝓝 x] 1)
    (hψ : ∀ x ∈ K, (ψ : D → ℝ) =ᶠ[𝓝 x] 1) :
    pushforwardLocalizedCLM f hf χ T =
      pushforwardLocalizedCLM f hf ψ T :=
  pushforwardLocalizedCLM_eq_of_eventuallyEq_on hT f hf χ ψ fun x hx ↦
    (hχ x hx).trans (hψ x hx).symm

/-- Localized pushforward is independent of normalized cutoffs even when the
normalizations are given on different carriers of the same distribution. -/
theorem pushforwardLocalizedCLM_eq_of_eq_one_near_carriers
    {T : 𝓓'((⊤ : Opens D), F)} {K L : Set D}
    (hTK : IsVanishingOn T Kᶜ)
    (hTL : IsVanishingOn T Lᶜ)
    (f : D → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ ψ : 𝓓((⊤ : Opens D), ℝ))
    (hχ : ∀ x ∈ K, (χ : D → ℝ) =ᶠ[𝓝 x] 1)
    (hψ : ∀ x ∈ L, (ψ : D → ℝ) =ᶠ[𝓝 x] 1) :
    pushforwardLocalizedCLM f hf χ T =
      pushforwardLocalizedCLM f hf ψ T := by
  ext φ
  rw [pushforwardLocalizedCLM_apply_apply, pushforwardLocalizedCLM_apply_apply]
  let φχ := TestFunction.precompLocalized f hf χ φ
  let φψ := TestFunction.precompLocalized f hf ψ φ
  let φχψ := TestFunction.precompLocalized f hf (TestFunction.mul χ ψ) φ
  have hleft : T (φχ - φχψ) = 0 := by
    apply hTL
    intro x hx
    by_contra hxL
    have hψx := hψ x (by simpa using hxL)
    have hzero :
        ((φχ - φχψ : 𝓓((⊤ : Opens D), ℝ)) : D → ℝ) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hψx] with y hy
      change χ y * φ (f y) - TestFunction.mul χ ψ y * φ (f y) = 0
      simp [hy]
    exact (notMem_tsupport_iff_eventuallyEq.2 hzero) hx
  have hright : T (φψ - φχψ) = 0 := by
    apply hTK
    intro x hx
    by_contra hxK
    have hχx := hχ x (by simpa using hxK)
    have hzero :
        ((φψ - φχψ : 𝓓((⊤ : Opens D), ℝ)) : D → ℝ) =ᶠ[𝓝 x] 0 := by
      filter_upwards [hχx] with y hy
      change ψ y * φ (f y) - TestFunction.mul χ ψ y * φ (f y) = 0
      simp [hy]
    exact (notMem_tsupport_iff_eventuallyEq.2 hzero) hx
  have hχeq : T φχ = T φχψ := by
    exact sub_eq_zero.mp (by simpa [map_sub] using hleft)
  have hψeq : T φψ = T φχψ := by
    exact sub_eq_zero.mp (by simpa [map_sub] using hright)
  exact hχeq.trans hψeq.symm

end Distribution
