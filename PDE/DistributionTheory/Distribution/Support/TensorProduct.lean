/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.TensorProduct
public import PDE.DistributionTheory.Distribution.Support.CompactCarrier

/-!
# Support of tensor products of distributions

Vanishing of either tensor factor propagates to the corresponding product
region. Applying these two transport laws to open neighborhoods outside the
factor supports proves that the support of a distribution tensor product is
contained in the product of the factor supports.
-/

@[expose] public section

open Set TopologicalSpace
open scoped Distributions Topology

noncomputable section

namespace Distribution

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Vanishing of the first factor propagates to the corresponding product region. -/
theorem IsVanishingOn.tensorProduct_left
    {S : 𝓓'((⊤ : Opens E), ℝ)}
    {T : 𝓓'((⊤ : Opens F), ℝ)}
    {U : Set E}
    (hS : IsVanishingOn S U) :
    IsVanishingOn (tensorProduct S T) (U ×ˢ (univ : Set F)) := by
  intro Φ hΦ
  rw [tensorProduct_apply]
  apply hS
  refine (TestFunction.tsupport_applyDistributionToSliceRight_subset T Φ).trans ?_
  rintro x ⟨p, hp, rfl⟩
  exact (hΦ hp).1

/-- Vanishing of the second factor propagates to the corresponding product region. -/
theorem IsVanishingOn.tensorProduct_right
    {S : 𝓓'((⊤ : Opens E), ℝ)}
    {T : 𝓓'((⊤ : Opens F), ℝ)}
    {V : Set F}
    (hT : IsVanishingOn T V) :
    IsVanishingOn (tensorProduct S T) ((univ : Set E) ×ˢ V) := by
  intro Φ hΦ
  rw [tensorProduct_apply]
  suffices TestFunction.applyDistributionToSliceRight T Φ = 0 by
    rw [this, map_zero]
  ext x
  rw [TestFunction.applyDistributionToSliceRight_apply]
  apply hT
  refine (TestFunction.tsupport_sliceRight_subset x Φ).trans ?_
  intro y hy
  exact (hΦ hy).2

/-- The support of a tensor product is contained in the product of the factor supports. -/
theorem dsupport_tensorProduct_subset
    (S : 𝓓'((⊤ : Opens E), ℝ))
    (T : 𝓓'((⊤ : Opens F), ℝ)) :
    dsupport (tensorProduct S T) ⊆ dsupport S ×ˢ dsupport T := by
  intro p hp
  by_contra hprod
  have hfactor : p.1 ∉ dsupport S ∨ p.2 ∉ dsupport T := by
    simpa only [Set.mem_prod, not_and_or] using hprod
  rcases hfactor with hx | hy
  · obtain ⟨U, hSU, hU, hxU⟩ := (notMem_dsupport_iff p.1).mp hx
    have hnot : p ∉ dsupport (tensorProduct S T) :=
      (notMem_dsupport_iff p).mpr
        ⟨U ×ˢ (univ : Set F), hSU.tensorProduct_left,
          hU.prod isOpen_univ, ⟨hxU, mem_univ p.2⟩⟩
    exact hnot hp
  · obtain ⟨V, hTV, hV, hyV⟩ := (notMem_dsupport_iff p.2).mp hy
    have hnot : p ∉ dsupport (tensorProduct S T) :=
      (notMem_dsupport_iff p).mpr
        ⟨(univ : Set E) ×ˢ V, hTV.tensorProduct_right,
          isOpen_univ.prod hV, ⟨mem_univ p.1, hyV⟩⟩
    exact hnot hp

/-- The product of two compact carriers is a carrier for the tensor product. -/
theorem IsVanishingOn.tensorProduct_compl
    {S : 𝓓'((⊤ : Opens E), ℝ)}
    {T : 𝓓'((⊤ : Opens F), ℝ)}
    {K : Set E} {L : Set F}
    (hK : IsCompact K) (hL : IsCompact L)
    (hS : IsVanishingOn S Kᶜ)
    (hT : IsVanishingOn T Lᶜ) :
    IsVanishingOn (tensorProduct S T) (K ×ˢ L)ᶜ := by
  intro Φ hΦ
  rw [tensorProduct_apply]
  apply hS
  have hKL : K ×ˢ L ⊆ (tsupport Φ)ᶜ := by
    intro p hp hpΦ
    exact hΦ hpΦ hp
  obtain ⟨U, V, hU, hV, hKU, hLV, hUV⟩ :=
    generalized_tube_lemma hK hL
      (isOpen_compl_iff.mpr (isClosed_tsupport _)) hKL
  intro x hx
  by_contra hxK
  have hxU : x ∈ U := hKU (by simpa using hxK)
  have hzero :
      (TestFunction.applyDistributionToSliceRight T Φ : E → ℝ) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hU.mem_nhds hxU] with z hzU
    rw [TestFunction.applyDistributionToSliceRight_apply]
    apply hT
    refine (TestFunction.tsupport_sliceRight_subset z Φ).trans ?_
    intro y hy
    by_contra hyL
    exact hUV ⟨hzU, hLV (by simpa using hyL)⟩ hy
  exact (notMem_tsupport_iff_eventuallyEq.2 hzero) hx

/-- The product of compact carriers is a compact carrier for the tensor product. -/
theorem HasCompactCarrier.tensorProduct
    {S : 𝓓'((⊤ : Opens E), ℝ)}
    {T : 𝓓'((⊤ : Opens F), ℝ)}
    (hS : HasCompactCarrier S)
    (hT : HasCompactCarrier T) :
    HasCompactCarrier (tensorProduct S T) := by
  rcases hS with ⟨K, hK, hSK⟩
  rcases hT with ⟨L, hL, hTL⟩
  exact ⟨K ×ˢ L, hK.prod hL,
    IsVanishingOn.tensorProduct_compl hK hL hSK hTL⟩

end Distribution
