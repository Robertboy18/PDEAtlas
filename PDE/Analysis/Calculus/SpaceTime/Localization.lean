/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean.SpaceTime
public import PDE.DistributionTheory.TestFunction.CompactCutoff
import PDE.FDeriv.SpaceTime

/-!
# Compact localization with separate spatial regularity

Multiplication by a smooth cutoff preserves both joint regularity and the
regularity of each spatial slice. The cutoff is supported inside the original
open set and equals one near a prescribed compact subset. No regularity of the
original function outside that open set is required.
-/

@[expose] public section

namespace PDE.Analysis

open Filter Function Set
open PDE.Common
open scoped Topology Distributions

variable {n : ℕ}

/-- A compactly supported representative can preserve different joint and spatial
regularity orders, while agreeing with the original field near a compact set. -/
theorem exists_contDiff_compactSupport_eventuallyEq_of_contDiffOn_slices
    {m k : ℕ∞} {u : SpaceTime n → ℝ} {Ω K : Set (SpaceTime n)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hu : ContDiffOn ℝ m u Ω)
    (huSpace : ∀ s, ContDiffOn ℝ k (fun y ↦ u (timeSpaceCons s y))
      ((timeSpaceCons s) ⁻¹' Ω)) :
    ∃ v : SpaceTime n → ℝ, ContDiff ℝ m v ∧
      (∀ s, ContDiff ℝ k (fun y ↦ v (timeSpaceCons s y))) ∧
      HasCompactSupport v ∧ ∀ p ∈ K, v =ᶠ[𝓝 p] u := by
  obtain ⟨ψ, hψΩ, _, hψOne, _⟩ :=
    TestFunction.exists_eq_one_on_compact_finiteDimensional hΩ hK hKΩ
  let v : SpaceTime n → ℝ := fun p ↦ ψ.toFun p * u p
  have hzero {p : SpaceTime n} (hp : p ∉ tsupport ψ.toFun) :
      v =ᶠ[𝓝 p] 0 := by
    filter_upwards [(isClosed_tsupport ψ.toFun).isOpen_compl.mem_nhds hp] with q hq
    simp only [v, image_eq_zero_of_notMem_tsupport hq, zero_mul, Pi.zero_apply]
  refine ⟨v, ?_, ?_, ψ.hasCompactSupport.mul_right, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ tsupport ψ.toFun
    · exact (ψ.contDiff.of_le (by simp)).contDiffAt.mul
        (hu.contDiffAt (hΩ.mem_nhds (hψΩ hp)))
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero hp)
  · intro s
    rw [contDiff_iff_contDiffAt]
    intro y
    have hcons : ContDiff ℝ k (timeSpaceCons s : ℝ^n → SpaceTime n) :=
      contDiff_timeSpaceCons_spatial n s
    by_cases hy : timeSpaceCons s y ∈ tsupport ψ.toFun
    · exact ((ψ.contDiff.of_le (by simp)).comp hcons).contDiffAt.mul
        ((huSpace s).contDiffAt
          ((hΩ.preimage hcons.continuous).mem_nhds (hψΩ hy)))
    · exact contDiffAt_const.congr_of_eventuallyEq
        ((hzero hy).comp_tendsto hcons.continuous.continuousAt)
  · intro p hp
    filter_upwards [hψOne p hp] with q hq
    simp only [v, hq, Pi.one_apply, one_mul]

end PDE.Analysis
