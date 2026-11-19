/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Reduction.Equilibria

/-!
# Common state and parameter neighborhoods for a profile graph

Continuity of the linear coordinates and graph gives neighborhoods
before any right state or speed is selected. A physical range bound controls
the augmented orbit; a smaller center rectangle controls the constructed
profile. The argument uses the operator norms of the coordinate equivalence,
since a general eigenbasis is not an isometry.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Choose compatible physical and augmented neighborhoods. The physical
profile radius may subsequently be decreased, allowing a common radius over
all characteristic families. -/
theorem exists_profileGraph_neighborhoods {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (q : E) (e : E ≃L[ℝ] (ι → ℝ)) (k : ι) {φ : (Option ι → ℝ) → (Option ι → ℝ)}
    (hφ : Continuous φ) (hφ0 : φ 0 = 0) {r rconv : ℝ} (hr : 0 < r) (hrconv : 0 < rconv) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ δ η τ : ℝ, 0 < δ ∧ δ < ρ ∧ 0 < η ∧ 0 < τ ∧
      τ < rconv ∧ η ≤ τ ∧
      (∀ u ∈ ball q ρ, ∀ μ ∈ ball 0 η, augmentedProfileCoordinates e (u - q, μ) ∈ ball 0 r) ∧
      (∀ s ∈ Ioo (-τ) τ, ∀ μ ∈ ball 0 η, φ (profileCenterCoordinates k (s, μ)) ∈ ball 0 r ∧
        profileGraph q e k φ (s, μ) ∈ ball q ρ) ∧
      (∀ u ∈ ball q δ, e (u - q) k ∈ Ioo (-τ) τ) := by
  let C := augmentedProfileCoordinates e
  have hCnear : ∀ᶠ z in 𝓝 (0 : E × ℝ), C z ∈ ball 0 r := by
    simpa only [map_zero] using! C.continuous.continuousAt (ball_mem_nhds (C 0) hr)
  obtain ⟨r₀, hr₀, hCball⟩ := Metric.mem_nhds_iff.mp hCnear
  refine ⟨r₀ / 2, half_pos hr₀, fun ρ hρ hρ₀ ↦ ?_⟩
  let G := fun z : ℝ × ℝ ↦ φ (profileCenterCoordinates k z)
  have hG : Continuous G := hφ.comp (profileCenterCoordinates k).continuous
  have hG0 : G 0 = 0 := by simp only [G, map_zero, hφ0]
  have hH : Continuous (profileGraph q e k φ) :=
    continuous_const.add ((profileStateProjection e).continuous.comp hG)
  have hH0 : profileGraph q e k φ 0 = q := by
    simp only [profileGraph, map_zero, hφ0, add_zero]
  have hnear : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ),
      G z ∈ ball 0 r ∧ profileGraph q e k φ z ∈ ball q ρ := by
    have hg : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), G z ∈ ball (G 0) r := hG.continuousAt (ball_mem_nhds (G 0) hr)
    have hh : ∀ᶠ z in 𝓝 (0 : ℝ × ℝ), profileGraph q e k φ z ∈ ball (profileGraph q e k φ 0) ρ :=
      hH.continuousAt (ball_mem_nhds (profileGraph q e k φ 0) hρ)
    simpa only [hG0, hH0] using hg.and hh
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let τ := min a (rconv / 2)
  have hτ : 0 < τ := lt_min ha (half_pos hrconv)
  have hτa : τ ≤ a := min_le_left _ _
  have hτconv : τ < rconv := (min_le_right _ _).trans_lt (half_lt_self hrconv)
  let η := min (r₀ / 2) τ
  have hη : 0 < η := lt_min (half_pos hr₀) hτ
  have hητ : η ≤ τ := min_le_right _ _
  have hA : Continuous (fun u : E ↦ e (u - q) k) :=
    (continuous_apply k).comp (e.continuous.comp (continuous_id.sub continuous_const))
  have hAnear : ∀ᶠ u in 𝓝 q, e (u - q) k ∈ ball 0 τ := by
    simpa only [sub_self, map_zero, Pi.zero_apply] using!
      hA.continuousAt (ball_mem_nhds (e (q - q) k) hτ)
  obtain ⟨d, hd, hdA⟩ := Metric.mem_nhds_iff.mp hAnear
  let δ := min d (ρ / 2)
  have hδ : 0 < δ := lt_min hd (half_pos hρ)
  have hδρ : δ < ρ := (min_le_right _ _).trans_lt (half_lt_self hρ)
  refine ⟨δ, η, τ, hδ, hδρ, hη, hτ, hτconv, hητ, ?_, ?_, ?_⟩
  · intro u hu μ hμ
    apply hCball
    change (u - q, μ) ∈ ball ((0 : E), (0 : ℝ)) r₀
    rw [← ball_prod_same]
    constructor
    · have hu' : u - q ∈ ball 0 ρ := by
        simpa only [mem_ball, dist_eq_norm, sub_zero] using hu
      exact ball_subset_ball (hρ₀.trans (half_le_self hr₀.le)) hu'
    · exact ball_subset_ball ((min_le_left _ _).trans (half_le_self hr₀.le)) hμ
  · intro s hs μ hμ
    apply hball
    apply ball_subset_ball hτa
    change (s, μ) ∈ ball ((0 : ℝ), (0 : ℝ)) τ
    rw [← ball_prod_same]
    refine ⟨?_, ball_subset_ball hητ hμ⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hs
  · intro u hu
    have h := hdA (ball_subset_ball (min_le_left d (ρ / 2)) hu)
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using! h

end PDE.Hyperbolic.ConservationLaw.System
