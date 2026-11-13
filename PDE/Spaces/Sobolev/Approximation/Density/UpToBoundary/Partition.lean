/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.DefiningFunction
public import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# A finite partition for inward mollification

Compactness of the closure of a bounded C¹ domain reduces the local inward-ball
construction to finitely many patches. Mathlib's smooth partition of unity supplies
compactly supported cutoffs on these patches whose sum is one on the closure.
Interior patches use the zero translation.
-/

@[expose] public noncomputable section

open Set Filter Metric Function TopologicalSpace
open scoped Topology Distributions Manifold

namespace SobolevSpace.Approximation.UpToBoundary

open Boundary

variable {n : ℕ}

/-- Finite smooth partition data with enough room for translated mollification.
The cutoffs have compact support in the ambient space, possibly meeting `∂Ω`. -/
structure InwardPartition (Ω : Set (ℝ^n)) where
  /-- Number of patches. -/
  N : ℕ
  /-- Open ambient neighborhoods. -/
  patch : Fin N → Set (ℝ^n)
  /-- Each patch is open. -/
  patch_open : ∀ i, IsOpen (patch i)
  /-- Smooth cutoffs subordinate to the patches. -/
  cutoff : Fin N → 𝓓((⊤ : Opens (ℝ^n)), ℝ)
  /-- Each cutoff is supported in its patch. -/
  cutoff_support : ∀ i, tsupport (cutoff i).toFun ⊆ patch i
  /-- The cutoffs sum to one on the closure of the domain. -/
  sum_eq_one : ∀ x ∈ closure Ω, ∑ i, (cutoff i).toFun x = 1
  /-- A fixed inward direction for each patch. -/
  direction : Fin N → ℝ^n
  /-- Upper bounds on the translation scale. -/
  radius : Fin N → ℝ
  /-- Every scale bound is positive. -/
  radius_pos : ∀ i, 0 < radius i
  /-- Translation leaves room for an interior mollifier ball. -/
  interior_ball : ∀ i, ∀ ε ∈ Ioo 0 (radius i), ∀ x ∈ patch i ∩ Ω,
    closedBall (x + ε • direction i) ε ⊆ Ω

/-- A bounded open set with C¹ boundary admits a finite partition on which
inward translations make room for mollification. -/
theorem exists_inwardPartition {Ω : Set (ℝ^n)} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hC : HasC1Boundary Ω) :
    Nonempty (InwardPartition Ω) := by
  classical
  have hlocal (x : closure Ω) :
      ∃ V : Set (ℝ^n), IsOpen V ∧ x.val ∈ V ∧ Bornology.IsBounded V ∧
        ∃ v : ℝ^n, ∃ δ > 0, ∀ ε ∈ Ioo 0 δ, ∀ z ∈ V ∩ Ω,
          closedBall (z + ε • v) ε ⊆ Ω := by
    by_cases hx : x.val ∈ Ω
    · obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ x.val hx
      refine ⟨ball x.val (r / 2), isOpen_ball, mem_ball_self (half_pos hr),
        isBounded_ball, 0, r / 2, half_pos hr, ?_⟩
      intro ε hε z hz y hy
      apply hrΩ
      have hyz : dist y z ≤ ε := by
        simpa only [smul_zero, add_zero, mem_closedBall] using hy
      have hzx : dist z x.val < r / 2 := hz.1
      have htri := dist_triangle y z x.val
      change dist y x.val < r
      linarith [hε.2]
    · have hxfront : x.val ∈ frontier Ω := by
        rw [frontier, hΩ.interior_eq]
        exact ⟨x.property, hx⟩
      obtain ⟨V, hVo, hxV, v, δ, hδ, hball⟩ := hC.exists_inward_ball hxfront
      refine ⟨V ∩ ball x.val 1, hVo.inter isOpen_ball,
        ⟨hxV, mem_ball_self zero_lt_one⟩, isBounded_ball.subset inter_subset_right,
        v, δ, hδ, ?_⟩
      exact fun ε hε z hz ↦ hball ε hε z ⟨hz.1.1, hz.2⟩
  choose V hVo hxV hVb v δ hδ hball using hlocal
  have hcover : closure Ω ⊆ ⋃ x : closure Ω, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hb.isCompact_closure.elim_finite_subcover V hVo hcover
  let e : Fin s.card ≃ s := s.equivFin.symm
  let W (i : Fin s.card) := V (e i).val
  have hWo (i : Fin s.card) : IsOpen (W i) := hVo _
  have hWb (i : Fin s.card) : Bornology.IsBounded (W i) := hVb _
  have hWcover : closure Ω ⊆ ⋃ i, W i := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨e.symm ⟨j, hj⟩, by simpa only [W, e.apply_symm_apply] using hxj⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, ℝ^n) isClosed_closure W hWo hWcover
  let ψ (i : Fin s.card) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    ⟨ρ i, (ρ i).contMDiff.contDiff,
      Metric.isCompact_of_isClosed_isBounded isClosed_closure ((hWb i).subset (hρ i)),
      subset_univ _⟩
  refine ⟨{
    N := s.card
    patch := W
    patch_open := hWo
    cutoff := ψ
    cutoff_support := hρ
    sum_eq_one := ?_
    direction := fun i ↦ v (e i).val
    radius := fun i ↦ δ (e i).val
    radius_pos := fun i ↦ hδ _
    interior_ball := fun i ↦ hball (e i).val
  }⟩
  intro x hx
  simpa only [ψ, finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx

end SobolevSpace.Approximation.UpToBoundary
