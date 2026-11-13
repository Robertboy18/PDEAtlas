/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Construction
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphBoundary
import PDE.Analysis.Calculus.LocalExtension

/-!
# Finite boundary covers retaining linear graph coordinates

A raw C¹ graph boundary gives finitely many bounded patches with globally
C¹ graph heights. The height extension agrees with the original germ on
its patch. Retaining the linear coordinates and the heights allows local
integration formulas to be applied before the partition of unity is summed.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Boundary

open Filter Metric Set
open scoped Topology

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}

/-- A finite boundary cover with explicit C¹ graph data on each patch.
Only the local geometry is recorded; integral identities are not fields. -/
structure C1GraphBoundaryCover (m : ℕ) (Ω : Set (ℝ^(m + 1)))
    extends FiniteBoundaryCover (m + 1) Ω where
  /-- Linear tangential-normal coordinates of each patch. -/
  coordinates : Fin N → ℝ^(m + 1) ≃L[ℝ] (ℝ^m × ℝ)
  /-- Globally represented graph height for each patch. -/
  height : Fin N → ℝ^m → ℝ
  /-- The graph heights have continuous first derivatives. -/
  height_contDiff : ∀ i, ContDiff ℝ 1 (height i)
  /-- Within its patch, the domain is exactly the strict epigraph. -/
  mem_iff_epigraph : ∀ i, ∀ x ∈ boundaryPatch i,
    x ∈ Ω ↔ height i (coordinates i x).1 < (coordinates i x).2

/-- A C¹ graph germ has a bounded open physical neighborhood on which the
height can be represented by a globally C¹ function. -/
theorem HasC1GraphBoundary.exists_global_graph_patch
    (hgraph : HasC1GraphBoundary Ω) {x : ℝ^(m + 1)} (hx : x ∈ frontier Ω) :
    ∃ U : Set (ℝ^(m + 1)), IsOpen U ∧ Bornology.IsBounded U ∧ x ∈ U ∧
      ∃ A : ℝ^(m + 1) ≃L[ℝ] (ℝ^m × ℝ), ∃ g : ℝ^m → ℝ,
        ContDiff ℝ 1 g ∧
          ∀ y ∈ U, y ∈ Ω ↔ g (A y).1 < (A y).2 := by
  obtain ⟨A, g, hg, _, hside⟩ := hgraph x hx
  obtain ⟨G, hG, _, heq⟩ := hg.exists_contDiff_compactSupport_eventuallyEq
  have hagree := heq.comp_tendsto A.continuous.continuousAt.fst
  obtain ⟨r, hr, hlocal⟩ := Metric.mem_nhds_iff.mp (inter_mem hside hagree)
  refine ⟨ball x r, isOpen_ball, isBounded_ball, mem_ball_self hr, A, G, hG, ?_⟩
  intro y hy
  obtain ⟨hyside, hyeq⟩ := hlocal hy
  change y ∈ Ω ↔ g (A y).1 < (A y).2 at hyside
  change g (A y).1 = G (A y).1 at hyeq
  rwa [hyeq] at hyside

/-- Compactness selects finitely many raw graph patches. The subordinate
smooth cutoffs are supplied by the inherited finite boundary cover. -/
theorem HasC1GraphBoundary.nonempty_c1GraphBoundaryCover
    (hgraph : HasC1GraphBoundary Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) :
    Nonempty (C1GraphBoundaryCover m Ω) := by
  classical
  have hpatch := fun x : frontier Ω ↦ hgraph.exists_global_graph_patch x.property
  choose U hUopen hUbounded hxU A g hg hside using hpatch
  have hcompact : IsCompact (frontier Ω) :=
    hbounded.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨s, hs⟩ := hcompact.elim_finite_subcover U hUopen
    (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  let index : Fin s.card → frontier Ω := fun i ↦ (s.equivFin.symm i).val
  exact ⟨{
    isOpen := hopen
    bounded := hbounded
    N := s.card
    boundaryPatch := fun i ↦ U (index i)
    boundaryPatch_open := fun i ↦ hUopen (index i)
    boundaryPatch_bounded := fun i ↦ hUbounded (index i)
    frontier_subset_iUnion := by
      intro x hx
      obtain ⟨y, hys, hy⟩ := mem_iUnion₂.mp (hs hx)
      refine mem_iUnion.2 ⟨s.equivFin ⟨y, hys⟩, ?_⟩
      simpa only [index, Equiv.symm_apply_apply] using hy
    coordinates := fun i ↦ A (index i)
    height := fun i ↦ g (index i)
    height_contDiff := fun i ↦ hg (index i)
    mem_iff_epigraph := fun i ↦ hside (index i) }⟩

end SobolevSpace.Boundary
