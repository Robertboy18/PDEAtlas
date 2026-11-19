/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.Graph.Geometry
public import PDE.Analysis.Topology.Frontier.Locality
import PDE.Spaces.Sobolev.Boundary.Geometry.SurfaceMeasure

/-!
# The physical frontier of a graph epigraph

The graph shear identifies the strict epigraph, its frontier, and its graph
parametrization in arbitrary linear coordinates. These identities are local
when the epigraph represents a patch of another domain.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Boundary.Flux.Graph

open Set Trace.HalfSpace Geometry.SurfaceMeasure

variable {m : ℕ}

/-- Flatten a graph by subtracting its height after the linear coordinate change. -/
def linearGraphFlattening (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1))
    (g : ℝ^m → ℝ) (hg : Continuous g) : ℝ^(m + 1) ≃ₜ ℝ^m × ℝ :=
  A.toHomeomorph.trans
    (tangentialNormalContinuousLinearEquiv.toHomeomorph.trans
      (Homeomorph.graphShear g hg).symm)

@[simp]
theorem linearGraphFlattening_apply (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1))
    (g : ℝ^m → ℝ) (hg : Continuous g) (x : ℝ^(m + 1)) :
    linearGraphFlattening A g hg x =
      ((splitTangentialNormal (A x)).1, linearGraphHeight A g x) := rfl

@[simp]
theorem linearGraphFlattening_symm_apply (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1))
    (g : ℝ^m → ℝ) (hg : Continuous g) (z : ℝ^m × ℝ) :
    (linearGraphFlattening A g hg).symm z =
      A.symm (joinTangentialNormal (z.1, z.2 + g z.1)) := rfl

/-- Flattening sends the strict epigraph onto the upper half-space. -/
theorem linearGraphFlattening_preimage_upper
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (hg : Continuous g) :
    linearGraphFlattening A g hg ⁻¹' (univ ×ˢ Ioi 0) = linearEpigraph A g := by
  ext x
  simp [linearGraphHeight, linearEpigraph, sub_pos]

/-- The strict epigraph is open for a continuous graph height. -/
theorem isOpen_linearEpigraph
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (hg : Continuous g) :
    IsOpen (linearEpigraph A g) := by
  rw [← linearGraphFlattening_preimage_upper A g hg]
  exact (isOpen_univ.prod isOpen_Ioi).preimage (linearGraphFlattening A g hg).continuous

/-- The physical frontier consists exactly of points of zero graph height. -/
theorem mem_frontier_linearEpigraph_iff
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (hg : Continuous g)
    (x : ℝ^(m + 1)) :
    x ∈ frontier (linearEpigraph A g) ↔ linearGraphHeight A g x = 0 := by
  have h := (linearGraphFlattening A g hg).preimage_frontier (univ ×ˢ Ioi 0)
  rw [linearGraphFlattening_preimage_upper, frontier_univ_prod_eq, frontier_Ioi] at h
  rw [← h]
  simp

/-- The full graph parametrizes the full frontier of the epigraph. -/
theorem range_linearGraphParametrization
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (hg : Continuous g) :
    range (linearGraphParametrization A g) = frontier (linearEpigraph A g) := by
  ext x
  rw [mem_frontier_linearEpigraph_iff A g hg]
  constructor
  · rintro ⟨y, rfl⟩
    simp [linearGraphHeight, linearGraphParametrization]
  · intro hx
    refine ⟨(splitTangentialNormal (A x)).1, ?_⟩
    apply A.injective
    have heq : g (splitTangentialNormal (A x)).1 = (A x) (Fin.last m) :=
      (sub_eq_zero.mp hx).symm
    rw [linearGraphParametrization, A.apply_symm_apply, heq]
    exact join_splitTangentialNormal (A x)

/-- Graph parametrization is a closed embedding, so compact physical
supports pull back to compact tangential supports. -/
theorem isClosedEmbedding_linearGraphParametrization
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (hg : Continuous g) :
    Topology.IsClosedEmbedding (linearGraphParametrization A g) := by
  have h := (linearGraphFlattening A g hg).symm.isClosedEmbedding.comp
    (tangentialNormalContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.comp
      (isometry_flatEmbedding (n := m)).isClosedEmbedding)
  convert h using 1
  funext y
  simp [Function.comp_def, flatEmbedding, linearGraphParametrization]

/-- On a graph patch, the domain frontier agrees with the parametrized graph. -/
theorem mem_frontier_iff_graphHeight_eq_zero
    {Ω U : Set (ℝ^(m + 1))} (hU : IsOpen U)
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) (g : ℝ^m → ℝ) (hg : Continuous g)
    (hside : ∀ x ∈ U, x ∈ Ω ↔ x ∈ linearEpigraph A g)
    {x : ℝ^(m + 1)} (hx : x ∈ U) :
    x ∈ frontier Ω ↔ linearGraphHeight A g x = 0 :=
  (hU.mem_frontier_iff_of_local_eq hside hx).trans
    (mem_frontier_linearEpigraph_iff A g hg x)

end SobolevSpace.Boundary.Flux.Graph
