/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GlobalGraphChart
public import PDE.Spaces.Sobolev.Boundary.Geometry.TangentialNormal
import PDE.Analysis.Calculus.LocalExtension

/-!
# Local differentiable graph boundary

`HasContDiffGraphBoundary` expresses the local graph condition using continuous linear
coordinates and a height that is `C^m` on an open tangential neighborhood. The boundary
point lies on the graph, and the domain agrees locally with its strict epigraph. Openness
and boundedness of the domain are separate hypotheses. At finite order the graph germ
suffices; the order-one predicate agrees with `HasC1GraphBoundary`.

Flattening subtracts a global `C^m` representative of the height from the normal coordinate.
A cutoff supplies this representative, and restricting the source preserves the graph
relation. The triangular formulas give global regularity of both maps, which is retained
when their source and target are bounded. At infinite order the same construction uses
smoothness on one open neighborhood, rather than smoothness at a single point.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology
open SobolevSpace.Trace.HalfSpace

namespace SobolevSpace.Extension.GraphChart

variable {n : ℕ}

/-- The tangential split is unchanged by zeroing the final coordinate. -/
@[simp]
theorem splitTangentialNormal_fst_boundaryProjection (x : ℝ^(n + 1)) :
    (splitTangentialNormal (HalfSpace.boundaryProjection (n + 1) x)).1 =
      (splitTangentialNormal x).1 := by
  ext i
  simp only [splitTangentialNormal_fst_apply]
  apply HalfSpace.boundaryProjection_apply_of_ne_last
  exact Fin.castSucc_ne_last i

end SobolevSpace.Extension.GraphChart

namespace SobolevSpace.Boundary

open Extension.GraphChart

variable {n : ℕ}

/-- A set has C1 graph boundary if, near each boundary point, linear coordinates identify
it with the region above a scalar C1 graph. The coordinate change need not be orthogonal.
Regularity and the side condition are only required as germs at the boundary point. -/
def HasC1GraphBoundary (Ω : Set (ℝ^n)) : Prop :=
  ∀ x ∈ frontier Ω,
    ∃ e : ℝ^n ≃L[ℝ] (ℝ^(n - 1) × ℝ), ∃ g : ℝ^(n - 1) → ℝ,
      ContDiffAt ℝ 1 g (e x).1 ∧ (e x).2 = g (e x).1 ∧
        ∀ᶠ y in 𝓝 x, y ∈ Ω ↔ g (e y).1 < (e y).2

/-- A boundary is locally a `C^m` graph if linear coordinates identify the domain with
an epigraph near each boundary point. The height is `C^m` on an open tangential neighborhood.
For infinite order, this requires one neighborhood on which all orders are available. -/
def HasContDiffGraphBoundary (m : ℕ∞) (Ω : Set (ℝ^n)) : Prop :=
  ∀ x ∈ frontier Ω,
    ∃ e : ℝ^n ≃L[ℝ] (ℝ^(n - 1) × ℝ), ∃ g : ℝ^(n - 1) → ℝ,
      ∃ s : Set (ℝ^(n - 1)), IsOpen s ∧ (e x).1 ∈ s ∧ ContDiffOn ℝ m g s ∧
        (e x).2 = g (e x).1 ∧ ∀ᶠ y in 𝓝 x, y ∈ Ω ↔ g (e y).1 < (e y).2

/-- Lowering the differentiability order preserves the local graph condition. -/
theorem HasContDiffGraphBoundary.of_le {m k : ℕ∞} {Ω : Set (ℝ^n)}
    (hΩ : HasContDiffGraphBoundary m Ω) (hk : k ≤ m) : HasContDiffGraphBoundary k Ω := by
  intro x hx
  obtain ⟨e, g, s, hs, hxs, hg, heq, hside⟩ := hΩ x hx
  exact ⟨e, g, s, hs, hxs, hg.of_le (by exact_mod_cast hk), heq, hside⟩

/-- At finite order, regularity of the graph germ suffices for the open-neighborhood
formulation of graph boundary. -/
theorem hasContDiffGraphBoundary_nat_iff (k : ℕ) {Ω : Set (ℝ^n)} :
    HasContDiffGraphBoundary k Ω ↔
      ∀ x ∈ frontier Ω,
        ∃ e : ℝ^n ≃L[ℝ] (ℝ^(n - 1) × ℝ), ∃ g : ℝ^(n - 1) → ℝ,
          ContDiffAt ℝ k g (e x).1 ∧ (e x).2 = g (e x).1 ∧
            ∀ᶠ y in 𝓝 x, y ∈ Ω ↔ g (e y).1 < (e y).2 := by
  constructor
  · intro h x hx
    obtain ⟨e, g, s, hs, hxs, hg, heq, hside⟩ := h x hx
    exact ⟨e, g, hg.contDiffAt (hs.mem_nhds hxs), heq, hside⟩
  · intro h x hx
    obtain ⟨e, g, hg, heq, hside⟩ := h x hx
    obtain ⟨s, hs, hgs⟩ := hg.contDiffOn le_rfl (by simp)
    obtain ⟨t, hts, ht, hxt⟩ := _root_.mem_nhds_iff.mp hs
    exact ⟨e, g, t, ht, hxt, hgs.mono hts, heq, hside⟩

/-- The order-one graph condition agrees with the original C1 boundary predicate. -/
theorem hasContDiffGraphBoundary_one_iff {Ω : Set (ℝ^n)} :
    HasContDiffGraphBoundary 1 Ω ↔ HasC1GraphBoundary Ω :=
  hasContDiffGraphBoundary_nat_iff 1

/-- A higher-order graph boundary is in particular a C1 graph boundary. -/
theorem HasContDiffGraphBoundary.hasC1GraphBoundary {m : ℕ∞} {Ω : Set (ℝ^n)}
    (hΩ : HasContDiffGraphBoundary m Ω) (hm : 1 ≤ m) : HasC1GraphBoundary Ω :=
  hasContDiffGraphBoundary_one_iff.mp (hΩ.of_le hm)

variable {Ω : Set (ℝ^(n + 1))} {x : ℝ^(n + 1)}

/-- A local `C^m` graph has a bounded flattening chart whose total forward and inverse
maps are globally `C^m`. Cutting off the height preserves the triangular inverse formula. -/
theorem exists_contDiff_flattening_chart_of_local_graph
    {m : ℕ∞} (hm : 1 ≤ m)
    (A : ℝ^(n + 1) ≃L[ℝ] (ℝ^n × ℝ)) {g : ℝ^n → ℝ} {s : Set (ℝ^n)}
    (hg : ContDiffOn ℝ m g s) (hs : IsOpen s) (hxs : (A x).1 ∈ s)
    (hΩ : ∀ᶠ y in 𝓝 x, y ∈ Ω ↔ g (A y).1 < (A y).2) :
    ∃ e : OpenPartialHomeomorph (ℝ^(n + 1)) (ℝ^(n + 1)),
      x ∈ e.source ∧ ContDiff ℝ m e ∧ ContDiff ℝ m e.symm ∧
      Bornology.IsBounded e.source ∧ Bornology.IsBounded e.target ∧
      ∀ y ∈ e.source, y ∈ Ω ↔ e y ∈ HalfSpace.upper (n + 1) := by
  obtain ⟨G, hG, _, heq⟩ := hg.exists_contDiff_compactSupport_eventuallyEq hs hxs
  have hπ : ContDiff ℝ m (fun z : ℝ^(n + 1) ↦ (splitTangentialNormal z).1) :=
    tangentialNormalContinuousLinearEquiv.contDiff.fst
  let B := A.trans tangentialNormalContinuousLinearEquiv.symm
  let h : ℝ^(n + 1) → ℝ := fun z ↦ -G (splitTangentialNormal z).1
  have hh : ContDiff ℝ m h := (hG.comp hπ).neg
  let e := B.toHomeomorph.trans
    (negativeHomeomorph (n + 1) h (hh.of_le (by exact_mod_cast hm)))
  have he : ContDiff ℝ m e := (negativeMap_contDiff (n + 1) m hh).comp B.contDiff
  have he' : ContDiff ℝ m e.symm :=
    B.symm.contDiff.comp (negativeMapInverse_contDiff (n + 1) m hh)
  have hagree := heq.comp_tendsto A.continuous.continuousAt.fst
  obtain ⟨δ, hδ, hlocal⟩ := Metric.mem_nhds_iff.mp (inter_mem hΩ hagree)
  refine ⟨restrictHomeomorph (n + 1) e (ball x δ) isOpen_ball,
    mem_ball_self hδ, he, he', isBounded_ball,
    restrictHomeomorph_target_bounded (n + 1) e _ _ isBounded_ball, ?_⟩
  intro y hy
  obtain ⟨hyside, hyagree⟩ := hlocal hy
  change y ∈ Ω ↔ g (A y).1 < (A y).2 at hyside
  change g (A y).1 = G (A y).1 at hyagree
  rw [hyside]
  change g (A y).1 < (A y).2 ↔ negativeMap (n + 1) h (B y) ∈ HalfSpace.upper (n + 1)
  rw [negativeMap_mem_upper_iff]
  change g (A y).1 < (A y).2 ↔
    -(splitTangentialNormal (B y)).2 < h (HalfSpace.boundaryProjection (n + 1) (B y))
  simp only [h, splitTangentialNormal_fst_boundaryProjection, B,
    ContinuousLinearEquiv.trans_apply, tangentialNormalContinuousLinearEquiv_symm_apply,
    split_joinTangentialNormal]
  rw [hyagree]
  exact neg_lt_neg_iff.symm

/-- Graph boundary supplies bounded local flattenings with globally `C^m` forward and
inverse representatives at every boundary point. -/
theorem HasContDiffGraphBoundary.global_flattening_charts {m : ℕ∞}
    (hΩ : HasContDiffGraphBoundary m Ω) (hm : 1 ≤ m) :
    ∀ x ∈ frontier Ω, ∃ e : OpenPartialHomeomorph (ℝ^(n + 1)) (ℝ^(n + 1)),
      x ∈ e.source ∧ ContDiff ℝ m e ∧ ContDiff ℝ m e.symm ∧
      Bornology.IsBounded e.source ∧ Bornology.IsBounded e.target ∧
      ∀ y ∈ e.source, y ∈ Ω ↔ e y ∈ HalfSpace.upper (n + 1) := by
  intro x hx
  obtain ⟨e, g, s, hs, hxs, hg, _, hgraph⟩ := hΩ x hx
  exact exists_contDiff_flattening_chart_of_local_graph hm e hg hs hxs hgraph

/-- A C1 graph germ in linear coordinates supplies a local C1 flattening. -/
theorem exists_c1_flattening_chart_of_local_graph
    (A : ℝ^(n + 1) ≃L[ℝ] (ℝ^n × ℝ)) {g : ℝ^n → ℝ}
    (hg : ContDiffAt ℝ 1 g (A x).1)
    (hΩ : ∀ᶠ y in 𝓝 x, y ∈ Ω ↔ g (A y).1 < (A y).2) :
    ∃ e : OpenPartialHomeomorph (ℝ^(n + 1)) (ℝ^(n + 1)),
      x ∈ e.source ∧ ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∀ y ∈ e.source, y ∈ Ω ↔ e y ∈ HalfSpace.upper (n + 1) := by
  obtain ⟨s, hs, hgs⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨t, hts, ht, hxt⟩ := _root_.mem_nhds_iff.mp hs
  obtain ⟨e, hx, he, he', _, _, hside⟩ :=
    exists_contDiff_flattening_chart_of_local_graph le_rfl A (hgs.mono hts) ht hxt hΩ
  exact ⟨e, hx, he.contDiffOn, he'.contDiffOn, hside⟩

/-- C1 graph boundary gives local C1 homeomorphisms flattening the domain to the upper
half-space at every boundary point. -/
theorem HasC1GraphBoundary.local_flattening_charts (hΩ : HasC1GraphBoundary Ω) :
    ∀ x ∈ frontier Ω, ∃ e : OpenPartialHomeomorph (ℝ^(n + 1)) (ℝ^(n + 1)),
      x ∈ e.source ∧ ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∀ y ∈ e.source, y ∈ Ω ↔ e y ∈ HalfSpace.upper (n + 1) := by
  intro x hx
  obtain ⟨e, g, hg, _, hgraph⟩ := hΩ x hx
  exact exists_c1_flattening_chart_of_local_graph e hg hgraph

end SobolevSpace.Boundary
