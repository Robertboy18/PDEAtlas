/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Analysis.Calculus.LocalExtension

/-!
# Localizing geometric boundary charts

A local `C¹` flattening chart has a smaller source on which both it and its inverse
admit globally `C¹` representatives. The representatives need only invert each other
between the smaller source and target. Cutting off their germs independently and
then shrinking the source preserves this property and the half-space description
of the domain.

Both new chart neighborhoods are bounded. This prepares local geometric charts for
the finite partition construction used by the Sobolev extension and trace theorems.
-/

@[expose] public section

open Filter Function Metric Set
open scoped Topology

namespace SobolevSpace.Boundary

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A local `C¹` boundary chart can be shrunk to bounded neighborhoods with globally
`C¹` forward and inverse representatives, preserving its values and the domain it flattens. -/
theorem exists_bounded_c1_flattening_chart
    (e : OpenPartialHomeomorph (ℝ^n) (ℝ^n)) {x : ℝ^n} (hx : x ∈ e.source)
    (he : ContDiffOn ℝ 1 e e.source) (he' : ContDiffOn ℝ 1 e.symm e.target)
    (hΩ : ∀ y ∈ e.source, y ∈ Ω ↔ e y ∈ HalfSpace.upper n) :
    ∃ c : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      x ∈ c.source ∧ c.source ⊆ e.source ∧ EqOn c e c.source ∧
      ContDiff ℝ 1 c ∧ ContDiff ℝ 1 c.symm ∧
      Bornology.IsBounded c.source ∧ Bornology.IsBounded c.target ∧
      ∀ y ∈ c.source, y ∈ Ω ↔ c y ∈ HalfSpace.upper n := by
  obtain ⟨f, hf, _, hef⟩ :=
    he.exists_contDiff_compactSupport_eventuallyEq e.open_source hx
  obtain ⟨g, hg, _, heg⟩ :=
    he'.exists_contDiff_compactSupport_eventuallyEq e.open_target (e.map_source hx)
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ e.source ∧ e y = f y ∧ e.symm (e y) = g (e y) :=
    (e.open_source.eventually_mem hx).and (hef.and (heg.comp_tendsto (e.continuousAt hx)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let d := e.restrOpen (ball x r) isOpen_ball
  have hdf : EqOn d f d.source := fun y hy ↦ (hball hy.2).2.1
  have hdg : EqOn d.symm g d.target := by
    intro y hy
    have hy' := hball (d.map_target hy).2
    simpa only [d, OpenPartialHomeomorph.coe_restrOpen_symm, e.right_inv hy.1] using hy'.2.2
  let c : OpenPartialHomeomorph (ℝ^n) (ℝ^n) :=
    { toFun := f
      invFun := g
      source := d.source
      target := d.target
      map_source' := fun y hy ↦ by rw [← hdf hy]; exact d.map_source hy
      map_target' := fun y hy ↦ by rw [← hdg hy]; exact d.map_target hy
      left_inv' := fun y hy ↦ by
        rw [← hdf hy, ← hdg (d.map_source hy)]
        exact d.left_inv hy
      right_inv' := fun y hy ↦ by
        rw [← hdg hy, ← hdf (d.map_target hy)]
        exact d.right_inv hy
      open_source := d.open_source
      open_target := d.open_target
      continuousOn_toFun := hf.continuous.continuousOn
      continuousOn_invFun := hg.continuous.continuousOn }
  have hcb : Bornology.IsBounded c.source :=
    (isBounded_ball : Bornology.IsBounded (ball x r)).subset inter_subset_right
  have hct : c.target ⊆ f '' closedBall x r := by
    intro y hy
    refine ⟨g y, ball_subset_closedBall (c.map_target hy).2, c.right_inv hy⟩
  refine ⟨c, ⟨hx, mem_ball_self hr⟩, inter_subset_left, hdf.symm, hf, hg, hcb,
    ((isCompact_closedBall x r).image hf.continuous).isBounded.subset hct, ?_⟩
  intro y hy
  change y ∈ Ω ↔ f y ∈ HalfSpace.upper n
  rw [← hdf hy]
  exact hΩ y hy.1

end SobolevSpace.Boundary
