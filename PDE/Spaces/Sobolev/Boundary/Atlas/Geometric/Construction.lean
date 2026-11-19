/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.LocalConstruction
public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.Localization

/-!
# Operational atlases from local boundary geometry

A bounded open domain with local `C¹` flattening charts admits an operational
`C1ExtensionAtlas`. The geometric hypothesis asks only for a local homeomorphism
near each boundary point, `C¹` on its source with a `C¹` inverse on its target,
which identifies the domain with the upper half-space.

The proof first shrinks each chart and cuts off both representatives. Compactness
of the boundary gives a finite subcover of the bounded chart neighborhoods.
The smooth partition construction then supplies the interior and boundary
test functions, their support inclusions, and their sum identity.

No global chart regularity, finite cover, partition, or analytic estimate is
required of the geometric input.
-/

@[expose] public section

open Set

namespace SobolevSpace.Boundary

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A bounded open set with local `C¹` boundary flattenings has an operational extension
atlas. The charts and their inverses need only be `C¹` on their original open neighborhoods. -/
theorem nonempty_c1ExtensionAtlas_of_local_charts
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hcharts : ∀ x ∈ frontier Ω, ∃ e : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      x ∈ e.source ∧ ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∀ y ∈ e.source, y ∈ Ω ↔ e y ∈ HalfSpace.upper n) :
    Nonempty (C1ExtensionAtlas n Ω) := by
  classical
  have hlocal : ∀ x : frontier Ω, ∃ c : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      (x : ℝ^n) ∈ c.source ∧ ContDiff ℝ 1 c ∧ ContDiff ℝ 1 c.symm ∧
      Bornology.IsBounded c.source ∧ Bornology.IsBounded c.target ∧
      ∀ y ∈ c.source, y ∈ Ω ↔ c y ∈ HalfSpace.upper n := by
    intro x
    obtain ⟨e, hx, he, he', hΩ⟩ := hcharts x x.property
    obtain ⟨c, hc, _, _, hcf, hcg, hcs, hct, hcΩ⟩ :=
      exists_bounded_c1_flattening_chart e hx he he' hΩ
    exact ⟨c, hc, hcf, hcg, hcs, hct, hcΩ⟩
  obtain ⟨atlas, _, _⟩ := exists_c1ExtensionAtlas_of_global_charts le_rfl hopen hbounded hlocal
  exact ⟨atlas⟩

/-- Choose an operational extension atlas from local `C¹` boundary geometry on a
bounded open set. All localization data are supplied by the construction. -/
@[instance_reducible]
noncomputable def c1ExtensionAtlasOfLocalCharts
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hcharts : ∀ x ∈ frontier Ω, ∃ e : OpenPartialHomeomorph (ℝ^n) (ℝ^n),
      x ∈ e.source ∧ ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      ∀ y ∈ e.source, y ∈ Ω ↔ e y ∈ HalfSpace.upper n) :
    C1ExtensionAtlas n Ω :=
  Classical.choice (nonempty_c1ExtensionAtlas_of_local_charts hopen hbounded hcharts)

end SobolevSpace.Boundary
