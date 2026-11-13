/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.DefiningFunction

/-!
# Independence of the outward normal from the operational atlas

A height coordinate from one atlas is a local defining function for the other.
Its positive orientation identifies both normalized conormals, so the intrinsic
normal does not depend on the finite atlas used to construct it.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Set Filter
open scoped Topology

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Any two operational C¹ atlases of the same domain define the same outward normal. -/
theorem outwardUnitNormal_eq_of_atlases
    (A B : Boundary.C1ExtensionAtlas n Ω) (x : frontier Ω) :
    outwardUnitNormal (hΩ := A) x = outwardUnitNormal (hΩ := B) x := by
  obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier (hΩ := A) x.property
  let q := (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
    (fderiv ℝ (fun z ↦ A.chart i z) x)
  have hq : q ≠ 0 := by
    intro h
    apply chartConormal_ne_zero (hΩ := A) i hi
    change (InnerProductSpace.toDual ℝ (ℝ^n)).symm q = 0
    rw [h, map_zero]
  have hnormal := outwardUnitNormal_eq_of_defining_function (hΩ := B) x.property
    (hasFDerivAt_chartLastCoordinate (hΩ := A) i x) hq
    (by
      filter_upwards [(A.chart i).open_source.mem_nhds hi] with y hy
      exact (chartLastCoordinate_eq_zero_iff (hΩ := A) i hy).mpr)
    (by
      filter_upwards [(A.chart i).open_source.mem_nhds hi] with y hy
      exact fun hyΩ ↦ ((chartLastCoordinate_pos_iff (hΩ := A) i hy).mpr hyΩ).le)
  rw [hnormal, outwardUnitNormal_eq_chart (hΩ := A) x i hi]
  rfl

end SobolevSpace.Trace.C1
