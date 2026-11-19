/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Star.Topology
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.ExtrClosure

/-!
# Outward normals on star-shaped domains

At a boundary point, moving toward a star center stays in the closure of the domain.
The flattened height has a local minimum there, so its derivative in that direction
is nonnegative. The outward normal is the normalized negative height gradient; hence
its inner product with the vector from the center to the boundary is nonnegative.

We use Mathlib's positive tangent cone to take this one-sided derivative. The main
result assumes star-convexity of the closure, as in Evans, §9.4.2, the lemma on normals
to a star-shaped region. Star-convexity of the open domain is a sufficient condition.
The center can be any point, and convexity of the whole domain is not required.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.4.2, p. 551, for star-shaped regions, and the lemma on
  normals to a star-shaped region, p. 552: if `∂U` is C¹ and `U` is star-shaped with respect to `0`,
  then `x · ν(x) ≥ 0` on `∂U`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace SobolevSpace.Trace.C1

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
  [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The flattened height has a local minimum on the closed domain at a boundary point. -/
theorem isLocalMinOn_chartLastCoordinate_closure
    (i : Fin hΩ.N) {x : ℝ^n} (hxi : x ∈ (hΩ.chart i).source)
    (hx : x ∈ frontier Ω) :
    IsLocalMinOn (fun y : ℝ^n ↦ (hΩ.chart i y) (PDE.Common.lastIndex (n := n)))
      (closure Ω) x := by
  have hzero := (chartLastCoordinate_eq_zero_iff i hxi).mpr hx
  have hmin :
      IsLocalMinOn
        (fun y : ℝ^n ↦ (hΩ.chart i y) (PDE.Common.lastIndex (n := n))) Ω x := by
    refine mem_nhdsWithin.mpr ⟨(hΩ.chart i).source, (hΩ.chart i).open_source, hxi, ?_⟩
    intro y hy
    change (hΩ.chart i x) _ ≤ (hΩ.chart i y) _
    rw [hzero]
    exact ((chartLastCoordinate_pos_iff i hy.1).mpr hy.2).le
  exact hmin.closure
    ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).continuous.comp
      (hΩ.chart_contDiff i).continuous).continuousOn

/-- The outward normal has nonnegative inner product with the radius from a star center.
It suffices that the closed domain is star-convex; the center may lie on its boundary. -/
theorem inner_sub_outwardUnitNormal_nonneg_of_starConvex_closure
    {c : ℝ^n} (hstar : StarConvex ℝ c (closure Ω)) (x : frontier Ω) :
    0 ≤ inner ℝ ((x : ℝ^n) - c) (outwardUnitNormal (n := n) (Ω := Ω) x) := by
  obtain ⟨i, hxi⟩ := exists_chart_source_of_mem_frontier (n := n) (Ω := Ω) x.property
  have hseg : segment ℝ (x : ℝ^n) c ⊆ closure Ω := by
    rw [segment_symm]
    exact hstar.segment_subset (frontier_subset_closure x.property)
  have hmin := isLocalMinOn_chartLastCoordinate_closure i hxi x.property
  have hder := hmin.hasFDerivWithinAt_nonneg
    (hasFDerivAt_chartLastCoordinate i x).hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset hseg)
  have hdual :
      (InnerProductSpace.toDual ℝ (ℝ^n)) (chartConormal (n := n) (Ω := Ω) i x) =
        (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
          (fderiv ℝ (fun z ↦ hΩ.chart i z) x) := by
    exact (InnerProductSpace.toDual ℝ (ℝ^n)).apply_symm_apply _
  rw [← hdual, InnerProductSpace.toDual_apply_apply] at hder
  have hsign : inner ℝ ((x : ℝ^n) - c) (chartConormal (n := n) (Ω := Ω) i x) ≤ 0 := by
    rw [real_inner_comm, ← neg_sub c (x : ℝ^n), inner_neg_right]
    exact neg_nonpos.mpr hder
  rw [outwardUnitNormal_eq_chart x i hxi, chartOutwardUnitNormal, inner_smul_right]
  exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (inv_nonneg.mpr (norm_nonneg _))) hsign

/-- Star-convexity of the domain itself also gives the outward-normal inequality. -/
theorem inner_sub_outwardUnitNormal_nonneg_of_starConvex
    {c : ℝ^n} (hstar : StarConvex ℝ c Ω) (x : frontier Ω) :
    0 ≤ inner ℝ ((x : ℝ^n) - c) (outwardUnitNormal (n := n) (Ω := Ω) x) :=
  inner_sub_outwardUnitNormal_nonneg_of_starConvex_closure hstar.closure x

end SobolevSpace.Trace.C1
