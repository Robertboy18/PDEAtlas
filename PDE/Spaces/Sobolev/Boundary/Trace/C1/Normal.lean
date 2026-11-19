/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry -- shake: keep

/-!
# Chartwise outward normals on operational `C¹` domains

Each chart in a `Boundary.C1ExtensionAtlas` identifies the domain with the upper half-space, so
the flattened height `h(x) = (chart x)ₙ` is a `C¹` function that is positive on `Ω`, zero on
`∂Ω`, and negative outside. Its gradient at a boundary point is therefore an inward conormal,
and the outward unit normal `ν` of the `C¹` boundary (Evans, PDE, Appendix C.1) is the
normalized negative of that gradient. We carry out that construction chart by chart and
show it is chart independent.

The chart conormal is the Riesz representative of `x ↦ D h(x)`. It is nonzero on the chart source
because `D(chart) ∘ D(chart⁻¹) = id`. On an overlap of two charts, both heights vanish on `∂Ω`
and are positive on `Ω`, so their differentials at a boundary point have the same kernel (the
tangent hyperplane) and the same sign in the normal direction, hence differ by a positive scalar.
The normalized vectors therefore agree, which allows the outward unit normal to be defined on
`frontier Ω` by choosing any chart containing the point.

## Main results

* `chartLastCoordinate_pos_iff`, `chartLastCoordinate_eq_zero_iff`,
  `hasFDerivAt_chartLastCoordinate`: the flattened height and its derivative.
* `chartConormal`, `chartConormal_ne_zero`, `chartOutwardUnitNormal`,
  `norm_chartOutwardUnitNormal`: the chartwise conormal and unit normal.
* `chartConormal_eq_pos_smul`, `chartOutwardUnitNormal_eq`: chart independence up to a positive
  scalar, hence exact independence after normalization.
* `outwardUnitNormal`, `outwardUnitNormal_eq_chart`, `norm_outwardUnitNormal`: the intrinsic
  outward unit normal on `∂Ω`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.1, pp. 710-711, for `C¹` boundaries and the outward
  unit normal.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Trace.C1

open Filter Set

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The derivative of a chart followed by that of its inverse is the
identity wherever the chart is defined. -/
theorem fderiv_chart_comp_fderiv_chart_symm
    (i : Fin hΩ.N) {x : ℝ^n} (hx : x ∈ (hΩ.chart i).source) :
    (fderiv ℝ (fun z ↦ hΩ.chart i z) x).comp
        (fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (hΩ.chart i x)) =
      ContinuousLinearMap.id ℝ (ℝ^n) := by
  let e := hΩ.chart i
  have hy : e x ∈ e.target := e.map_source hx
  have hx' : e.symm (e x) = x := e.left_inv hx
  have hchart :
      HasFDerivAt (fun z ↦ e z)
        (fderiv ℝ (fun z ↦ e z) (e.symm (e x))) (e.symm (e x)) :=
    (hΩ.chart_contDiff i).differentiable
      (by norm_num) (e.symm (e x)) |>.hasFDerivAt
  have hsymm :
      HasFDerivAt (fun z ↦ e.symm z)
        (fderiv ℝ (fun z ↦ e.symm z) (e x)) (e x) :=
    (hΩ.chart_symm_contDiff i).differentiable
      (by norm_num) (e x) |>.hasFDerivAt
  have hcomp' :
      HasFDerivAt (fun z ↦ e (e.symm z))
        ((fderiv ℝ (fun z ↦ e z) (e.symm (e x))).comp
          (fderiv ℝ (fun z ↦ e.symm z) (e x))) (e x) := by
    exact hchart.comp (e x) hsymm
  have hcomp :
      HasFDerivAt (fun z ↦ e (e.symm z))
        ((fderiv ℝ (fun z ↦ e z) x).comp
          (fderiv ℝ (fun z ↦ e.symm z) (e x))) (e x) := by
    simpa [hx'] using hcomp'
  have heq : (fun z ↦ e (e.symm z)) =ᶠ[nhds (e x)] fun z ↦ z :=
    e.eventually_right_inverse hy
  exact
    (hcomp.congr_of_eventuallyEq heq.symm).unique
      (hasFDerivAt_id (x := e x))

/-- The derivative of a chart inverse followed by that of the chart is the
identity wherever the chart is defined. -/
theorem fderiv_chart_symm_comp_fderiv_chart
    (i : Fin hΩ.N) {x : ℝ^n} (hx : x ∈ (hΩ.chart i).source) :
    (fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (hΩ.chart i x)).comp
        (fderiv ℝ (fun z ↦ hΩ.chart i z) x) =
      ContinuousLinearMap.id ℝ (ℝ^n) := by
  let e := hΩ.chart i
  have hy : e x ∈ e.target := e.map_source hx
  have hchart :
      HasFDerivAt (fun z ↦ e z) (fderiv ℝ (fun z ↦ e z) x) x :=
    (hΩ.chart_contDiff i).differentiable (by norm_num) x |>.hasFDerivAt
  have hsymm :
      HasFDerivAt (fun z ↦ e.symm z)
        (fderiv ℝ (fun z ↦ e.symm z) (e x)) (e x) :=
    (hΩ.chart_symm_contDiff i).differentiable (by norm_num) (e x) |>.hasFDerivAt
  have hcomp :
      HasFDerivAt (fun z ↦ e.symm (e z))
        ((fderiv ℝ (fun z ↦ e.symm z) (e x)).comp
          (fderiv ℝ (fun z ↦ e z) x)) x :=
    hsymm.comp x hchart
  have heq : (fun z ↦ e.symm (e z)) =ᶠ[nhds x] fun z ↦ z :=
    e.eventually_left_inverse hx
  exact
    (hcomp.congr_of_eventuallyEq heq.symm).unique
      (hasFDerivAt_id (x := x))

/-- The flattened normal coordinate is positive exactly on the domain. -/
theorem chartLastCoordinate_pos_iff
    (i : Fin hΩ.N) {x : ℝ^n} (hx : x ∈ (hΩ.chart i).source) :
    0 < (hΩ.chart i x) (PDE.Common.lastIndex (n := n)) ↔ x ∈ Ω := by
  simpa [HalfSpace.upper] using (hΩ.chart_mem_iff_upper i x hx).symm

/-- The flattened normal coordinate vanishes exactly on the boundary. -/
theorem chartLastCoordinate_eq_zero_iff
    (i : Fin hΩ.N) {x : ℝ^n} (hx : x ∈ (hΩ.chart i).source) :
    (hΩ.chart i x) (PDE.Common.lastIndex (n := n)) = 0 ↔
      x ∈ frontier Ω := by
  simpa [HalfSpace.boundary] using
    chart_mem_boundary_iff (n := n) (Ω := Ω) i hx

/-- The derivative of the flattened normal coordinate is the last-coordinate
covector composed with the chart derivative. -/
theorem hasFDerivAt_chartLastCoordinate
    (i : Fin hΩ.N) (x : ℝ^n) :
    HasFDerivAt
      (fun z : ℝ^n ↦ (hΩ.chart i z) (PDE.Common.lastIndex (n := n)))
      ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
        (fderiv ℝ (fun z ↦ hΩ.chart i z) x)) x := by
  have hchart :
      HasFDerivAt (fun z ↦ hΩ.chart i z)
        (fderiv ℝ (fun z ↦ hΩ.chart i z) x) x :=
    (hΩ.chart_contDiff i).differentiable (by norm_num) x |>.hasFDerivAt
  exact
    (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).hasFDerivAt.comp
      x hchart

/-- The physical conormal determined by the last coordinate of a boundary
chart. -/
noncomputable def chartConormal (i : Fin hΩ.N) (x : ℝ^n) : ℝ^n :=
  (InnerProductSpace.toDual ℝ (ℝ^n)).symm
    ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
      (fderiv ℝ (fun z ↦ hΩ.chart i z) x))

/-- The chart conormal is nonzero wherever the boundary chart is defined. -/
theorem chartConormal_ne_zero
    (i : Fin hΩ.N) {x : ℝ^n} (hx : x ∈ (hΩ.chart i).source) :
    chartConormal (n := n) (Ω := Ω) i x ≠ 0 := by
  let e := hΩ.chart i
  let last := PDE.Common.lastIndex (n := n)
  let q : ℝ^n →L[ℝ] ℝ := EuclideanSpace.proj last
  let v : ℝ^n := EuclideanSpace.single last 1
  let w : ℝ^n := fderiv ℝ (fun z ↦ e.symm z) (e x) v
  have hinv := congrArg (fun A : ℝ^n →L[ℝ] ℝ^n ↦ A v)
    (fderiv_chart_comp_fderiv_chart_symm
      (n := n) (Ω := Ω) i hx)
  have hinv' :
      (fderiv ℝ (fun z ↦ e z) x)
          (fderiv ℝ (fun z ↦ e.symm z) (e x) v) = v := by
    simpa using hinv
  have hfw :
      (q.comp (fderiv ℝ (fun z ↦ e z) x)) w = 1 := by
    change q
      ((fderiv ℝ (fun z ↦ e z) x)
        (fderiv ℝ (fun z ↦ e.symm z) (e x) v)) = 1
    rw [hinv']
    simp [q, v, last]
  intro hzero
  have hdual := congrArg (InnerProductSpace.toDual ℝ (ℝ^n)) hzero
  have hmap : q.comp (fderiv ℝ (fun z ↦ e z) x) = 0 := by
    simpa [chartConormal, e, q, last] using hdual
  rw [hmap] at hfw
  simp at hfw

/-- The outward unit normal supplied by a boundary chart. The negative sign
points toward decreasing flattened height, hence out of the upper half-space. -/
noncomputable def chartOutwardUnitNormal
    (i : Fin hΩ.N) (x : ℝ^n) : ℝ^n :=
  -(‖chartConormal (n := n) (Ω := Ω) i x‖)⁻¹ •
    chartConormal (n := n) (Ω := Ω) i x

/-- The outward unit normal points toward decreasing flattened height. -/
theorem chartConormal_apply_outwardUnitNormal
    (i : Fin hΩ.N) {x : ℝ^n} (hx : x ∈ (hΩ.chart i).source) :
    ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
      (fderiv ℝ (fun z ↦ hΩ.chart i z) x))
        (chartOutwardUnitNormal (n := n) (Ω := Ω) i x) =
      -‖chartConormal (n := n) (Ω := Ω) i x‖ := by
  let L : ℝ^n →L[ℝ] ℝ :=
    (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
      (fderiv ℝ (fun z ↦ hΩ.chart i z) x)
  let c := chartConormal (n := n) (Ω := Ω) i x
  have hc : c ≠ 0 :=
    chartConormal_ne_zero (n := n) (Ω := Ω) i hx
  have hdual : (InnerProductSpace.toDual ℝ (ℝ^n)) c = L := by
    dsimp [c, chartConormal, L]
    exact (InnerProductSpace.toDual ℝ (ℝ^n)).apply_symm_apply _
  have hLc : L c = ‖c‖ * ‖c‖ := by
    rw [← hdual, InnerProductSpace.toDual_apply_apply]
    exact real_inner_self_eq_norm_mul_norm c
  change L (-‖c‖⁻¹ • c) = -‖c‖
  rw [map_smul, hLc]
  simp only [smul_eq_mul]
  field_simp

/-- The chart height decreases strictly in the chartwise outward direction.

This combines the exact evaluation theorem with nonvanishing of the chart
conormal. -/
theorem chartConormal_apply_outwardUnitNormal_neg
    (i : Fin hΩ.N) {x : ℝ^n} (hx : x ∈ (hΩ.chart i).source) :
    ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
      (fderiv ℝ (fun z ↦ hΩ.chart i z) x))
        (chartOutwardUnitNormal (n := n) (Ω := Ω) i x) < 0 := by
  rw [chartConormal_apply_outwardUnitNormal
    (n := n) (Ω := Ω) i hx]
  exact neg_lt_zero.mpr <|
    norm_pos_iff.mpr <|
      chartConormal_ne_zero (n := n) (Ω := Ω) i hx

/-- The chart outward normal has unit length wherever the chart is defined. -/
theorem norm_chartOutwardUnitNormal
    (i : Fin hΩ.N) {x : ℝ^n} (hx : x ∈ (hΩ.chart i).source) :
    ‖chartOutwardUnitNormal (n := n) (Ω := Ω) i x‖ = 1 := by
  simp [chartOutwardUnitNormal, norm_smul,
    chartConormal_ne_zero (n := n) (Ω := Ω) i hx]

/-- Along the chart line `t ↦ φᵢ x + t • w`, the point eventually stays in the target of `φᵢ`
with preimage in the source of `φⱼ`, and the last coordinate of `φⱼ ∘ φᵢ⁻¹` along the line has
derivative `((Dφⱼ)ₓ ((Dφᵢ⁻¹)_{φᵢ x} w))ₙ` at `t = 0`. -/
private theorem chart_line_transition (i j : Fin hΩ.N) {x : ℝ^n}
    (hxi : x ∈ (hΩ.chart i).source) (hxj : x ∈ (hΩ.chart j).source) (w : ℝ^n) :
    (∀ᶠ t in nhds (0 : ℝ), hΩ.chart i x + t • w ∈ (hΩ.chart i).target ∧
        (hΩ.chart i).symm (hΩ.chart i x + t • w) ∈ (hΩ.chart j).source) ∧
      HasDerivAt (EuclideanSpace.proj (PDE.Common.lastIndex (n := n)) ∘
          (fun z ↦ hΩ.chart j z) ∘ (fun z ↦ (hΩ.chart i).symm z) ∘
            fun t : ℝ ↦ hΩ.chart i x + t • w)
        (EuclideanSpace.proj (PDE.Common.lastIndex (n := n)) (fderiv ℝ (fun z ↦ hΩ.chart j z) x
          (fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (hΩ.chart i x) w))) 0 := by
  have hpath : HasDerivAt (fun t : ℝ ↦ hΩ.chart i x + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add (hΩ.chart i x)
  have h0 : (hΩ.chart i).symm (hΩ.chart i x + (0 : ℝ) • w) = x := by
    simp [(hΩ.chart i).left_inv hxi]
  have hphys := ((hΩ.chart_symm_contDiff i).differentiable (by norm_num)
    (hΩ.chart i x)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp)
  refine ⟨(hpath.continuousAt.eventually_mem ((hΩ.chart i).open_target.mem_nhds
    (by simpa using (hΩ.chart i).map_source hxi))).and
      (hphys.continuousAt.eventually_mem ((hΩ.chart j).open_source.mem_nhds ?_)), ?_⟩
  · simpa only [Function.comp_apply, h0] using hxj
  · exact (EuclideanSpace.proj _).hasFDerivAt.comp_hasDerivAt 0
      (((hΩ.chart_contDiff j).differentiable (by norm_num) x).hasFDerivAt.comp_hasDerivAt_of_eq
        0 hphys (by simpa using h0.symm))

private theorem chartLastDerivative_eq_zero_of_eq_zero
    (i j : Fin hΩ.N) {x v : ℝ^n}
    (hxi : x ∈ (hΩ.chart i).source)
    (hxj : x ∈ (hΩ.chart j).source)
    (hxb : x ∈ frontier Ω)
    (hv :
      ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
        (fderiv ℝ (fun z ↦ hΩ.chart i z) x)) v = 0) :
    ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
      (fderiv ℝ (fun z ↦ hΩ.chart j z) x)) v = 0 := by
  set w : ℝ^n := fderiv ℝ (fun z ↦ hΩ.chart i z) x v
  obtain ⟨hev, hderiv⟩ := chart_line_transition i j hxi hxj w
  -- the line `φᵢ x + t • w` stays in the flat boundary, so chart `j` stays flat along it
  have hflat (t : ℝ) : (hΩ.chart i x + t • w) (PDE.Common.lastIndex (n := n)) = 0 := by
    have hy := (chartLastCoordinate_eq_zero_iff (n := n) (Ω := Ω) i hxi).2 hxb
    have hw : w (PDE.Common.lastIndex (n := n)) = 0 := hv
    simp [hy, hw]
  have hzero : (EuclideanSpace.proj (PDE.Common.lastIndex (n := n)) ∘
      (fun z ↦ hΩ.chart j z) ∘ (fun z ↦ (hΩ.chart i).symm z) ∘
        fun t : ℝ ↦ hΩ.chart i x + t • w) =ᶠ[nhds 0] fun _ ↦ 0 := by
    filter_upwards [hev] with t ⟨htT, htJ⟩
    have hj := (chartLastCoordinate_eq_zero_iff (n := n) (Ω := Ω) j htJ).2 <|
      (chartLastCoordinate_eq_zero_iff (n := n) (Ω := Ω) i ((hΩ.chart i).map_target htT)).1
        (by rw [(hΩ.chart i).right_inv htT]; exact hflat t)
    simpa using hj
  have hinv : fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (hΩ.chart i x) w = v := by
    simpa using congrArg (fun A : ℝ^n →L[ℝ] ℝ^n ↦ A v)
      (fderiv_chart_symm_comp_fderiv_chart (n := n) (Ω := Ω) i hxi)
  simpa [hinv] using hderiv.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hzero)

private theorem chartLastDerivative_eq_zero_iff
    (i j : Fin hΩ.N) {x v : ℝ^n}
    (hxi : x ∈ (hΩ.chart i).source)
    (hxj : x ∈ (hΩ.chart j).source)
    (hxb : x ∈ frontier Ω) :
    ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
        (fderiv ℝ (fun z ↦ hΩ.chart i z) x)) v = 0 ↔
      ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
        (fderiv ℝ (fun z ↦ hΩ.chart j z) x)) v = 0 := by
  constructor
  · exact chartLastDerivative_eq_zero_of_eq_zero i j hxi hxj hxb
  · exact chartLastDerivative_eq_zero_of_eq_zero j i hxj hxi hxb

private theorem chartLastDerivative_eq_pos_smul
    (i j : Fin hΩ.N) {x : ℝ^n}
    (hxi : x ∈ (hΩ.chart i).source)
    (hxj : x ∈ (hΩ.chart j).source)
    (hxb : x ∈ frontier Ω) :
    ∃ a : ℝ, 0 < a ∧
      (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
          (fderiv ℝ (fun z ↦ hΩ.chart j z) x) =
        a •
          ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
            (fderiv ℝ (fun z ↦ hΩ.chart i z) x)) := by
  let last := PDE.Common.lastIndex (n := n)
  let Li : ℝ^n →L[ℝ] ℝ :=
    (EuclideanSpace.proj last).comp
      (fderiv ℝ (fun z ↦ hΩ.chart i z) x)
  let Lj : ℝ^n →L[ℝ] ℝ :=
    (EuclideanSpace.proj last).comp
      (fderiv ℝ (fun z ↦ hΩ.chart j z) x)
  let eLast : ℝ^n := EuclideanSpace.single last 1
  let wi : ℝ^n :=
    fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (hΩ.chart i x) eLast
  have hinv := congrArg (fun A : ℝ^n →L[ℝ] ℝ^n ↦ A eLast)
    (fderiv_chart_comp_fderiv_chart_symm
      (n := n) (Ω := Ω) i hxi)
  have hLiwi : Li wi = 1 := by
    have hinv' :
        (fderiv ℝ (fun z ↦ hΩ.chart i z) x)
            (fderiv ℝ (fun z ↦ (hΩ.chart i).symm z)
              (hΩ.chart i x) eLast) = eLast := by
      simpa using hinv
    change
      (EuclideanSpace.proj last)
        ((fderiv ℝ (fun z ↦ hΩ.chart i z) x)
          (fderiv ℝ (fun z ↦ (hΩ.chart i).symm z)
            (hΩ.chart i x) eLast)) = 1
    rw [hinv']
    simp [eLast, last]
  let a : ℝ := Lj wi
  have hEq : Lj = a • Li := by
    ext v
    have hLiKernel : Li (v - (Li v) • wi) = 0 := by
      simp [hLiwi]
    have hLjKernel : Lj (v - (Li v) • wi) = 0 := by
      apply
        (chartLastDerivative_eq_zero_iff
          (n := n) (Ω := Ω) i j hxi hxj hxb).1
      simpa [Li] using hLiKernel
    rw [map_sub, map_smul] at hLjKernel
    rw [sub_eq_zero] at hLjKernel
    simpa [a, smul_eq_mul, mul_comm] using hLjKernel
  -- `a` is the slope at `0` of the height of chart `j` along the normal line of chart `i`
  obtain ⟨hev, hr⟩ := chart_line_transition i j hxi hxj eLast
  have hr0 : (EuclideanSpace.proj last ∘ (fun z ↦ hΩ.chart j z) ∘
      (fun z ↦ (hΩ.chart i).symm z) ∘ fun t : ℝ ↦ hΩ.chart i x + t • eLast) 0 = 0 := by
    simpa [(hΩ.chart i).left_inv hxi] using
      (chartLastCoordinate_eq_zero_iff (n := n) (Ω := Ω) j hxj).2 hxb
  have hslopeNonneg : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      0 ≤ t⁻¹ • ((EuclideanSpace.proj last ∘ (fun z ↦ hΩ.chart j z) ∘
          (fun z ↦ (hΩ.chart i).symm z) ∘ fun t : ℝ ↦ hΩ.chart i x + t • eLast) t -
        (EuclideanSpace.proj last ∘ (fun z ↦ hΩ.chart j z) ∘
          (fun z ↦ (hΩ.chart i).symm z) ∘ fun t : ℝ ↦ hΩ.chart i x + t • eLast) 0) := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with t ⟨htT, htJ⟩ (ht : 0 < t)
    -- for `t > 0` the line point lies in the open upper half-space, so in `Ω`
    have htΩ : (hΩ.chart i).symm (hΩ.chart i x + t • eLast) ∈ Ω := by
      refine (hΩ.chart_mem_iff_upper i _ ((hΩ.chart i).map_target htT)).2 ?_
      rw [(hΩ.chart i).right_inv htT]
      change 0 < (hΩ.chart i x + t • eLast) last
      simpa [eLast, last, (chartLastCoordinate_eq_zero_iff (n := n) (Ω := Ω) i hxi).2 hxb]
        using ht
    rw [hr0, sub_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 ht.le) (by
      simpa using ((chartLastCoordinate_pos_iff (n := n) (Ω := Ω) j htJ).2 htΩ).le)
  have haNonneg : 0 ≤ a := by
    simpa [a, Lj, wi] using ge_of_tendsto hr.tendsto_slope_zero_right
      (by simpa only [zero_add] using hslopeNonneg)
  have haNe : a ≠ 0 := by
    intro ha
    have hLiwiZero :
        ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
            (fderiv ℝ (fun z ↦ hΩ.chart i z) x)) wi = 0 :=
      (chartLastDerivative_eq_zero_iff (n := n) (Ω := Ω) i j hxi hxj hxb).2 <| by
        simpa [Lj] using (show Lj wi = 0 from ha)
    have : Li wi = 0 := by simpa [Li] using hLiwiZero
    linarith
  exact ⟨a, lt_of_le_of_ne haNonneg (Ne.symm haNe), by simpa [Li, Lj] using hEq⟩

/-- Conormals from two boundary charts differ by a positive scalar on their
overlap. In particular, the atlas determines a coherent orientation. -/
theorem chartConormal_eq_pos_smul
    (i j : Fin hΩ.N) {x : ℝ^n}
    (hxi : x ∈ (hΩ.chart i).source)
    (hxj : x ∈ (hΩ.chart j).source)
    (hxb : x ∈ frontier Ω) :
    ∃ a : ℝ, 0 < a ∧
      chartConormal (n := n) (Ω := Ω) j x =
        a • chartConormal (n := n) (Ω := Ω) i x := by
  obtain ⟨a, ha, hcovector⟩ :=
    chartLastDerivative_eq_pos_smul
      (n := n) (Ω := Ω) i j hxi hxj hxb
  refine ⟨a, ha, ?_⟩
  apply (InnerProductSpace.toDual ℝ (ℝ^n)).injective
  simp [chartConormal, hcovector]

/-- Normalized outward normals from overlapping charts agree. -/
theorem chartOutwardUnitNormal_eq
    (i j : Fin hΩ.N) {x : ℝ^n}
    (hxi : x ∈ (hΩ.chart i).source)
    (hxj : x ∈ (hΩ.chart j).source)
    (hxb : x ∈ frontier Ω) :
    chartOutwardUnitNormal (n := n) (Ω := Ω) i x =
      chartOutwardUnitNormal (n := n) (Ω := Ω) j x := by
  obtain ⟨a, ha, hconormal⟩ :=
    chartConormal_eq_pos_smul
      (n := n) (Ω := Ω) i j hxi hxj hxb
  rw [chartOutwardUnitNormal, chartOutwardUnitNormal, hconormal]
  simp only [neg_smul, neg_inj]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, smul_smul]
  congr 1
  field_simp

/-- The intrinsic outward unit normal on the boundary of an operational
`C¹` domain. Chart independence is proved by
`outwardUnitNormal_eq_chart`. -/
noncomputable def outwardUnitNormal (x : frontier Ω) : ℝ^n :=
  chartOutwardUnitNormal (n := n) (Ω := Ω)
    (Classical.choose
      (exists_chart_source_of_mem_frontier (n := n) (Ω := Ω) x.property))
    x

/-- The intrinsic outward normal agrees with every chart containing the
boundary point. -/
theorem outwardUnitNormal_eq_chart
    (x : frontier Ω) (i : Fin hΩ.N)
    (hxi : (x : ℝ^n) ∈ (hΩ.chart i).source) :
    outwardUnitNormal (n := n) (Ω := Ω) x =
      chartOutwardUnitNormal (n := n) (Ω := Ω) i x := by
  let j :=
    Classical.choose
      (exists_chart_source_of_mem_frontier (n := n) (Ω := Ω) x.property)
  have hxj : (x : ℝ^n) ∈ (hΩ.chart j).source :=
    Classical.choose_spec
      (exists_chart_source_of_mem_frontier (n := n) (Ω := Ω) x.property)
  exact chartOutwardUnitNormal_eq
    (n := n) (Ω := Ω) j i hxj hxi x.property

/-- The intrinsic outward normal has unit length. -/
theorem norm_outwardUnitNormal (x : frontier Ω) :
    ‖outwardUnitNormal (n := n) (Ω := Ω) x‖ = 1 := by
  let i :=
    Classical.choose
      (exists_chart_source_of_mem_frontier (n := n) (Ω := Ω) x.property)
  have hxi : (x : ℝ^n) ∈ (hΩ.chart i).source :=
    Classical.choose_spec
      (exists_chart_source_of_mem_frontier (n := n) (Ω := Ω) x.property)
  rw [outwardUnitNormal_eq_chart (n := n) (Ω := Ω) x i hxi]
  exact norm_chartOutwardUnitNormal (n := n) (Ω := Ω) i hxi

end Trace.C1
end SobolevSpace
