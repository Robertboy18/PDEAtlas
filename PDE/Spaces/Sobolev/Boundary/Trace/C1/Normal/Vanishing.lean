/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal

/-!
# Derivatives of functions vanishing on the boundary

A differentiable function which vanishes locally on a C¹ boundary has zero
derivative along every tangent direction. Consequently its derivative is
a scalar multiple of the chart conormal. The proof differentiates
curves in the boundary, and requires no ambient second derivative.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1

open Filter Set
open scoped Topology

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- A function locally zero on the boundary has zero derivative in every
chart tangent direction. -/
theorem derivative_eq_zero_of_vanishing_on_frontier
    (i : Fin hΩ.N) {x v : ℝ^n} (hx : x ∈ (hΩ.chart i).source)
    (hxb : x ∈ frontier Ω) {f : ℝ^n → ℝ} {f' : ℝ^n →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hzero : ∀ᶠ y in 𝓝 x, y ∈ frontier Ω → f y = 0)
    (hv : (fderiv ℝ (fun z ↦ hΩ.chart i z) x v)
      (PDE.Common.lastIndex (n := n)) = 0) :
    f' v = 0 := by
  let e := hΩ.chart i
  let y := e x
  let w := fderiv ℝ (fun z ↦ e z) x v
  let path : ℝ → ℝ^n := fun t ↦ y + t • w
  have hp : HasDerivAt path w 0 := by
    simpa [path] using ((hasDerivAt_id (x := (0 : ℝ))).smul_const w).const_add y
  have hptarget : ∀ᶠ t in 𝓝 (0 : ℝ), path t ∈ e.target :=
    hp.continuousAt.eventually (by
      simpa [path, y] using e.open_target.mem_nhds (e.map_source hx))
  have hphysical0 : e.symm (path 0) = x := by
    simp [path, y, e.left_inv hx]
  have hs : HasFDerivAt (fun z ↦ e.symm z)
      (fderiv ℝ (fun z ↦ e.symm z) y) (path 0) := by
    simpa [path] using
      ((hΩ.chart_symm_contDiff i).differentiable one_ne_zero y).hasFDerivAt
  have hphysical := hs.comp_hasDerivAt 0 hp
  have hphysicalDeriv : fderiv ℝ (fun z ↦ e.symm z) y w = v := by
    have h := congrArg (fun A : ℝ^n →L[ℝ] ℝ^n ↦ A v)
      (fderiv_chart_symm_comp_fderiv_chart i hx)
    exact h
  have hboundary : ∀ᶠ t in 𝓝 (0 : ℝ), e.symm (path t) ∈ frontier Ω := by
    filter_upwards [hptarget] with t ht
    apply (chart_mem_boundary_iff (n := n) (Ω := Ω) i (e.map_target ht)).mp
    rw [e.right_inv ht]
    change path t (PDE.Common.lastIndex (n := n)) = 0
    have hy : y (PDE.Common.lastIndex (n := n)) = 0 :=
      (chartLastCoordinate_eq_zero_iff i hx).mpr hxb
    simp [path, hy, w, e, hv]
  have hz : (fun t ↦ f (e.symm (path t))) =ᶠ[𝓝 (0 : ℝ)] fun _ ↦ 0 := by
    have hpzero : ∀ᶠ t in 𝓝 (0 : ℝ),
        e.symm (path t) ∈ frontier Ω → f (e.symm (path t)) = 0 :=
      hphysical.continuousAt.eventually (by simpa [hphysical0] using hzero)
    filter_upwards [hpzero, hboundary] with t ht hb
    exact ht hb
  have hf0 : HasFDerivAt f f' (e.symm (path 0)) := by rwa [hphysical0]
  have hd := (hf0.comp_hasDerivAt 0 hphysical).congr_of_eventuallyEq hz.symm
  have heq := hd.unique (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ)))
  simpa only [hphysicalDeriv] using heq

/-- The derivative of a function locally zero on the boundary is a scalar
multiple of the unnormalized chart normal covector. -/
theorem derivative_eq_smul_conormal_of_vanishing_on_frontier
    (i : Fin hΩ.N) {x : ℝ^n} (hx : x ∈ (hΩ.chart i).source)
    (hxb : x ∈ frontier Ω) {f : ℝ^n → ℝ} {f' : ℝ^n →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hzero : ∀ᶠ y in 𝓝 x, y ∈ frontier Ω → f y = 0) :
    ∃ a : ℝ, f' = a •
      ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
        (fderiv ℝ (fun z ↦ hΩ.chart i z) x)) := by
  let q := (EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
    (fderiv ℝ (fun z ↦ hΩ.chart i z) x)
  let w := fderiv ℝ (fun z ↦ (hΩ.chart i).symm z) (hΩ.chart i x)
    (EuclideanSpace.single (PDE.Common.lastIndex (n := n)) 1)
  have hqw : q w = 1 := by
    have h := congrArg
      (fun A : ℝ^n →L[ℝ] ℝ^n ↦
        A (EuclideanSpace.single (PDE.Common.lastIndex (n := n)) 1))
      (fderiv_chart_comp_fderiv_chart_symm i hx)
    change (fderiv ℝ (fun z ↦ hΩ.chart i z) x w)
      (PDE.Common.lastIndex (n := n)) = 1
    rw [show fderiv ℝ (fun z ↦ hΩ.chart i z) x w =
      EuclideanSpace.single (PDE.Common.lastIndex (n := n)) 1 from h]
    simp
  refine ⟨f' w, ?_⟩
  ext v
  have hqv : q (v - q v • w) = 0 := by simp [hqw]
  have hfv := derivative_eq_zero_of_vanishing_on_frontier i hx hxb hf hzero hqv
  rw [map_sub, map_smul, sub_eq_zero] at hfv
  simpa only [smul_apply, smul_eq_mul, mul_comm] using hfv

/-- The gradient of a differentiable function locally zero on the
boundary is its normal derivative times the outward unit normal. -/
theorem gradient_eq_normal_smul_of_vanishing_on_frontier
    {x : ℝ^n} (hxb : x ∈ frontier Ω) {f : ℝ^n → ℝ} {f' : ℝ^n →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hzero : ∀ᶠ y in 𝓝 x, y ∈ frontier Ω → f y = 0) :
    (InnerProductSpace.toDual ℝ (ℝ^n)).symm f' =
      inner ℝ ((InnerProductSpace.toDual ℝ (ℝ^n)).symm f')
        (outwardUnitNormal (Ω := Ω) ⟨x, hxb⟩) •
          outwardUnitNormal (Ω := Ω) ⟨x, hxb⟩ := by
  obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier (Ω := Ω) hxb
  obtain ⟨a, ha⟩ :=
    derivative_eq_smul_conormal_of_vanishing_on_frontier i hi hxb hf hzero
  let c := chartConormal (Ω := Ω) i x
  have hc : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr (chartConormal_ne_zero i hi)
  have hg : (InnerProductSpace.toDual ℝ (ℝ^n)).symm f' = a • c := by
    rw [ha, map_smul]
    rfl
  have hgν : (InnerProductSpace.toDual ℝ (ℝ^n)).symm f' =
      (-a * ‖c‖) • chartOutwardUnitNormal (Ω := Ω) i x := by
    rw [hg, chartOutwardUnitNormal, smul_smul]
    change a • c = ((-a * ‖c‖) * -‖c‖⁻¹) • c
    congr 1
    field_simp
  rw [outwardUnitNormal_eq_chart _ i hi, hgν]
  simp [inner_smul_left, norm_chartOutwardUnitNormal i hi]

end SobolevSpace.Trace.C1
