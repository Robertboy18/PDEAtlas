/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Vanishing

/-!
# The outward normal from a local defining function

A differentiable defining function which is nonnegative inside the domain
and zero on its boundary has inward-pointing derivative. If this derivative
is nonzero, its negative Riesz vector, normalized to unit length, is the
intrinsic outward normal. Only local first-order data are used.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1

open Filter Set
open scoped Topology

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- A nondegenerate defining function which is nonnegative inside the domain
has derivative positively proportional to the chart height derivative. -/
theorem derivative_eq_pos_smul_conormal_of_defining_function
    (i : Fin hΩ.N) {x : ℝ^n} (hx : x ∈ (hΩ.chart i).source)
    (hxb : x ∈ frontier Ω) {f : ℝ^n → ℝ} {f' : ℝ^n →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x) (hne : f' ≠ 0)
    (hzero : ∀ᶠ y in 𝓝 x, y ∈ frontier Ω → f y = 0)
    (hpos : ∀ᶠ y in 𝓝 x, y ∈ Ω → 0 ≤ f y) :
    ∃ a : ℝ, 0 < a ∧ f' = a •
      ((EuclideanSpace.proj (PDE.Common.lastIndex (n := n))).comp
        (fderiv ℝ (fun z ↦ hΩ.chart i z) x)) := by
  obtain ⟨a, ha⟩ :=
    derivative_eq_smul_conormal_of_vanishing_on_frontier i hx hxb hf hzero
  have hane : a ≠ 0 := by
    intro hz
    exact hne (by simpa [hz] using ha)
  let e := hΩ.chart i
  let last := PDE.Common.lastIndex (n := n)
  let v : ℝ^n := EuclideanSpace.single last 1
  let path : ℝ → ℝ^n := fun t ↦ e x + t • v
  have hp : HasDerivAt path v 0 := by
    simpa [path] using ((hasDerivAt_id (x := (0 : ℝ))).smul_const v).const_add (e x)
  have hp0 : path 0 = e x := by simp [path]
  have hs : HasFDerivAt (fun z ↦ e.symm z)
      (fderiv ℝ (fun z ↦ e.symm z) (e x)) (path 0) := by
    rw [hp0]
    exact ((hΩ.chart_symm_contDiff i).differentiable one_ne_zero _).hasFDerivAt
  have hphysical := hs.comp_hasDerivAt 0 hp
  have hphysical0 : e.symm (path 0) = x := by rw [hp0, e.left_inv hx]
  have hf0 : HasFDerivAt f f' (e.symm (path 0)) := by rwa [hphysical0]
  have hd := hf0.comp_hasDerivAt 0 hphysical
  have hq : (fderiv ℝ (fun z ↦ e z) x)
      (fderiv ℝ (fun z ↦ e.symm z) (e x) v) = v :=
    congrArg (fun A : ℝ^n →L[ℝ] ℝ^n ↦ A v)
      (fderiv_chart_comp_fderiv_chart_symm i hx)
  have hderiv : f' (fderiv ℝ (fun z ↦ e.symm z) (e x) v) = a := by
    rw [ha]
    change a * ((fderiv ℝ (fun z ↦ e z) x)
      (fderiv ℝ (fun z ↦ e.symm z) (e x) v)) last = a
    rw [hq]
    simp [v]
  have hfx : f x = 0 := hzero.self_of_nhds hxb
  have htarget : ∀ᶠ t in 𝓝 (0 : ℝ), path t ∈ e.target :=
    hp.continuousAt.eventually (by
      rw [hp0]
      exact e.open_target.mem_nhds (e.map_source hx))
  have hpositive : ∀ᶠ t in 𝓝 (0 : ℝ),
      e.symm (path t) ∈ Ω → 0 ≤ f (e.symm (path t)) :=
    hphysical.continuousAt.eventually (by
      simpa only [Function.comp_apply, hphysical0] using hpos)
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ t⁻¹ • (f (e.symm (path t)) - f (e.symm (path 0))) := by
    filter_upwards [htarget.filter_mono nhdsWithin_le_nhds,
      hpositive.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hft htpos
    have htin : e.symm (path t) ∈ Ω := by
      apply (hΩ.chart_mem_iff_upper i _ (e.map_target ht)).mpr
      rw [e.right_inv ht]
      change 0 < path t last
      have hxlast : e x last = 0 :=
        (chartLastCoordinate_eq_zero_iff i hx).mpr hxb
      simpa [path, hxlast, v] using htpos
    rw [hphysical0, hfx, sub_zero]
    exact mul_nonneg (inv_nonneg.mpr htpos.le) (hft htin)
  have hnonneg : 0 ≤ f' (fderiv ℝ (fun z ↦ e.symm z) (e x) v) :=
    ge_of_tendsto hd.tendsto_slope_zero_right (by
      simpa only [zero_add, Function.comp_apply] using hslope)
  exact ⟨a, lt_of_le_of_ne (hderiv ▸ hnonneg) hane.symm, ha⟩

/-- The normalized negative gradient of a nondegenerate local defining
function is the outward unit normal. -/
theorem outwardUnitNormal_eq_of_defining_function
    {x : ℝ^n} (hxb : x ∈ frontier Ω) {f : ℝ^n → ℝ} {f' : ℝ^n →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x) (hne : f' ≠ 0)
    (hzero : ∀ᶠ y in 𝓝 x, y ∈ frontier Ω → f y = 0)
    (hpos : ∀ᶠ y in 𝓝 x, y ∈ Ω → 0 ≤ f y) :
    outwardUnitNormal (Ω := Ω) ⟨x, hxb⟩ =
      -‖(InnerProductSpace.toDual ℝ (ℝ^n)).symm f'‖⁻¹ •
        (InnerProductSpace.toDual ℝ (ℝ^n)).symm f' := by
  obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier (Ω := Ω) hxb
  obtain ⟨a, ha, hderiv⟩ :=
    derivative_eq_pos_smul_conormal_of_defining_function i hi hxb hf hne hzero hpos
  have hc : (InnerProductSpace.toDual ℝ (ℝ^n)).symm f' =
      a • chartConormal (Ω := Ω) i x := by
    rw [hderiv, map_smul]
    rfl
  rw [outwardUnitNormal_eq_chart _ i hi, hc, chartOutwardUnitNormal,
    norm_smul, Real.norm_eq_abs, abs_of_pos ha, smul_smul]
  congr 1
  field_simp

end SobolevSpace.Trace.C1
