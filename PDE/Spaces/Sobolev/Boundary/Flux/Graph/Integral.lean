/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.Graph.Normal
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Normal.Flux
import PDE.Analysis.MeasureTheory.AreaFormula.C1

/-!
# Signed boundary integration on a graph patch

The C¹ epigraph derivative formula is transported through the area formula
to Euclidean Hausdorff measure. A compactly supported function localized to
a graph patch has the same volume and boundary integrals on the physical
domain. The outward normal in the localized conclusion is intrinsic.

`integral_fderiv_eq_normalFlux_of_graph_patch` is the Gauss–Green formula (1) of Evans App. C.2,
Theorem 1(i), in direction `v`, for `f` that is C¹ with compact support in one graph patch;
`GaussGreen.Scalar` sums these local formulas over a smooth partition of unity. The change of
variables to the graph is the area formula `integral_image_eq_integral_normDet_smul_of_contDiffOn`
for the graph parametrization, whose Jacobian factor times the outward normal is computed by
`normDet_linearGraphTangent_smul_outwardNormal`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, App. C.2, Theorem 1(i), (1), p. 711.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Boundary.Flux.Graph

open Set MeasureTheory Trace.HalfSpace Trace.C1 Geometry.SurfaceMeasure

variable {m : ℕ}

/-- Gauss–Green above a C¹ graph: for a linear equivalence `A`, a C¹ function `g` and a C¹
function `f` with compact support, the integral of `∂_v f` over `linearEpigraph A g` equals the
integral of `f (v · ν)` over its frontier for the Hausdorff measure of dimension `m`, where `ν` is
the outward unit normal `linearGraphOutwardNormal A g` at the tangential coordinates of `A x`. -/
theorem integral_linearEpigraph_fderiv_eq_surfaceIntegral
    (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1)) {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g)
    {f : ℝ^(m + 1) → ℝ} (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (v : ℝ^(m + 1)) :
    ∫ x in linearEpigraph A g, fderiv ℝ f x v =
      ∫ x in frontier (linearEpigraph A g),
        f x * inner ℝ v (linearGraphOutwardNormal A g (splitTangentialNormal (A x)).1)
          ∂Measure.euclideanHausdorffMeasure m := by
  let H : ℝ^(m + 1) → ℝ := fun x ↦
    f x * inner ℝ v (linearGraphOutwardNormal A g (splitTangentialNormal (A x)).1)
  have hH : Continuous H := hf.continuous.mul
    (continuous_const.inner (𝕜 := ℝ)
      ((continuous_linearGraphOutwardNormal A hg).comp
        (tangentialNormalContinuousLinearEquiv.continuous.fst.comp A.continuous)))
  have harea := integral_image_eq_integral_normDet_smul_of_contDiffOn isOpen_univ
    (contDiff_linearGraphParametrization A hg).contDiffOn
    (linearGraphParametrization_injective A g).injOn
    (fun y _ ↦ by
      rw [(hasFDerivAt_linearGraphParametrization A hg y).fderiv]
      exact linearGraphTangent_injective A g y) H hH.aestronglyMeasurable
  simp only [image_univ, range_linearGraphParametrization A g hg.continuous,
    finrank_euclideanSpace_fin, setIntegral_univ] at harea
  change (∫ x in linearEpigraph A g, fderiv ℝ f x v) = _
  rw [harea, integral_linearEpigraph_fderiv A hg hf hcompact v, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [(hasFDerivAt_linearGraphParametrization A hg y).fderiv]
  have hν := normDet_linearGraphTangent_smul_outwardNormal A g y
  have hinner := congrArg (fun z : ℝ^(m + 1) ↦ inner ℝ v z) hν
  have hc : inner ℝ v (linearGraphConormal A g y) = linearGraphCovector A g y v := by
    rw [real_inner_comm, linearGraphConormal, InnerProductSpace.toDual_symm_apply]
  have hp : (splitTangentialNormal (A (linearGraphParametrization A g y))).1 = y := by
    simp [linearGraphParametrization]
  simp only [inner_smul_right, hc, linearGraphCovector_apply] at hinner
  change |A.symm.toLinearMap.det| *
      (((fderiv ℝ g y) (splitTangentialNormal (A v)).1 - (A v) (Fin.last m)) *
        f (linearGraphParametrization A g y)) =
      (linearGraphTangent A g y).toLinearMap.normDet *
        (f (linearGraphParametrization A g y) *
          inner ℝ v (linearGraphOutwardNormal A g
            (splitTangentialNormal (A (linearGraphParametrization A g y))).1))
  rw [hp]
  nlinarith [congrArg (fun r : ℝ ↦ f (linearGraphParametrization A g y) * r) hinner]

/-- Directional Gauss–Green for a function supported in one graph patch: if `Ω` carries a
`C1ExtensionAtlas`, `U` is open and `Ω ∩ U = linearEpigraph A g ∩ U` for a C¹ function `g`, and
`f` is C¹ with compact support in `U`, then `∫_Ω ∂_v f = ∫_{∂Ω} f (v · ν) dS` for the outward unit
normal and surface measure of `Ω`. -/
theorem integral_fderiv_eq_normalFlux_of_graph_patch
    {Ω U : Set (ℝ^(m + 1))} [hΩ : C1ExtensionAtlas (m + 1) Ω]
    (hU : IsOpen U) (A : ℝ^(m + 1) ≃L[ℝ] ℝ^(m + 1))
    {g : ℝ^m → ℝ} (hg : ContDiff ℝ 1 g)
    (hside : ∀ x ∈ U, x ∈ Ω ↔ x ∈ linearEpigraph A g)
    {f : ℝ^(m + 1) → ℝ} (hf : ContDiff ℝ 1 f) (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ U) (v : ℝ^(m + 1)) :
    ∫ x in Ω, fderiv ℝ f x v =
      ∫ x, normalFlux (Ω := Ω) (fun y ↦ f y • v) x ∂surfaceMeasure Ω := by
  classical
  have hvolume :
      ∫ x in Ω, fderiv ℝ f x v =
        ∫ x in linearEpigraph A g, fderiv ℝ f x v := by
    rw [← integral_indicator hΩ.isOpen.measurableSet,
      ← integral_indicator (isOpen_linearEpigraph A g hg.continuous).measurableSet]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport f
    · have heq := hside x (hsupport hx)
      by_cases hxin : x ∈ Ω
      · simp [hxin, heq.mp hxin]
      · have hxout : x ∉ linearEpigraph A g := fun h ↦ hxin (heq.mpr h)
        simp [hxin, hxout]
    · by_cases hxin : x ∈ Ω <;> by_cases hxepi : x ∈ linearEpigraph A g <;>
        simp [hxin, hxepi, fderiv_of_notMem_tsupport ℝ hx]
  rw [hvolume, integral_linearEpigraph_fderiv_eq_surfaceIntegral A hg hf hcompact v]
  change (∫ x in frontier (linearEpigraph A g),
    f x * inner ℝ v (linearGraphOutwardNormal A g (splitTangentialNormal (A x)).1)
      ∂Measure.euclideanHausdorffMeasure m) =
    ∫ x in frontier Ω, normalFlux (Ω := Ω) (fun y ↦ f y • v) x
      ∂Measure.euclideanHausdorffMeasure m
  rw [← integral_indicator isClosed_frontier.measurableSet,
    ← integral_indicator isClosed_frontier.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport f
  · have hxU := hsupport hx
    have heq := hU.mem_frontier_iff_of_local_eq hside hxU
    by_cases hxb : x ∈ frontier Ω
    · simp only [indicator_of_mem (heq.mp hxb), indicator_of_mem hxb,
        normalFlux_eq_inner _ hxb, inner_smul_left, starRingEnd_apply, star_trivial,
        outwardUnitNormal_eq_linearGraph hU A hg hside hxU hxb]
    · have hxout : x ∉ frontier (linearEpigraph A g) := fun h ↦ hxb (heq.mpr h)
      simp [hxb, hxout]
  · have hfx := image_eq_zero_of_notMem_tsupport hx
    by_cases hxb : x ∈ frontier Ω <;>
      by_cases hxepi : x ∈ frontier (linearEpigraph A g) <;>
        simp [hxb, hxepi, hfx, normalFlux]

end SobolevSpace.Boundary.Flux.Graph
