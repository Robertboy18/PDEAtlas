/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Core
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Physicalization
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.CompactSupport
public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.Assembly
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.ClassicalRepresentative

/-!
# Trace operator on an operational C¹ domain

The `p = 2` case of the trace theorem for a bounded `C¹` domain (Evans, PDE, §5.5): a bounded
linear operator `T : H¹(Ω) → L²(∂Ω)` with `T u = u|_{∂Ω}` for `u` smooth up to the boundary.
The operator is built from the flat half-space trace of `Trace.HalfSpace`, the boundary atlas,
and the chartwise comparison of surface measures.

A test function supported inside `Ω` has zero trace, hence by continuity
`H¹₀(Ω) ⊆ ker T`. The reverse inclusion is `trace_eq_zero_iff_mem_H10` in `Trace.C1.ZeroTrace`.

## Main results

* `flattenedClassicalPiece`, `flattenCLM_eq_classicalPiece`: the explicit flattened form of a
  smooth localized piece and its agreement with the abstract flattening operator.
* `localFlatTrace`, `localPhysicalTrace`: the trace of one localized piece, with bounds
  `norm_localFlatTrace_le` and `norm_localPhysicalTrace_le`.
* `trace`: the global operator `H¹(Ω) → L²(∂Ω)`.
* `trace_apply_ae`, `trace_classical`: the chart formula and agreement with restriction on smooth
  data.
* `trace_testFunctionOn_eq_zero`, `traceOnH10_eq_zero`, `trace_coe_H10_eq_zero`: the trace
  vanishes on `H¹₀(Ω)`.
* `norm_trace_le`: the quantitative bound in terms of the chart data.

## How it works

We follow the localization in Evans's proof but take the density step on the half-space. The
boundary cutoffs `ψᵢ` of the atlas, which sum to `1` on `∂Ω` because the interior cutoff vanishes
there, cut `u` into pieces `ψᵢ u` supported in chart sources. We flatten each piece by its chart to
an `H¹` function on the upper half-space (`Extension.C1.BoundaryPiece.flattenCLM`), apply the flat
trace of `Trace.HalfSpace`, which is already defined on all of `H¹(ℝ^n₊)`, and carry the result back
to the boundary patch by `chartPhysicalization`, which is bounded because the chart distorts surface
measure by a finite factor; `trace` is the sum of these finitely many pieces. Evans proves the
estimate for `u ∈ C¹(Ū)` and then extends `T` using the density of `C^∞(Ū)` in `W^{1,p}(U)` (§5.3.3,
Theorem 3), which we do not need. For a smooth compactly supported `φ`, each flattened piece is the
explicit `C¹` function `flattenedClassicalPiece`, whose flat trace is literal restriction; this is
how `trace_classical` identifies `T φ` with `φ|_{∂Ω}`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1 and its proof, pp. 272-273, and Theorem 2,
  pp. 273-275, for the characterization of the kernel of the trace.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace
namespace Trace.C1

open MeasureTheory Set
open scoped NNReal ENNReal Sobolev


/-- The classical `i`-th localized function in flattened coordinates.  The
auxiliary target cutoff makes the total representative compactly supported
without changing it where the partition piece can be nonzero. -/
noncomputable def flattenedClassicalPiece
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) : ℝ^(m + 1) → ℝ :=
  fun y ↦
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
      (n := m + 1) (Ω := Ω) i).toFun y *
      (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) *
      φ.1.toFun ((hΩ.chart i).symm y)

/-- A C¹ chart sends smooth data to C¹ data; the target cutoff supplies
compact support. -/
theorem flattenedClassicalPiece_contDiff
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    ContDiff ℝ 1 (flattenedClassicalPiece
      (m := m) (Ω := Ω) i φ) := by
  have hη : ContDiff ℝ 1
      (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
        (n := m + 1) (Ω := Ω) i).toFun :=
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
      (n := m + 1) (Ω := Ω) i).contDiff.of_le (by simp)
  have hψ : ContDiff ℝ 1
      (fun y ↦ (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y)) := by
    simpa [Function.comp_def] using
      ((hΩ.boundaryCutoff i).contDiff.of_le (by simp)).comp
        (hΩ.chart_symm_contDiff i)
  have hφ : ContDiff ℝ 1
      (fun y ↦ φ.1.toFun ((hΩ.chart i).symm y)) := by
    simpa [Function.comp_def] using
      (φ.1.contDiff.of_le (by simp)).comp (hΩ.chart_symm_contDiff i)
  change ContDiff ℝ 1 (fun y ↦
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
      (n := m + 1) (Ω := Ω) i).toFun y *
      (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) *
      φ.1.toFun ((hΩ.chart i).symm y))
  exact (hη.mul hψ).mul hφ

/-- The flattened classical piece has compact support, inherited from the target cutoff factor. -/
theorem flattenedClassicalPiece_hasCompactSupport
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    HasCompactSupport (flattenedClassicalPiece
      (m := m) (Ω := Ω) i φ) := by
  have hη :=
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
      (n := m + 1) (Ω := Ω) i).hasCompactSupport
  change HasCompactSupport (fun y ↦
    (Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff
      (n := m + 1) (Ω := Ω) i).toFun y *
      (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) *
      φ.1.toFun ((hΩ.chart i).symm y))
  exact hη.mul_right.mul_right

/-- On a physical boundary patch, the flattened classical piece is exactly
the localized value `ψᵢ φ` after applying the chart. -/
theorem flattenedClassicalPiece_chart_apply
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) {x : ℝ^(m + 1)}
    (hx : x ∈ (hΩ.chart i).source ∩ frontier Ω) :
    flattenedClassicalPiece (m := m) (Ω := Ω) i φ (hΩ.chart i x) =
      (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x := by
  have hxSource : x ∈ (hΩ.chart i).source := hx.1
  by_cases hψ : (hΩ.boundaryCutoff i).toFun x = 0
  · simp [flattenedClassicalPiece, (hΩ.chart i).left_inv hxSource, hψ]
  · have hxK : x ∈ Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupport
        (n := m + 1) (Ω := Ω) i := by
      exact subset_tsupport _ hψ
    have hyK : hΩ.chart i x ∈
        Boundary.C1ExtensionAtlas.DerivedCutoffs.boundarySupportInTarget
          (n := m + 1) (Ω := Ω) i :=
      ⟨x, hxK, rfl⟩
    have hη :=
      Boundary.C1ExtensionAtlas.DerivedCutoffs.targetSupportCutoff_eq_one_on_boundarySupportInTarget
        (n := m + 1) (Ω := Ω) i (hΩ.chart i x) hyK
    simp [flattenedClassicalPiece, hη, (hΩ.chart i).left_inv hxSource]

/-- The flattened classical chart expression as an element of the reusable
compact-C¹ source space. -/
noncomputable def flattenedClassicalPieceC1
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    Trace.HalfSpace.CompactSupport.c1CompactSubmodule m :=
  ⟨flattenedClassicalPiece (m := m) (Ω := Ω) i φ,
    flattenedClassicalPiece_contDiff (m := m) (Ω := Ω) i φ,
    flattenedClassicalPiece_hasCompactSupport (m := m) (Ω := Ω) i φ⟩

/-- For classical input, the abstract chart-flattening operator is exactly
the Sobolev embedding of the compact C¹ chart expression. -/
theorem flattenCLM_eq_classicalPiece
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    Extension.C1.BoundaryPiece.flattenCLM
        (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ) =
      Trace.HalfSpace.CompactSupport.toUpperH1
        (flattenedClassicalPieceC1 (m := m) (Ω := Ω) i φ) := by
  let U := globalTestFunctionToDomainW1pLinear
    (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ
  let F := Extension.C1.BoundaryPiece.flattenCLM
    (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i U
  let q := flattenedClassicalPieceC1 (m := m) (Ω := Ω) i φ
  apply GraphSpace.WkpSpaceOn.ext_of_base_ae
    (HalfSpace.isOpen_upper (n := m + 1))
  have hU :
      ((((U : GraphSpace.WkpAmbientOn (m + 1) 1 2 Ω)
          (GraphSpace.baseIndex (m + 1) 1) : GraphSpace.DerivLp (m + 1) 2 Ω) :
          ℝ^(m + 1) → ℝ)) =ᵐ[domainMeasure (m + 1) Ω] φ.1.toFun := by
    rw [show U = GraphSpace.mkWkpSpaceOnOfContDiff
      (n := m + 1) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω)
      (f := φ.1.toFun) φ.1.contDiff
      φ.1.hasCompactSupport by
        exact globalTestFunctionToDomainW1pLinear_eq_mk
          (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ]
    simpa [GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      (GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
        (n := m + 1) (k := 1) (p := (2 : ℝ≥0∞)) (Ω := Ω)
        (f := φ.1.toFun) φ.1.contDiff
        φ.1.hasCompactSupport (GraphSpace.baseIndex (m + 1) 1))
  have hF := Extension.C1.BoundaryPiece.flattenCLM_base_eq_classical_ae
    (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i U φ.1.toFun hU
  have hq := Trace.HalfSpace.CompactSupport.toUpperH1_coordinate_ae q
    (GraphSpace.baseIndex (m + 1) 1)
  have hF' :
      (((F : GraphSpace.WkpAmbientOn (m + 1) 1 2
          (HalfSpace.upper (m + 1))) (GraphSpace.baseIndex (m + 1) 1) :
          GraphSpace.DerivLp (m + 1) 2 (HalfSpace.upper (m + 1))) :
          ℝ^(m + 1) → ℝ) =ᵐ[
        domainMeasure (m + 1) (HalfSpace.upper (m + 1))]
      flattenedClassicalPiece (m := m) (Ω := Ω) i φ := by
    exact hF
  have hq' :
      ((((Trace.HalfSpace.CompactSupport.toUpperH1 q :
          GraphSpace.WkpAmbientOn (m + 1) 1 2 (HalfSpace.upper (m + 1)))
          (GraphSpace.baseIndex (m + 1) 1) :
          GraphSpace.DerivLp (m + 1) 2 (HalfSpace.upper (m + 1))) :
          ℝ^(m + 1) → ℝ)) =ᵐ[
        domainMeasure (m + 1) (HalfSpace.upper (m + 1))]
      flattenedClassicalPiece (m := m) (Ω := Ω) i φ := by
    simpa [q, flattenedClassicalPieceC1,
      GraphSpace.baseIndex_toList, iteratedPartialDeriv] using hq
  exact hF'.trans hq'.symm

/-- The trace of the `i`-th localized Sobolev field in flattened boundary
coordinates. -/
noncomputable def localFlatTrace
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) :
    H¹(Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2
        (Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m)) :=
  (Boundary.Geometry.SurfaceMeasure.flatTrace (n := m)).comp
    (Extension.C1.BoundaryPiece.flattenCLM
      (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i)

/-- On smooth classical input, the localized flat trace is represented by
the compact C¹ chart expression. -/
theorem localFlatTrace_classical_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    (localFlatTrace (m := m) (Ω := Ω) i
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ) :
      ℝ^(m + 1) → ℝ) =ᵐ[Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m)]
      flattenedClassicalPiece (m := m) (Ω := Ω) i φ := by
  change (Boundary.Geometry.SurfaceMeasure.flatTrace (n := m)
      (Extension.C1.BoundaryPiece.flattenCLM
        (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ)) :
      ℝ^(m + 1) → ℝ) =ᵐ[Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m)] _
  rw [flattenCLM_eq_classicalPiece (m := m) (Ω := Ω) i φ]
  exact Trace.HalfSpace.CompactSupport.flatTrace_c1_apply_ae
    (flattenedClassicalPieceC1 (m := m) (Ω := Ω) i φ)

/-- Quantitative bound for each localized flattened trace. -/
theorem norm_localFlatTrace_le
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (u : H¹(Ω)) :
    ‖localFlatTrace (m := m) (Ω := Ω) i u‖ ≤
      ‖Extension.C1.BoundaryPiece.flattenCLM
        (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i‖ * ‖u‖ := by
  have htrace := Boundary.Geometry.SurfaceMeasure.norm_flatTrace_le
    ((Extension.C1.BoundaryPiece.flattenCLM
      (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i) u)
  have hflatten := (Extension.C1.BoundaryPiece.flattenCLM
    (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i).le_opNorm u
  calc
    ‖localFlatTrace (m := m) (Ω := Ω) i u‖ ≤
        ‖(Extension.C1.BoundaryPiece.flattenCLM
          (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i) u‖ := htrace
    _ ≤ _ := hflatten

/-- One physical localized boundary trace. -/
noncomputable def localPhysicalTrace
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) :
    H¹(Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
  (chartPhysicalization (m := m) (Ω := Ω) (2 : ℝ≥0∞) i).comp
    (localFlatTrace (m := m) (Ω := Ω) i)

/-- Almost-everywhere chart formula for one physical localized trace. -/
theorem localPhysicalTrace_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (u : H¹(Ω)) :
    (localPhysicalTrace (m := m) (Ω := Ω) i u : ℝ^(m + 1) → ℝ) =ᵐ[
      Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
        (fun x ↦ localFlatTrace (m := m) (Ω := Ω) i u (hΩ.chart i x)) :=
  chartPhysicalization_apply_ae (m := m) (Ω := Ω) (2 : ℝ≥0∞) i
    (localFlatTrace (m := m) (Ω := Ω) i u)

/-- For smooth classical input, one physical chart contribution is precisely
the localized boundary value `ψᵢ φ`, extended by zero off its patch. -/
theorem localPhysicalTrace_classical_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    (localPhysicalTrace (m := m) (Ω := Ω) i
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ) :
      ℝ^(m + 1) → ℝ) =ᵐ[Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
        (fun x ↦ (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x) := by
  let A := chartBoundaryPatch (m := m) (Ω := Ω) i
  let μ := Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω
  let ρ := chartPushedSurfaceMeasure (m := m) (Ω := Ω) i
  let u := globalTestFunctionToDomainW1pLinear
    (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ
  let g := localFlatTrace (m := m) (Ω := Ω) i u
  let q := flattenedClassicalPiece (m := m) (Ω := Ω) i φ
  have hAmeas : MeasurableSet A :=
    measurableSet_chartBoundaryPatch (m := m) (Ω := Ω) i
  have hle : ρ ≤
      (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ≥0∞) •
        Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m) :=
    chartPushedSurfaceMeasure_le (m := m) (Ω := Ω) i
  have hflat : (g : ℝ^(m + 1) → ℝ) =ᵐ[
      Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m)] q := by
    simpa [g, q, u] using
      localFlatTrace_classical_apply_ae (m := m) (Ω := Ω) i φ
  have hflatρ : (g : ℝ^(m + 1) → ℝ) =ᵐ[ρ] q :=
    (Measure.absolutelyContinuous_of_le_smul hle).ae_eq hflat
  have hmp : MeasurePreserving (hΩ.chart i) (μ.restrict A) ρ :=
    measurePreserving_chart_boundaryPatch (m := m) (Ω := Ω) i
  have hcomp := hmp.quasiMeasurePreserving.ae hflatρ
  have hrestrict :
      (fun x ↦ g (hΩ.chart i x)) =ᵐ[μ.restrict A]
        fun x ↦ (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x := by
    filter_upwards [hcomp, MeasureTheory.ae_restrict_mem hAmeas] with x hx hxA
    rw [hx]
    exact flattenedClassicalPiece_chart_apply
      (m := m) (Ω := Ω) i φ hxA
  have hind : A.indicator (fun x ↦ g (hΩ.chart i x)) =ᵐ[μ]
      A.indicator (fun x ↦ (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x) :=
    (ae_eq_restrict_iff_indicator_ae_eq hAmeas).mp hrestrict
  exact (localPhysicalTrace_apply_ae (m := m) (Ω := Ω) i u).trans
    (by simpa [A, μ, g] using hind)

/-- Explicit bound for one physical localized trace. -/
theorem norm_localPhysicalTrace_le
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (i : Fin hΩ.N) (u : H¹(Ω)) :
    ‖localPhysicalTrace (m := m) (Ω := Ω) i u‖ ≤
      (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
          (1 / (2 : ℝ≥0∞)).toReal *
        ‖Extension.C1.BoundaryPiece.flattenCLM
          (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i‖ * ‖u‖ := by
  have hp := norm_chartPhysicalization_apply_le
    (m := m) (Ω := Ω) (2 : ℝ≥0∞) i
    (localFlatTrace (m := m) (Ω := Ω) i u)
  have hl := norm_localFlatTrace_le (m := m) (Ω := Ω) i u
  calc
    ‖localPhysicalTrace (m := m) (Ω := Ω) i u‖ ≤
        (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
            (1 / (2 : ℝ≥0∞)).toReal *
          ‖localFlatTrace (m := m) (Ω := Ω) i u‖ := hp
    _ ≤ (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
          (1 / (2 : ℝ≥0∞)).toReal *
        (‖Extension.C1.BoundaryPiece.flattenCLM
          (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i‖ * ‖u‖) := by
      gcongr
    _ = _ := by ring

/-- The `p = 2` case of the global trace operator of Evans §5.5 on a bounded operational `C¹`
domain, assembled from the finitely many localized boundary charts, with source `H¹ = W^{1,2}` and
target `L²(∂Ω)`. The finite-exponent version is `Trace.C1.traceLp`. -/
noncomputable def trace
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω] :
    H¹(Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
  ∑ i : Fin hΩ.N, localPhysicalTrace (m := m) (Ω := Ω) i

private theorem sum_localPhysicalTrace_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (u : H¹(Ω)) (s : Finset (Fin hΩ.N)) :
    ((∑ i ∈ s, localPhysicalTrace (m := m) (Ω := Ω) i u :
        MeasureTheory.Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)) :
      ℝ^(m + 1) → ℝ) =ᵐ[Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      fun x ↦ ∑ i ∈ s,
        (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
          (fun z ↦ localFlatTrace (m := m) (Ω := Ω) i u (hΩ.chart i z)) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [MeasureTheory.Lp.coeFn_zero ℝ 2
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)] with x hx
      simpa using hx
  | @insert i s hi ih =>
      have hadd := MeasureTheory.Lp.coeFn_add
        (localPhysicalTrace (m := m) (Ω := Ω) i u)
        (∑ j ∈ s, localPhysicalTrace (m := m) (Ω := Ω) j u)
      have hlocal := localPhysicalTrace_apply_ae (m := m) (Ω := Ω) i u
      filter_upwards [hadd, hlocal, ih] with x hxadd hxlocal hxsum
      simp only [Finset.sum_insert hi]
      rw [hxadd]
      change
        (localPhysicalTrace (m := m) (Ω := Ω) i u : ℝ^(m + 1) → ℝ) x +
            ((∑ j ∈ s, localPhysicalTrace (m := m) (Ω := Ω) j u :
              MeasureTheory.Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)) :
              ℝ^(m + 1) → ℝ) x = _
      rw [hxlocal, hxsum]

/-- Almost-everywhere chart formula for the assembled global trace. -/
theorem trace_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (u : H¹(Ω)) :
    (trace (m := m) (Ω := Ω) u : ℝ^(m + 1) → ℝ) =ᵐ[
      Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      fun x ↦ ∑ i : Fin hΩ.N,
        (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
          (fun z ↦ localFlatTrace (m := m) (Ω := Ω) i u (hΩ.chart i z)) x := by
  simpa [trace] using
    sum_localPhysicalTrace_apply_ae (m := m) (Ω := Ω) u Finset.univ

/-- The completed global trace agrees with literal restriction of every
ambient smooth compactly supported function to `∂Ω`. -/
theorem trace_classical
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (φ : Trace.HalfSpace.GlobalTestFunction m) :
    trace (m := m) (Ω := Ω)
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ) =
      globalTestFunctionBoundaryLpLinear
        (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ := by
  apply MeasureTheory.Lp.ext
  let u := globalTestFunctionToDomainW1pLinear
    (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ
  have htrace := trace_apply_ae (m := m) (Ω := Ω) u
  have hlocal : ∀ᵐ x ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω,
      ∀ i : Fin hΩ.N,
        (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
            (fun z ↦ localFlatTrace (m := m) (Ω := Ω) i u
              (hΩ.chart i z)) x =
          (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
            (fun z ↦ (hΩ.boundaryCutoff i).toFun z * φ.1.toFun z) x := by
    apply MeasureTheory.ae_all_iff.2
    intro i
    exact (localPhysicalTrace_apply_ae (m := m) (Ω := Ω) i u).symm.trans
      (localPhysicalTrace_classical_apply_ae (m := m) (Ω := Ω) i φ)
  have hboundary := globalTestFunctionBoundaryLpLinear_apply_ae
    (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ
  have hfrontier : ∀ᵐ x ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω,
      x ∈ frontier Ω := by
    simpa [Boundary.Geometry.SurfaceMeasure.surfaceMeasure] using
      (MeasureTheory.ae_restrict_mem
        (μ := Measure.euclideanHausdorffMeasure m)
        (s := frontier Ω) isClosed_frontier.measurableSet)
  filter_upwards [htrace, hlocal, hboundary, hfrontier] with
      x hxtrace hxlocal hxboundary hxfrontier
  rw [hxtrace, hxboundary]
  simp_rw [hxlocal]
  have hpatch : ∀ i : Fin hΩ.N,
      (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
          (fun z ↦ (hΩ.boundaryCutoff i).toFun z * φ.1.toFun z) x =
        (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x := by
    intro i
    by_cases hxSource : x ∈ (hΩ.chart i).source
    · have hxPatch : x ∈ chartBoundaryPatch (m := m) (Ω := Ω) i :=
        ⟨hxSource, hxfrontier⟩
      rw [Set.indicator_of_mem hxPatch]
    · have hψ : (hΩ.boundaryCutoff i).toFun x = 0 := by
        by_contra hne
        exact hxSource (hΩ.boundaryCutoff_support i (subset_tsupport _ hne))
      rw [Set.indicator_of_notMem]
      · simp [hψ]
      · exact fun hxPatch ↦ hxSource hxPatch.1
  simp_rw [hpatch, ← Finset.sum_mul]
  rw [sum_boundary_partition_eq_one (n := m + 1) (Ω := Ω) hxfrontier]
  simp

/-- A smooth function compactly supported inside `Ω` has zero boundary
trace. -/
theorem trace_testFunctionOn_eq_zero
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (φ : GraphSpace.TestFunctionOn (m + 1) Ω) :
    trace (m := m) (Ω := Ω)
        (GraphSpace.testFunctionToH1
          (n := m + 1) (Ω := Ω) φ) = 0 := by
  let Φ : Trace.HalfSpace.GlobalTestFunction m := ⟨φ.1, Set.subset_univ _⟩
  have hinput :
      globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (2 : ℝ≥0∞) Φ =
        GraphSpace.testFunctionToH1
          (n := m + 1) (Ω := Ω) φ := by
    rw [globalTestFunctionToDomainW1pLinear_eq_mk]
    rfl
  rw [← hinput, trace_classical]
  apply MeasureTheory.Lp.ext
  have hboundary := globalTestFunctionBoundaryLpLinear_apply_ae
    (m := m) (Ω := Ω) (2 : ℝ≥0∞) Φ
  have hfrontier : ∀ᵐ x ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω,
      x ∈ frontier Ω := by
    simpa [Boundary.Geometry.SurfaceMeasure.surfaceMeasure] using
      (MeasureTheory.ae_restrict_mem
        (μ := Measure.euclideanHausdorffMeasure m)
        (s := frontier Ω) isClosed_frontier.measurableSet)
  have hzero := MeasureTheory.Lp.coeFn_zero ℝ 2
    (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)
  filter_upwards [hboundary, hfrontier, hzero] with
      x hxboundary hxfrontier hxzero
  rw [hxboundary, hxzero]
  have hxNot : x ∉ Ω := by
    rw [hΩ.isOpen.frontier_eq] at hxfrontier
    exact hxfrontier.2
  have hφzero : φ.1.toFun x = 0 := by
    by_contra hne
    exact hxNot (φ.2 (subset_tsupport _ hne))
  exact hφzero

/-- Trace restricted to `H¹₀(Ω)`. -/
noncomputable def traceOnH10
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω] :
    H¹₀(Ω) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
  (trace (m := m) (Ω := Ω)).comp
    (GraphSpace.h10SubmoduleOn
      (n := m + 1) (Ω := Ω)).toSubmodule.subtypeL

/-- The inclusion `H¹₀(Ω) ⊆ ker(trace)` for the trace assembled from
`Boundary.C1ExtensionAtlas`. -/
theorem traceOnH10_eq_zero
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω] :
    traceOnH10 (m := m) (Ω := Ω) = 0 := by
  let e := GraphSpace.testFunctionToH10Linear
    (n := m + 1) (Ω := Ω)
  have hcomp : (traceOnH10 (m := m) (Ω := Ω) :
      H¹₀(Ω) →
        MeasureTheory.Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)) ∘ e =
      (0 : H¹₀(Ω) →L[ℝ]
        MeasureTheory.Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)) ∘ e := by
    funext φ
    change trace (m := m) (Ω := Ω)
        (GraphSpace.testFunctionToH1
          (n := m + 1) (Ω := Ω) φ) = 0
    exact trace_testFunctionOn_eq_zero (m := m) (Ω := Ω) φ
  have hfun :=
    (GraphSpace.denseRange_testFunctionToH10Linear
      (n := m + 1) (Ω := Ω)).equalizer
      (traceOnH10 (m := m) (Ω := Ω)).continuous
      (0 : H¹₀(Ω) →L[ℝ]
        MeasureTheory.Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)).continuous hcomp
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- Every `H¹₀(Ω)` function has zero trace in `L²(∂Ω)` on a `C¹` domain. -/
theorem trace_coe_H10_eq_zero
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (u : H¹₀(Ω)) :
    trace (m := m) (Ω := Ω) (u : H¹(Ω)) = 0 := by
  change traceOnH10 (m := m) (Ω := Ω) u = 0
  rw [traceOnH10_eq_zero]
  rfl

/-- Quantitative global trace estimate. -/
theorem norm_trace_le
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (u : H¹(Ω)) :
    ‖trace (m := m) (Ω := Ω) u‖ ≤
      (∑ i : Fin hΩ.N,
        (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
            (1 / (2 : ℝ≥0∞)).toReal *
          ‖Extension.C1.BoundaryPiece.flattenCLM
            (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i‖) * ‖u‖ := by
  calc
    ‖trace (m := m) (Ω := Ω) u‖ =
        ‖∑ i : Fin hΩ.N, localPhysicalTrace (m := m) (Ω := Ω) i u‖ := by
      simp [trace]
    _ ≤ ∑ i : Fin hΩ.N,
        ‖localPhysicalTrace (m := m) (Ω := Ω) i u‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin hΩ.N,
        ((chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
            (1 / (2 : ℝ≥0∞)).toReal *
          ‖Extension.C1.BoundaryPiece.flattenCLM
            (n := m + 1) (p := (2 : ℝ≥0∞)) (Ω := Ω) i‖ * ‖u‖) := by
      exact Finset.sum_le_sum fun i _ ↦
        norm_localPhysicalTrace_le (m := m) (Ω := Ω) i u
    _ = _ := by rw [Finset.sum_mul]

end Trace.C1
end SobolevSpace
