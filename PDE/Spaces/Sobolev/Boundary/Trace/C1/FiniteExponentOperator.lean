/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Operator
public import PDE.Spaces.Sobolev.Boundary.Geometry.FiniteExponentSurfaceMeasure
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.ClassicalRepresentative

/-!
# Finite-exponent trace on an operational `C¹` domain

This construction covers `1 ≤ p < ∞`, including the endpoint `W^{1,1} → L¹` trace.

The trace theorem for a bounded `C¹` domain (Evans, PDE, §5.5) provides a bounded linear operator
`T : W^{1,p}(Ω) → Lᵖ(∂Ω)` which agrees with restriction to `∂Ω` on functions that are
continuous up to the boundary, and whose kernel is `W^{1,p}_0(Ω)`. We construct `T`,
for real exponents `1 ≤ p`, from the flat finite-exponent trace on the half-space: the boundary
cutoffs `ψᵢ` of the atlas, which sum to `1` on `∂Ω` because the interior cutoff vanishes there,
cut `u` into pieces `ψᵢ u` supported in chart sources; each piece is flattened by its chart,
traced on the hyperplane, transported back to the physical boundary patch by
`chartPhysicalization`, and the finitely many contributions are summed.

We obtain the operator, its explicit norm bound in terms of the chart data, the
almost-everywhere chart formula for its values, the identity `T u = u|_{∂Ω}` for globally
smooth compactly supported `u`, and the inclusion `W^{1,p}_0(Ω) ⊆ ker T`. The reverse inclusion
(Evans' characterization of trace-zero functions) is proved in `Trace.C1.ZeroTrace`. At `p = 1`,
the flat trace bound is one; the global bound also includes the localization and chart norms.

At `p = 2` the finite-exponent operator agrees with the Hilbert
trace `Trace.C1.trace` under the canonical identifications `W^{1,2} ≃ H¹` and
`L^{ofReal 2} ≃ L²`.

## Main results

* `localFlatTraceLp`, `localPhysicalTraceLp`: the trace of one localized piece, in flat and in
  physical coordinates, with the bounds `norm_localFlatTraceLp_le` and
  `norm_localPhysicalTraceLp_le`.
* `traceLp`: the global operator `W^{1,p}(Ω) → Lᵖ(∂Ω)`.
* `traceLp_apply_ae`, `traceLp_classical`: the chart formula and agreement with restriction on
  smooth data.
* `traceLp_testFunctionOn_eq_zero`, `traceLpOnW1p0_eq_zero`, `traceLp_coe_W1p0_eq_zero`: the
  trace vanishes on `W^{1,p}_0(Ω)`.
* `norm_traceLp_le`: the quantitative bound.
* `boundaryLpTwoEquivL2_traceLp`: compatibility with the Hilbert trace at `p = 2`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1 and its proof, pp. 272-273, for the trace
  operator, and Theorem 2, pp. 273-275, for the characterization of its kernel as `W^{1,p}_0(U)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.C1

open MeasureTheory Set
open scoped NNReal ENNReal Sobolev

/-- For classical input, finite-exponent chart flattening is exactly the
Sobolev embedding of the compact `C1` chart expression. -/
theorem flattenCLM_eq_classicalPieceLp
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    Extension.C1.BoundaryPiece.flattenCLM
        (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal p) φ) =
      Trace.HalfSpace.CompactSupport.toUpperW1p p
        (flattenedClassicalPieceC1 (m := m) (Ω := Ω) i φ) := by
  let U := globalTestFunctionToDomainW1pLinear
    (m := m) (Ω := Ω) (ENNReal.ofReal p) φ
  let F := Extension.C1.BoundaryPiece.flattenCLM
    (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i U
  let q := flattenedClassicalPieceC1 (m := m) (Ω := Ω) i φ
  apply GraphSpace.WkpSpaceOn.ext_of_base_ae
    (HalfSpace.isOpen_upper (n := m + 1))
  have hU :
      ((((U : GraphSpace.WkpAmbientOn (m + 1) 1
          (ENNReal.ofReal p) Ω) (GraphSpace.baseIndex (m + 1) 1) :
          GraphSpace.DerivLp (m + 1) (ENNReal.ofReal p) Ω) :
          ℝ^(m + 1) → ℝ)) =ᵐ[domainMeasure (m + 1) Ω]
        φ.1.toFun := by
    rw [show U = GraphSpace.mkWkpSpaceOnOfContDiff
      (n := m + 1) (k := 1) (p := ENNReal.ofReal p) (Ω := Ω)
      (f := φ.1.toFun) φ.1.contDiff
      φ.1.hasCompactSupport by
        exact globalTestFunctionToDomainW1pLinear_eq_mk
          (m := m) (Ω := Ω) (ENNReal.ofReal p) φ]
    simpa [GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      (GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae
        (n := m + 1) (k := 1) (p := ENNReal.ofReal p) (Ω := Ω)
        (f := φ.1.toFun) φ.1.contDiff
        φ.1.hasCompactSupport (GraphSpace.baseIndex (m + 1) 1))
  have hF := Extension.C1.BoundaryPiece.flattenCLM_base_eq_classical_ae
    (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i U φ.1.toFun hU
  have hq := Trace.HalfSpace.CompactSupport.toUpperW1p_coordinate_ae p q
    (GraphSpace.baseIndex (m + 1) 1)
  have hF' :
      (((F : GraphSpace.WkpAmbientOn (m + 1) 1 (ENNReal.ofReal p)
          (HalfSpace.upper (m + 1))) (GraphSpace.baseIndex (m + 1) 1) :
          GraphSpace.DerivLp (m + 1) (ENNReal.ofReal p)
            (HalfSpace.upper (m + 1))) :
          ℝ^(m + 1) → ℝ) =ᵐ[
        domainMeasure (m + 1) (HalfSpace.upper (m + 1))]
      flattenedClassicalPiece (m := m) (Ω := Ω) i φ := by
    exact hF
  have hq' :
      ((((Trace.HalfSpace.CompactSupport.toUpperW1p p q :
          GraphSpace.WkpAmbientOn (m + 1) 1 (ENNReal.ofReal p)
            (HalfSpace.upper (m + 1)))
          (GraphSpace.baseIndex (m + 1) 1) :
          GraphSpace.DerivLp (m + 1) (ENNReal.ofReal p)
            (HalfSpace.upper (m + 1))) :
          ℝ^(m + 1) → ℝ)) =ᵐ[
        domainMeasure (m + 1) (HalfSpace.upper (m + 1))]
      flattenedClassicalPiece (m := m) (Ω := Ω) i φ := by
    simpa [q, flattenedClassicalPieceC1,
      GraphSpace.baseIndex_toList, iteratedPartialDeriv] using hq
  exact hF'.trans hq'.symm

/-- The finite-exponent trace of the `i`-th localized Sobolev field in
flattened boundary coordinates. -/
noncomputable def localFlatTraceLp
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (i : Fin hΩ.N) :
    W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
      MeasureTheory.Lp ℝ (ENNReal.ofReal p)
        (Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m)) :=
  (Boundary.Geometry.SurfaceMeasure.flatTraceLp m p).comp
    (Extension.C1.BoundaryPiece.flattenCLM
      (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i)

/-- On smooth classical input, the localized finite-exponent flat trace is
represented by the compact `C¹` chart expression. -/
theorem localFlatTraceLp_classical_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    (localFlatTraceLp (m := m) (Ω := Ω) p i
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal p) φ) :
      ℝ^(m + 1) → ℝ) =ᵐ[
        Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m)]
      flattenedClassicalPiece (m := m) (Ω := Ω) i φ := by
  change (Boundary.Geometry.SurfaceMeasure.flatTraceLp m p
      (Extension.C1.BoundaryPiece.flattenCLM
        (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal p) φ)) :
      ℝ^(m + 1) → ℝ) =ᵐ[
        Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m)] _
  rw [flattenCLM_eq_classicalPieceLp
    (m := m) (Ω := Ω) p i φ]
  exact Boundary.Geometry.SurfaceMeasure.flatTraceLp_c1_apply_ae p
    (flattenedClassicalPieceC1 (m := m) (Ω := Ω) i φ)

/-- Quantitative bound for each localized finite-exponent flattened trace. -/
theorem norm_localFlatTraceLp_le
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    ‖localFlatTraceLp (m := m) (Ω := Ω) p i u‖ ≤
      p ^ (1 / p) *
        ‖Extension.C1.BoundaryPiece.flattenCLM
          (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i‖ * ‖u‖ := by
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.mp Fact.out
  have htrace := Boundary.Geometry.SurfaceMeasure.norm_flatTraceLp_le
    m p
    ((Extension.C1.BoundaryPiece.flattenCLM
      (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i) u)
  have hflatten := (Extension.C1.BoundaryPiece.flattenCLM
    (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i).le_opNorm u
  calc
    ‖localFlatTraceLp (m := m) (Ω := Ω) p i u‖ ≤
        p ^ (1 / p) *
          ‖(Extension.C1.BoundaryPiece.flattenCLM
            (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i) u‖ :=
      htrace
    _ ≤ p ^ (1 / p) *
        (‖Extension.C1.BoundaryPiece.flattenCLM
          (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i‖ * ‖u‖) := by
      gcongr
    _ = _ := by ring

/-- One physical localized finite-exponent boundary trace. -/
noncomputable def localPhysicalTraceLp
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (i : Fin hΩ.N) :
    W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
      MeasureTheory.Lp ℝ (ENNReal.ofReal p)
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
  (chartPhysicalization (m := m) (Ω := Ω) (ENNReal.ofReal p) i).comp
    (localFlatTraceLp (m := m) (Ω := Ω) p i)

/-- Representative formula for one physical finite-exponent chart trace. -/
theorem localPhysicalTraceLp_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    (localPhysicalTraceLp (m := m) (Ω := Ω) p i u :
      ℝ^(m + 1) → ℝ) =ᵐ[
        Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
        (fun x ↦
          localFlatTraceLp (m := m) (Ω := Ω) p i u
            (hΩ.chart i x)) :=
  chartPhysicalization_apply_ae (m := m) (Ω := Ω) (ENNReal.ofReal p) i
    (localFlatTraceLp (m := m) (Ω := Ω) p i u)

/-- For smooth classical input, one physical finite-exponent chart
contribution is the localized boundary value, extended by zero. -/
theorem localPhysicalTraceLp_classical_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (i : Fin hΩ.N) (φ : Trace.HalfSpace.GlobalTestFunction m) :
    (localPhysicalTraceLp (m := m) (Ω := Ω) p i
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal p) φ) :
      ℝ^(m + 1) → ℝ) =ᵐ[
        Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
        (fun x ↦ (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x) := by
  let A := chartBoundaryPatch (m := m) (Ω := Ω) i
  let μ := Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω
  let ρ := chartPushedSurfaceMeasure (m := m) (Ω := Ω) i
  let u := globalTestFunctionToDomainW1pLinear
    (m := m) (Ω := Ω) (ENNReal.ofReal p) φ
  let g := localFlatTraceLp (m := m) (Ω := Ω) p i u
  let q := flattenedClassicalPiece (m := m) (Ω := Ω) i φ
  have hAmeas : MeasurableSet A :=
    measurableSet_chartBoundaryPatch (m := m) (Ω := Ω) i
  have hle : ρ ≤
      (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ≥0∞) •
        Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m) :=
    chartPushedSurfaceMeasure_le (m := m) (Ω := Ω) i
  have hflat :
      (g : ℝ^(m + 1) → ℝ) =ᵐ[
        Boundary.Geometry.SurfaceMeasure.flatSurfaceMeasure (n := m)] q := by
    simpa [g, q, u] using
      localFlatTraceLp_classical_apply_ae
        (m := m) (Ω := Ω) p i φ
  have hflatρ : (g : ℝ^(m + 1) → ℝ) =ᵐ[ρ] q :=
    (Measure.absolutelyContinuous_of_le_smul hle).ae_eq hflat
  have hmp : MeasurePreserving (hΩ.chart i) (μ.restrict A) ρ :=
    measurePreserving_chart_boundaryPatch (m := m) (Ω := Ω) i
  have hcomp := hmp.quasiMeasurePreserving.ae hflatρ
  have hrestrict :
      (fun x ↦ g (hΩ.chart i x)) =ᵐ[μ.restrict A]
        fun x ↦ (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x := by
    filter_upwards [hcomp, MeasureTheory.ae_restrict_mem hAmeas] with
      x hx hxA
    rw [hx]
    exact flattenedClassicalPiece_chart_apply
      (m := m) (Ω := Ω) i φ hxA
  have hind :
      A.indicator (fun x ↦ g (hΩ.chart i x)) =ᵐ[μ]
        A.indicator
          (fun x ↦ (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x) :=
    (ae_eq_restrict_iff_indicator_ae_eq hAmeas).mp hrestrict
  exact
    (localPhysicalTraceLp_apply_ae
      (m := m) (Ω := Ω) p i u).trans
      (by simpa [A, μ, g] using hind)

/-- Explicit bound for one physical localized finite-exponent trace. -/
theorem norm_localPhysicalTraceLp_le
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (i : Fin hΩ.N)
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    ‖localPhysicalTraceLp (m := m) (Ω := Ω) p i u‖ ≤
      (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
          (1 / ENNReal.ofReal p).toReal *
        p ^ (1 / p) *
        ‖Extension.C1.BoundaryPiece.flattenCLM
          (n := m + 1) (p := ENNReal.ofReal p) (Ω := Ω) i‖ * ‖u‖ := by
  have hphysical := norm_chartPhysicalization_apply_le
    (m := m) (Ω := Ω) (ENNReal.ofReal p) i
    (localFlatTraceLp (m := m) (Ω := Ω) p i u)
  have hflat := norm_localFlatTraceLp_le
    (m := m) (Ω := Ω) p i u
  calc
    ‖localPhysicalTraceLp (m := m) (Ω := Ω) p i u‖ ≤
        (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
            (1 / ENNReal.ofReal p).toReal *
          ‖localFlatTraceLp (m := m) (Ω := Ω) p i u‖ :=
      hphysical
    _ ≤ (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
          (1 / ENNReal.ofReal p).toReal *
        (p ^ (1 / p) *
          ‖Extension.C1.BoundaryPiece.flattenCLM
            (n := m + 1) (p := ENNReal.ofReal p)
            (Ω := Ω) i‖ * ‖u‖) := by
      gcongr
    _ = _ := by ring

/-- The global `L^p` trace on a bounded operational `C¹` domain, assembled from
its finitely many localized boundary charts for `1 ≤ p`. -/
noncomputable def traceLp
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
      MeasureTheory.Lp ℝ (ENNReal.ofReal p)
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
  ∑ i : Fin hΩ.N, localPhysicalTraceLp
    (m := m) (Ω := Ω) p i

private theorem sum_localPhysicalTraceLp_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (u : W^{1,ENNReal.ofReal p}(Ω))
    (s : Finset (Fin hΩ.N)) :
    ((∑ i ∈ s,
        localPhysicalTraceLp (m := m) (Ω := Ω) p i u :
        MeasureTheory.Lp ℝ (ENNReal.ofReal p)
          (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)) :
      ℝ^(m + 1) → ℝ) =ᵐ[
        Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      fun x ↦ ∑ i ∈ s,
        (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
          (fun z ↦
            localFlatTraceLp (m := m) (Ω := Ω) p i u
              (hΩ.chart i z)) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [
        MeasureTheory.Lp.coeFn_zero ℝ (ENNReal.ofReal p)
          (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)] with x hx
      simpa using hx
  | @insert i s hi ih =>
      have hadd := MeasureTheory.Lp.coeFn_add
        (localPhysicalTraceLp (m := m) (Ω := Ω) p i u)
        (∑ j ∈ s,
          localPhysicalTraceLp (m := m) (Ω := Ω) p j u)
      have hlocal := localPhysicalTraceLp_apply_ae
        (m := m) (Ω := Ω) p i u
      filter_upwards [hadd, hlocal, ih] with
        x hxadd hxlocal hxsum
      simp only [Finset.sum_insert hi]
      rw [hxadd]
      change
        (localPhysicalTraceLp
            (m := m) (Ω := Ω) p i u : ℝ^(m + 1) → ℝ) x +
            ((∑ j ∈ s,
              localPhysicalTraceLp
                (m := m) (Ω := Ω) p j u :
              MeasureTheory.Lp ℝ (ENNReal.ofReal p)
                (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)) :
              ℝ^(m + 1) → ℝ) x = _
      rw [hxlocal, hxsum]

/-- Almost-everywhere chart formula for the global finite-exponent trace. -/
theorem traceLp_apply_ae
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    (traceLp (m := m) (Ω := Ω) p u :
      ℝ^(m + 1) → ℝ) =ᵐ[
        Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω]
      fun x ↦ ∑ i : Fin hΩ.N,
        (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
          (fun z ↦
            localFlatTraceLp (m := m) (Ω := Ω) p i u
              (hΩ.chart i z)) x := by
  simpa [traceLp] using
    sum_localPhysicalTraceLp_apply_ae
      (m := m) (Ω := Ω) p u Finset.univ

/-- The global finite-exponent trace agrees with literal restriction of every
ambient smooth compactly supported function to the boundary. -/
theorem traceLp_classical
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (φ : Trace.HalfSpace.GlobalTestFunction m) :
    traceLp (m := m) (Ω := Ω) p
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal p) φ) =
      globalTestFunctionBoundaryLpLinear
        (m := m) (Ω := Ω) (ENNReal.ofReal p) φ := by
  apply MeasureTheory.Lp.ext
  let u := globalTestFunctionToDomainW1pLinear
    (m := m) (Ω := Ω) (ENNReal.ofReal p) φ
  have htrace := traceLp_apply_ae
    (m := m) (Ω := Ω) p u
  have hlocal :
      ∀ᵐ x ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω,
        ∀ i : Fin hΩ.N,
          (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
              (fun z ↦
                localFlatTraceLp (m := m) (Ω := Ω) p i u
                  (hΩ.chart i z)) x =
            (chartBoundaryPatch (m := m) (Ω := Ω) i).indicator
              (fun z ↦
                (hΩ.boundaryCutoff i).toFun z * φ.1.toFun z) x := by
    apply MeasureTheory.ae_all_iff.2
    intro i
    exact
      (localPhysicalTraceLp_apply_ae
        (m := m) (Ω := Ω) p i u).symm.trans
        (localPhysicalTraceLp_classical_apply_ae
          (m := m) (Ω := Ω) p i φ)
  have hboundary := globalTestFunctionBoundaryLpLinear_apply_ae
    (m := m) (Ω := Ω) (ENNReal.ofReal p) φ
  have hfrontier :
      ∀ᵐ x ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω,
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
    · have hxPatch :
          x ∈ chartBoundaryPatch (m := m) (Ω := Ω) i :=
        ⟨hxSource, hxfrontier⟩
      rw [Set.indicator_of_mem hxPatch]
    · have hcutoff : (hΩ.boundaryCutoff i).toFun x = 0 := by
        by_contra hne
        exact hxSource
          (hΩ.boundaryCutoff_support i (subset_tsupport _ hne))
      rw [Set.indicator_of_notMem]
      · simp [hcutoff]
      · exact fun hxPatch ↦ hxSource hxPatch.1
  simp_rw [hpatch, ← Finset.sum_mul]
  rw [sum_boundary_partition_eq_one
    (n := m + 1) (Ω := Ω) hxfrontier]
  simp

/-- A smooth function compactly supported inside the domain has zero
finite-exponent boundary trace. -/
theorem traceLp_testFunctionOn_eq_zero
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (φ : GraphSpace.TestFunctionOn (m + 1) Ω) :
    traceLp (m := m) (Ω := Ω) p
        (GraphSpace.testFunctionToWkp
          (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := Ω) φ) = 0 := by
  let Φ : Trace.HalfSpace.GlobalTestFunction m :=
    ⟨φ.1, Set.subset_univ _⟩
  have hinput :
      globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal p) Φ =
        GraphSpace.testFunctionToWkp
          (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := Ω) φ := by
    rw [globalTestFunctionToDomainW1pLinear_eq_mk]
    rfl
  rw [← hinput, traceLp_classical (m := m) (Ω := Ω) p Φ]
  apply MeasureTheory.Lp.ext
  have hboundary := globalTestFunctionBoundaryLpLinear_apply_ae
    (m := m) (Ω := Ω) (ENNReal.ofReal p) Φ
  have hfrontier :
      ∀ᵐ x ∂Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω,
        x ∈ frontier Ω := by
    simpa [Boundary.Geometry.SurfaceMeasure.surfaceMeasure] using
      (MeasureTheory.ae_restrict_mem
        (μ := Measure.euclideanHausdorffMeasure m)
        (s := frontier Ω) isClosed_frontier.measurableSet)
  have hzero := MeasureTheory.Lp.coeFn_zero ℝ (ENNReal.ofReal p)
    (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)
  filter_upwards [hboundary, hfrontier, hzero] with
    x hxboundary hxfrontier hxzero
  rw [hxboundary, hxzero]
  have hxNot : x ∉ Ω := by
    rw [hΩ.isOpen.frontier_eq] at hxfrontier
    exact hxfrontier.2
  by_contra hne
  exact hxNot (φ.2 (subset_tsupport _ hne))

/-- The finite-exponent trace restricted to the supported-core completion
`W^{1,p}_0(Ω)`. -/
noncomputable def traceLpOnW1p0
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    W₀^{1,(ENNReal.ofReal p)}(Ω) →L[ℝ]
      MeasureTheory.Lp ℝ (ENNReal.ofReal p)
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
  (traceLp (m := m) (Ω := Ω) p).comp
    (GraphSpace.wkp0SubmoduleOn
      (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := Ω)).toSubmodule.subtypeL

/-- Every `W^{1,p}_0(Ω)` function has zero trace. -/
theorem traceLpOnW1p0_eq_zero
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    traceLpOnW1p0 (m := m) (Ω := Ω) p = 0 := by
  let e := GraphSpace.testFunctionToWkp0Linear
    (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
    (Ω := Ω)
  have hcomp :
      (traceLpOnW1p0 (m := m) (Ω := Ω) p :
        W₀^{1,(ENNReal.ofReal p)}(Ω) →
          MeasureTheory.Lp ℝ (ENNReal.ofReal p)
            (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)) ∘ e =
        (0 : W₀^{1,(ENNReal.ofReal p)}(Ω) →L[ℝ]
          MeasureTheory.Lp ℝ (ENNReal.ofReal p)
            (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)) ∘ e := by
    funext φ
    change traceLp (m := m) (Ω := Ω) p
        (GraphSpace.testFunctionToWkp
          (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
          (Ω := Ω) φ) = 0
    exact traceLp_testFunctionOn_eq_zero
      (m := m) (Ω := Ω) p φ
  have hfun :=
    (GraphSpace.denseRange_testFunctionToWkp0Linear
      (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
      (Ω := Ω)).equalizer
      (traceLpOnW1p0 (m := m) (Ω := Ω) p).continuous
      (0 : W₀^{1,(ENNReal.ofReal p)}(Ω) →L[ℝ]
        MeasureTheory.Lp ℝ (ENNReal.ofReal p)
          (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)).continuous
      hcomp
  apply ContinuousLinearMap.ext
  intro u
  exact congrFun hfun u

/-- The ambient finite-exponent trace vanishes on every element of
`W^{1,p}_0(Ω)`. -/
theorem traceLp_coe_W1p0_eq_zero
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (u : W₀^{1,(ENNReal.ofReal p)}(Ω)) :
    traceLp (m := m) (Ω := Ω) p
        (u : W^{1,ENNReal.ofReal p}(Ω)) = 0 := by
  have h := congrArg (fun T ↦ T u)
    (traceLpOnW1p0_eq_zero (m := m) (Ω := Ω) p)
  simpa [traceLpOnW1p0] using h

/-- Quantitative global finite-exponent trace estimate. -/
theorem norm_traceLp_le
    {m : ℕ} {Ω : Set (ℝ^(m + 1))}
    [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    ‖traceLp (m := m) (Ω := Ω) p u‖ ≤
      (∑ i : Fin hΩ.N,
        (chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
            (1 / ENNReal.ofReal p).toReal *
          p ^ (1 / p) *
          ‖Extension.C1.BoundaryPiece.flattenCLM
            (n := m + 1) (p := ENNReal.ofReal p)
            (Ω := Ω) i‖) * ‖u‖ := by
  calc
    ‖traceLp (m := m) (Ω := Ω) p u‖ =
        ‖∑ i : Fin hΩ.N,
          localPhysicalTraceLp (m := m) (Ω := Ω) p i u‖ := by
      simp [traceLp]
    _ ≤ ∑ i : Fin hΩ.N,
        ‖localPhysicalTraceLp (m := m) (Ω := Ω) p i u‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin hΩ.N,
        ((chartSurfaceBound (m := m) (Ω := Ω) i : ℝ) ^
            (1 / ENNReal.ofReal p).toReal *
          p ^ (1 / p) *
          ‖Extension.C1.BoundaryPiece.flattenCLM
            (n := m + 1) (p := ENNReal.ofReal p)
            (Ω := Ω) i‖ * ‖u‖) := by
      exact Finset.sum_le_sum fun i _ ↦
        norm_localPhysicalTraceLp_le
          (m := m) (Ω := Ω) p i u
    _ = _ := by rw [Finset.sum_mul]

/-! ## Compatibility with the Hilbert trace -/

section ExponentTwo

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}

/-- Canonical identification of the real-exponent domain `W^{1,2}` space
with the Hilbert-space alias `H¹`. -/
noncomputable def domainW1pTwoEquivH1 :
    W^{1,ENNReal.ofReal (2 : ℝ)}(Ω) ≃L[ℝ]
      H¹(Ω) :=
  GraphSpace.WkpSpaceOn.congrExponent (ENNReal.ofReal_ofNat 2) _ _ _

/-- The exponent-two identification preserves every Sobolev coordinate representative. -/
theorem domainW1pTwoEquivH1_coordinate
    (u : W^{1,ENNReal.ofReal (2 : ℝ)}(Ω))
    (a : GraphSpace.DerivIndex (m + 1) 1) :
    (GraphSpace.wkpCoordinateCLM a (domainW1pTwoEquivH1 u) : ℝ^(m + 1) → ℝ) =
      (GraphSpace.wkpCoordinateCLM a u : ℝ^(m + 1) → ℝ) :=
  GraphSpace.WkpSpaceOn.coordinate_congrExponent (ENNReal.ofReal_ofNat 2) u a

/-- The exponent-two identification carries `W¹,²₀` exactly onto `H¹₀`. -/
theorem domainW1pTwoEquivH1_mem_H10_iff
    (u : W^{1,ENNReal.ofReal (2 : ℝ)}(Ω)) :
    domainW1pTwoEquivH1 u ∈
        (GraphSpace.h10SubmoduleOn (n := m + 1) (Ω := Ω)).toSubmodule ↔
      u ∈ (GraphSpace.wkp0SubmoduleOn (n := m + 1) (k := 1)
        (p := ENNReal.ofReal (2 : ℝ)) (Ω := Ω)).toSubmodule := by
  have htransport {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (h : p = q)
      (v : W^{1,p}(Ω)) :
      GraphSpace.WkpSpaceOn.congrExponent h (m + 1) 1 Ω v ∈
          (GraphSpace.wkp0SubmoduleOn (n := m + 1) (k := 1) (p := q) (Ω := Ω)).toSubmodule ↔
        v ∈ (GraphSpace.wkp0SubmoduleOn (n := m + 1) (k := 1)
          (p := p) (Ω := Ω)).toSubmodule := by
    subst q
    rfl
  exact htransport (ENNReal.ofReal_ofNat 2) u

/-- Canonical identification of boundary `L^(ENNReal.ofReal 2)` with
boundary `L²`. -/
noncomputable def boundaryLpTwoEquivL2 :
    Lp ℝ (ENNReal.ofReal (2 : ℝ))
        (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) ≃L[ℝ]
      Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
  MeasureTheory.Lp.congrExponent (ENNReal.ofReal_ofNat 2) _

variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The canonical `W^{1,2} ≃ H¹` identification commutes with the ambient
smooth test-function embeddings. -/
theorem domainW1pTwoEquivH1_globalTestFunction
    (φ : Trace.HalfSpace.GlobalTestFunction m) :
    domainW1pTwoEquivH1 (m := m) (Ω := Ω)
        (globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal (2 : ℝ)) φ) =
      globalTestFunctionToDomainW1pLinear
        (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ := by
  apply eq_of_heq
  rw [globalTestFunctionToDomainW1pLinear_eq_mk,
    globalTestFunctionToDomainW1pLinear_eq_mk]
  exact (GraphSpace.WkpSpaceOn.congrExponent_apply_heq
    (ENNReal.ofReal_ofNat 2) _ _ _
    (GraphSpace.mkWkpSpaceOnOfContDiff
      (n := m + 1) (k := 1) (p := ENNReal.ofReal (2 : ℝ))
      (Ω := Ω) φ.1.toFun φ.1.contDiff
      φ.1.hasCompactSupport)).trans
    (GraphSpace.mkWkpSpaceOnOfContDiff_congrExponent
      (ENNReal.ofReal_ofNat 2) φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport)

/-- The canonical boundary exponent identification commutes with literal
restriction of ambient smooth functions. -/
theorem boundaryLpTwoEquivL2_globalTestFunction
    (φ : Trace.HalfSpace.GlobalTestFunction m) :
    boundaryLpTwoEquivL2 (m := m) (Ω := Ω)
        (globalTestFunctionBoundaryLpLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal (2 : ℝ)) φ) =
      globalTestFunctionBoundaryLpLinear
        (m := m) (Ω := Ω) (2 : ℝ≥0∞) φ := by
  apply eq_of_heq
  exact (MeasureTheory.Lp.congrExponent_apply_heq
    (ENNReal.ofReal_ofNat 2)
    (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)
    (globalTestFunctionBoundaryLpLinear
      (m := m) (Ω := Ω) (ENNReal.ofReal (2 : ℝ)) φ)).trans (by
      unfold globalTestFunctionBoundaryLpLinear
      let hp : MemLp φ.1.toFun (ENNReal.ofReal (2 : ℝ))
          (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
        φ.1.contDiff.continuous.memLp_of_hasCompactSupport
          φ.1.hasCompactSupport
      let hq : MemLp φ.1.toFun 2
          (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
        φ.1.contDiff.continuous.memLp_of_hasCompactSupport
          φ.1.hasCompactSupport
      change HEq (hp.toLp φ.1.toFun) (hq.toLp φ.1.toFun)
      exact MeasureTheory.MemLp.toLp_heq_of_exponent_eq
        (ENNReal.ofReal_ofNat 2) hp hq)

/-- Commuting-diagram form of compatibility between the finite `p = 2` trace
and the Hilbert trace. -/
theorem boundaryLpTwoEquivL2_traceLp
    (u : W^{1,ENNReal.ofReal (2 : ℝ)}(Ω)) :
    boundaryLpTwoEquivL2 (m := m) (Ω := Ω)
        (traceLp (m := m) (Ω := Ω) 2 u) =
      trace (m := m) (Ω := Ω)
        (domainW1pTwoEquivH1 (m := m) (Ω := Ω) u) := by
  let lhs :
      W^{1,ENNReal.ofReal (2 : ℝ)}(Ω) →L[ℝ]
        Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
    (boundaryLpTwoEquivL2 (m := m) (Ω := Ω)).toContinuousLinearMap.comp
      (traceLp (m := m) (Ω := Ω) 2)
  let rhs :
      W^{1,ENNReal.ofReal (2 : ℝ)}(Ω) →L[ℝ]
        Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
    (trace (m := m) (Ω := Ω)).comp
      (domainW1pTwoEquivH1 (m := m) (Ω := Ω)).toContinuousLinearMap
  have hcomp :
      (lhs : _ → _) ∘ globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal (2 : ℝ)) =
        (rhs : _ → _) ∘ globalTestFunctionToDomainW1pLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal (2 : ℝ)) := by
    funext φ
    simp only [lhs, rhs, ContinuousLinearMap.comp_apply, Function.comp_apply]
    rw [traceLp_classical]
    change boundaryLpTwoEquivL2 (m := m) (Ω := Ω)
        (globalTestFunctionBoundaryLpLinear
          (m := m) (Ω := Ω) (ENNReal.ofReal (2 : ℝ)) φ) =
      trace (m := m) (Ω := Ω)
        (domainW1pTwoEquivH1 (m := m) (Ω := Ω)
          (globalTestFunctionToDomainW1pLinear
            (m := m) (Ω := Ω) (ENNReal.ofReal (2 : ℝ)) φ))
    rw [boundaryLpTwoEquivL2_globalTestFunction,
      domainW1pTwoEquivH1_globalTestFunction, trace_classical]
  have hfun :=
    (denseRange_globalTestFunctionToDomainW1pLinear
      (m := m) (Ω := Ω) (ENNReal.ofReal (2 : ℝ)) (by norm_num)).equalizer
      lhs.continuous rhs.continuous hcomp
  exact congrFun hfun u

end ExponentTwo

end Trace.C1
end SobolevSpace
