/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.C1.Assembly.Flattening.Assembly
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.ChangeOfVariables
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.PullbackBounds
import PDE.Spaces.Sobolev.Extension.C1.Assembly.BoundaryPiece.ClassicalRepresentative
import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Uniqueness
import PDE.Spaces.Sobolev.Inequalities.Hardy.HalfSpace
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent

/-!
# Hardy inequality for a flattened boundary partition piece

For a compactly supported smooth function on a `C¹` domain, we multiply by one boundary partition
function and transport the result through its flattening chart. The transported function is
supported strictly inside the upper half-space, so the half-space Hardy inequality of
`Hardy.HalfSpace` applies. To return to the domain we use that the chart height is comparable to
the distance to `∂Ω` on the support of the partition function
(`Trace.C1.chart_height_le_mul_infDist_frontier_on_boundarySupport`) and that the inverse
Jacobian of the chart is bounded. Localizing the distance-to-boundary Hardy inequality to boundary
charts and applying the one-dimensional inequality along the lines of the last chart coordinate is
the argument of Nečas.

## Main results

* `flattenedBoundaryPiece`: the `i`-th boundary partition piece `χ_i φ` transported to the
  half-space through `(chart i).symm`, with a target cutoff that makes it compactly supported.
* `hardy_flattenedBoundaryPiece`: the half-space `Lᵖ` Hardy inequality for that piece.
* `eLpNorm_flattenedHeightQuotient_le_normalCoordinate`: the quotient by the normal height is
  controlled in `Lᵖ` by the normal weak-derivative coordinate, with constant `p/(p-1)`.
* `exists_eLpNorm_boundaryDistanceQuotient_le_flattenedHeightQuotient`: on the chart source, the
  physical quotient by `dist(·, ∂Ω)` is controlled by the flattened quotient by height, with a
  constant coming from the height comparison and the Jacobian bound of the chart.
* `exists_eLpNorm_boundaryDistanceQuotient_le_graphNorm`: each boundary piece divided by
  boundary distance is bounded in `Lᵖ` by the `W^{1,p}` graph norm of `φ`, for `p > 1`.

The constants are existential and the right-hand sides are full graph norms.

## References

* J. Nečas, "Sur une méthode pour résoudre les équations aux dérivées partielles du type elliptique,
  voisine de la variationnelle", *Ann. Scuola Norm. Sup. Pisa Cl. Sci. (3)* 16 (1962), no. 4,
  305-326, §1, Théorèmes 1.4-1.6 and their proofs.
  <https://www.numdam.org/item/ASNSP_1962_3_16_4_305_0/>
* G. H. Hardy, J. E. Littlewood and G. Pólya, *Inequalities*, 2nd ed., Cambridge Mathematical
  Library, Cambridge University Press, 1988, Chapter IX, for the one-dimensional inequality.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.Hardy

open MeasureTheory Set
open Boundary.C1ExtensionAtlas.DerivedCutoffs
open scoped ENNReal Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/--
The `i`-th boundary partition piece in flattened coordinates. The auxiliary
target cutoff makes the total function compactly supported without changing
it on the transported partition support.
-/
noncomputable def flattenedBoundaryPiece
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) : ℝ^n → ℝ :=
  fun y ↦
    (targetSupportCutoff (n := n) (Ω := Ω) i).toFun y *
      (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) *
      φ.1.toFun ((hΩ.chart i).symm y)

/-- A `C¹` chart transports a smooth domain test function to a `C¹` function. -/
theorem flattenedBoundaryPiece_contDiff
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    ContDiff ℝ 1 (flattenedBoundaryPiece (n := n) (Ω := Ω) i φ) :=
  (((targetSupportCutoff i).contDiff.of_le (by simp)).mul
    (((hΩ.boundaryCutoff i).contDiff.of_le (by simp)).comp (hΩ.chart_symm_contDiff i))).mul
    ((φ.1.contDiff.of_le (by simp)).comp (hΩ.chart_symm_contDiff i))

/-- The target cutoff gives every flattened boundary piece compact support. -/
theorem flattenedBoundaryPiece_hasCompactSupport
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    HasCompactSupport (flattenedBoundaryPiece (n := n) (Ω := Ω) i φ) :=
  (targetSupportCutoff (n := n) (Ω := Ω) i).hasCompactSupport.mul_right.mul_right

private noncomputable def flattenedBoundarySupport
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) : Set (ℝ^n) :=
  hΩ.chart i ''
    (boundarySupport (n := n) (Ω := Ω) i ∩ tsupport φ.1.toFun)

private theorem isCompact_flattenedBoundarySupport
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    IsCompact (flattenedBoundarySupport (n := n) (Ω := Ω) i φ) :=
  ((isCompact_boundarySupport i).inter φ.1.hasCompactSupport).image_of_continuousOn <|
    (hΩ.chart i).continuousOn.mono fun _ hx ↦ boundarySupport_subset_source i hx.1

private theorem support_flattenedBoundaryPiece_subset
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    Function.support (flattenedBoundaryPiece (n := n) (Ω := Ω) i φ) ⊆
      flattenedBoundarySupport (n := n) (Ω := Ω) i φ := by
  intro y hy
  simp only [Function.mem_support, flattenedBoundaryPiece, mul_ne_zero_iff] at hy
  obtain ⟨⟨hη, hψ⟩, hφ⟩ := hy
  exact ⟨(hΩ.chart i).symm y, ⟨subset_tsupport _ hψ, subset_tsupport _ hφ⟩, (hΩ.chart i).right_inv
    (tsupport_targetSupportCutoff_subset_target i (subset_tsupport _ hη))⟩

private theorem flattenedBoundaryPiece_tsupport_subset_supportSet
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    tsupport (flattenedBoundaryPiece (n := n) (Ω := Ω) i φ) ⊆
      flattenedBoundarySupport (n := n) (Ω := Ω) i φ :=
  closure_minimal (support_flattenedBoundaryPiece_subset i φ)
    (isCompact_flattenedBoundarySupport i φ).isClosed

/--
The flattened boundary piece is supported in the target of the chart
restricted to the physical domain.
-/
theorem flattenedBoundaryPiece_tsupport_subset_chartOnΩ_target
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    tsupport (flattenedBoundaryPiece (n := n) (Ω := Ω) i φ) ⊆
      (Boundary.C1ExtensionAtlas.Charts.chartOnΩ
        (n := n) (Ω := Ω) i).target := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := flattenedBoundaryPiece_tsupport_subset_supportSet i φ hy
  rw [Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper]
  have hxSource := boundarySupport_subset_source (n := n) (Ω := Ω) i hx.1
  exact ⟨(hΩ.chart i).map_source hxSource, (hΩ.chart_mem_iff_upper i x hxSource).1 (φ.2 hx.2)⟩

/-- The flattened boundary piece is supported inside the upper half-space. -/
theorem flattenedBoundaryPiece_tsupport_subset_upper
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    tsupport (flattenedBoundaryPiece (n := n) (Ω := Ω) i φ) ⊆
      HalfSpace.upper n :=
  (flattenedBoundaryPiece_tsupport_subset_chartOnΩ_target i φ).trans
    (Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper i)

/--
On the physical domain, evaluating the flattened piece at the chart image
recovers the boundary partition function times the original test function.
-/
theorem flattenedBoundaryPiece_chart_apply
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) {x : ℝ^n}
    (hx : x ∈ (hΩ.chart i).source ∩ Ω) :
    flattenedBoundaryPiece (n := n) (Ω := Ω) i φ (hΩ.chart i x) =
      (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x := by
  by_cases hψ : (hΩ.boundaryCutoff i).toFun x = 0
  · simp [flattenedBoundaryPiece, (hΩ.chart i).left_inv hx.1, hψ]
  · simp [flattenedBoundaryPiece, (hΩ.chart i).left_inv hx.1,
      targetSupportCutoff_eq_one_on_boundarySupportInTarget i (hΩ.chart i x)
        ⟨x, subset_tsupport _ hψ, rfl⟩]

/--
The normal first-derivative coordinate stored by the Sobolev flattening
operator for a smooth boundary partition piece.
-/
noncomputable def flattenedNormalCoordinate
    {p : ENNReal} [Fact (1 ≤ p)]
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    GraphSpace.DerivLp n p (HalfSpace.upper n) :=
  (((Extension.C1.BoundaryPiece.flattenCLM
      (n := n) (p := p) (Ω := Ω) i
      (GraphSpace.testFunctionToWkp
        (n := n) (k := 1) (p := p) (Ω := Ω) φ) :
      W^{1,p}(HalfSpace.upper n)) :
    GraphSpace.WkpAmbientOn n 1 p (HalfSpace.upper n))
    (GraphSpace.singleDerivIndex n (PDE.Common.lastIndex (n := n))) :
      GraphSpace.DerivLp n p (HalfSpace.upper n))

/--
The stored normal Sobolev coordinate of a flattened smooth partition piece
agrees almost everywhere with its classical normal derivative.
-/
theorem flattenedNormalCoordinate_eq_partialDeriv_ae
    {p : ENNReal} [Fact (1 ≤ p)]
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    ((flattenedNormalCoordinate (n := n) (Ω := Ω) (p := p) i φ :
      GraphSpace.DerivLp n p (HalfSpace.upper n)) : ℝ^n → ℝ) =ᵐ[
        domainMeasure n (HalfSpace.upper n)]
      fun y ↦
        (∂[PDE.Common.lastIndex (n := n)]
          (flattenedBoundaryPiece (n := n) (Ω := Ω) i φ)) y := by
  let U := GraphSpace.testFunctionToWkp (n := n) (k := 1) (p := p) (Ω := Ω) φ
  let F := Extension.C1.BoundaryPiece.flattenCLM (n := n) (p := p) (Ω := Ω) i U
  let q := flattenedBoundaryPiece i φ
  let base : ℝ^n → ℝ :=
    (F : GraphSpace.WkpAmbientOn n 1 p (HalfSpace.upper n)) (GraphSpace.baseIndex n 1)
  let d : ℝ^n → ℝ := ((F : GraphSpace.WkpAmbientOn n 1 p (HalfSpace.upper n))
    (GraphSpace.singleDerivIndex n (PDE.Common.lastIndex (n := n))) :
      GraphSpace.DerivLp n p (HalfSpace.upper n))
  have hU : ((((U : GraphSpace.WkpAmbientOn n 1 p Ω) (GraphSpace.baseIndex n 1) :
      GraphSpace.DerivLp n p Ω) : ℝ^n → ℝ)) =ᵐ[domainMeasure n Ω] φ.1.toFun := by
    simpa [U, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      GraphSpace.testFunctionToWkp_coordinate_ae (n := n) (k := 1) (p := p) (Ω := Ω) φ
        (GraphSpace.baseIndex n 1)
  have hbase : base =ᵐ[domainMeasure n (HalfSpace.upper n)] q := by
    filter_upwards [Extension.C1.BoundaryPiece.flattenCLM_base_eq_classical_ae
      (n := n) (p := p) (Ω := Ω) i U φ.1.toFun hU] with y hy
    rw [show base y = ((targetSupportCutoff (n := n) (Ω := Ω) i).toFun y *
        (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y)) * φ.1.toFun ((hΩ.chart i).symm y) by
      simpa [base, F, GraphSpace.baseRepresentative] using hy]
    simp only [q, flattenedBoundaryPiece]
  have hweakF : HasWeakDerivativeOn (n := n) (HalfSpace.upper n)
      [PDE.Common.lastIndex (n := n)] base d := by
    simpa [base, d, GraphSpace.singleDerivIndex_toList] using
      F.property (GraphSpace.singleDerivIndex n (PDE.Common.lastIndex (n := n)))
  have hweakQd := (hasWeakDerivativeOn_congr_ae (n := n) (Ω := HalfSpace.upper n)
    (α := [PDE.Common.lastIndex (n := n)]) hbase (Filter.EventuallyEq.refl _ _)).mp hweakF
  simpa [flattenedNormalCoordinate, d, q, F, U] using
    hweakQd.unique_ae (HalfSpace.isOpen_upper (n := n))
      (WeakChangeOfVariables.hasWeakDerivativeOn_of_contDiff_one (Ω := HalfSpace.upper n)
        (i := PDE.Common.lastIndex (n := n)) (flattenedBoundaryPiece_contDiff i φ))

/--
The normal Sobolev coordinate of a flattened boundary piece is controlled by
the flattening operator norm and the original `W^{1,p}` graph norm.
-/
theorem norm_flattenedNormalCoordinate_le
    {p : ENNReal} [Fact (1 ≤ p)]
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    ‖flattenedNormalCoordinate (n := n) (Ω := Ω) (p := p) i φ‖ ≤
      ‖Extension.C1.BoundaryPiece.flattenCLM
        (n := n) (p := p) (Ω := Ω) i‖ *
        ‖GraphSpace.testFunctionToWkp
          (n := n) (k := 1) (p := p) (Ω := Ω) φ‖ := by
  let F := Extension.C1.BoundaryPiece.flattenCLM (n := n) (p := p) (Ω := Ω) i
    (GraphSpace.testFunctionToWkp (n := n) (k := 1) (p := p) (Ω := Ω) φ)
  refine le_trans ?_
    ((Extension.C1.BoundaryPiece.flattenCLM (n := n) (p := p) (Ω := Ω) i).le_opNorm _)
  simpa [flattenedNormalCoordinate, F] using PiLp.norm_apply_le
    (x := (F : GraphSpace.WkpAmbientOn n 1 p (HalfSpace.upper n)))
    (i := GraphSpace.singleDerivIndex n (PDE.Common.lastIndex (n := n)))

/-- The physical boundary-partition piece divided by boundary distance. -/
noncomputable def boundaryDistanceQuotient
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) : ℝ^n → ℝ :=
  fun x ↦
    (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x /
      Metric.infDist x (frontier Ω)

/-- The flattened boundary-partition piece divided by normal height. -/
noncomputable def flattenedHeightQuotient
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) : ℝ^n → ℝ :=
  fun y ↦
    flattenedBoundaryPiece (n := n) (Ω := Ω) i φ y /
      y (PDE.Common.lastIndex (n := n))

/--
On a boundary chart, the physical quotient by boundary distance is controlled
pointwise by the flattened quotient by height.
-/
theorem exists_norm_boundaryDistanceQuotient_le_flattenedHeightQuotient
    (i : Fin hΩ.N) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : GraphSpace.TestFunctionOn n Ω,
        ∀ x ∈
            (Boundary.C1ExtensionAtlas.Charts.chartOnΩ
              (n := n) (Ω := Ω) i).source,
          |boundaryDistanceQuotient (n := n) (Ω := Ω) i φ x| ≤
            C *
              |flattenedHeightQuotient (n := n) (Ω := Ω) i φ
                (hΩ.chart i x)| := by
  obtain ⟨C, hC, hheight⟩ :=
    Trace.C1.chart_height_le_mul_infDist_frontier_on_boundarySupport (n := n) (Ω := Ω) i
  refine ⟨C, hC, fun φ x hxSource ↦ ?_⟩
  change |(hΩ.boundaryCutoff i).toFun x * φ.1.toFun x / Metric.infDist x (frontier Ω)| ≤ _
  set a := (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x with ha_def
  by_cases ha : a = 0
  · rw [ha, zero_div, abs_zero]
    exact mul_nonneg hC (abs_nonneg _)
  obtain ⟨hψne, hφne⟩ := mul_ne_zero_iff.1 ha
  have hxΩ : x ∈ Ω := φ.2 (subset_tsupport _ hφne)
  have hxChartSource : x ∈ (hΩ.chart i).source := by
    rw [Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] at hxSource
    exact hxSource.1
  have hheightPos : 0 < (hΩ.chart i x) (PDE.Common.lastIndex (n := n)) :=
    (hΩ.chart_mem_iff_upper i x hxChartSource).1 hxΩ
  have hdistPos := SobolevSpace.Trace.C1.infDist_frontier_pos_of_mem (n := n) (Ω := Ω) hxΩ
  rw [flattenedHeightQuotient, (flattenedBoundaryPiece_chart_apply i φ
    ⟨hxChartSource, hxΩ⟩).trans ha_def.symm, abs_div, abs_div, abs_of_pos hdistPos,
    abs_of_pos hheightPos]
  calc |a| / Metric.infDist x (frontier Ω) = |a| * (1 / Metric.infDist x (frontier Ω)) := by
        ring
    _ ≤ |a| * (C / (hΩ.chart i x) (PDE.Common.lastIndex (n := n))) := by
      gcongr |a| * ?_
      rw [div_le_div_iff₀ hdistPos hheightPos, one_mul]
      exact hheight x ⟨subset_tsupport _ hψne, hxΩ⟩
    _ = C * (|a| / (hΩ.chart i x) (PDE.Common.lastIndex (n := n))) := by ring

/--
The physical boundary-distance quotient is controlled in `Lᵖ` by the
flattened height quotient. The finite constant combines the chart-height
comparison with the inverse-Jacobian bound for the restricted chart.
-/
theorem exists_eLpNorm_boundaryDistanceQuotient_le_flattenedHeightQuotient
    {p : ENNReal} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (i : Fin hΩ.N) :
    ∃ C : ENNReal, C ≠ ∞ ∧
      ∀ φ : GraphSpace.TestFunctionOn n Ω,
        eLpNorm (boundaryDistanceQuotient (n := n) (Ω := Ω) i φ) p
            (domainMeasure n
              (Boundary.C1ExtensionAtlas.Charts.chartOnΩ
                (n := n) (Ω := Ω) i).source) ≤
          C *
            eLpNorm (flattenedHeightQuotient (n := n) (Ω := Ω) i φ) p
              (domainMeasure n
                (Boundary.C1ExtensionAtlas.Charts.chartOnΩ
                  (n := n) (Ω := Ω) i).target) := by
  let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i
  obtain ⟨Cdist, hCdist, hpoint⟩ :=
    exists_norm_boundaryDistanceQuotient_le_flattenedHeightQuotient (n := n) (Ω := Ω) i
  have hEsymm : ContDiff ℝ 1 (fun x ↦ E.symm x) := by
    simpa [E, Boundary.C1ExtensionAtlas.Charts.chartOnΩ] using hΩ.chart_symm_contDiff i
  have hTarget : Bornology.IsBounded E.target :=
    (hΩ.chart_target_bounded i).subset fun y hy ↦ by
      rw [Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_eq_target_inter_upper
        (n := n) (Ω := Ω) (i := i)] at hy
      exact hy.1
  obtain ⟨Cchart, hCchart, hpull⟩ :=
    WeakChangeOfVariables.eLpNorm_comp_partialHomeomorph_le_of_bounded_target
      (n := n) (p := p) hp hEsymm hTarget
  refine ⟨ENNReal.ofReal Cdist * Cchart, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCchart,
    fun φ ↦ ?_⟩
  have hAE : ∀ᵐ x ∂domainMeasure n E.source, ‖boundaryDistanceQuotient i φ x‖ ≤
      Cdist * ‖flattenedHeightQuotient i φ (E x)‖ :=
    ae_restrict_of_forall_mem E.open_source.measurableSet fun x hx ↦ by
      rw [show E x = hΩ.chart i x from rfl]
      simpa [Real.norm_eq_abs] using hpoint φ x hx
  calc _ ≤ ENNReal.ofReal Cdist * eLpNorm (fun x ↦ flattenedHeightQuotient i φ (E x)) p
        (domainMeasure n E.source) :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul (((hΩ.boundaryCutoff i).continuous.measurable.mul
        φ.1.continuous.measurable).div
          (Metric.continuous_infDist_pt (frontier Ω)).measurable).aestronglyMeasurable hAE p
    _ ≤ ENNReal.ofReal Cdist *
        (Cchart * eLpNorm (flattenedHeightQuotient i φ) p (domainMeasure n E.target)) := by
      gcongr
      exact hpull _
    _ = _ := (mul_assoc _ _ _).symm

/--
The upper-half-space Hardy inequality for one flattened boundary
partition piece.
-/
theorem hardy_flattenedBoundaryPiece
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω)
    {p : ℝ} (hp : 1 < p) :
    (∫ y in HalfSpace.upper n,
        |flattenedBoundaryPiece (n := n) (Ω := Ω) i φ y| ^ p *
          Metric.infDist y (frontier (HalfSpace.upper n)) ^ (-p)) ≤
      (p / (p - 1)) ^ p *
        ∫ y in HalfSpace.upper n,
          |(∂[PDE.Common.lastIndex (n := n)]
              (flattenedBoundaryPiece (n := n) (Ω := Ω) i φ)) y| ^ p :=
  hardy_upperHalfSpace_infDist_lp_of_hasCompactSupport_of_posDim hp
    (flattenedBoundaryPiece_contDiff i φ) (flattenedBoundaryPiece_hasCompactSupport i φ)
    (flattenedBoundaryPiece_tsupport_subset_upper i φ)

/--
The upper-half-space Hardy bound for the flattened chart quotient,
expressed directly in the `L^p` seminorm.
-/
theorem eLpNorm_flattenedHeightQuotient_le_normalCoordinate
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) :
    eLpNorm (flattenedHeightQuotient (n := n) (Ω := Ω) i φ)
        (ENNReal.ofReal p) (domainMeasure n (HalfSpace.upper n)) ≤
      ENNReal.ofReal (p / (p - 1)) *
        ‖flattenedNormalCoordinate
          (n := n) (Ω := Ω) (p := ENNReal.ofReal p) i φ‖ₑ := by
  let q := flattenedHeightQuotient (n := n) (Ω := Ω) i φ
  let D := flattenedNormalCoordinate (n := n) (Ω := Ω) (p := ENNReal.ofReal p) i φ
  let d : ℝ^n → ℝ := D
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hconst : 0 < p / (p - 1) := by positivity
  have hq : MemLp q (ENNReal.ofReal p) (domainMeasure n (HalfSpace.upper n)) :=
    (memLp_div_last_of_hasCompactSupport (n := n) hp0
      (flattenedBoundaryPiece_contDiff i φ).continuous
      (flattenedBoundaryPiece_hasCompactSupport i φ)
      (flattenedBoundaryPiece_tsupport_subset_upper i φ)).mono_measure Measure.restrict_le_self
  have hd : MemLp d (ENNReal.ofReal p) (domainMeasure n (HalfSpace.upper n)) := Lp.memLp D
  have hqIntegral : (∫ y, |q y| ^ p ∂domainMeasure n (HalfSpace.upper n)) =
      ∫ y in HalfSpace.upper n, |flattenedBoundaryPiece i φ y| ^ p *
        y (PDE.Common.lastIndex (n := n)) ^ (-p) :=
    setIntegral_congr_fun (HalfSpace.measurableSet_upper (n := n))
      fun y (hy : 0 < y (PDE.Common.lastIndex (n := n))) ↦ by
        change |flattenedBoundaryPiece i φ y / y (PDE.Common.lastIndex (n := n))| ^ p = _
        rw [abs_div, abs_of_pos hy, Real.div_rpow (abs_nonneg _) hy.le, Real.rpow_neg hy.le]
        ring
  have hdIntegral : (∫ y, |d y| ^ p ∂domainMeasure n (HalfSpace.upper n)) =
      ∫ y in HalfSpace.upper n,
        |(∂[PDE.Common.lastIndex (n := n)] (flattenedBoundaryPiece i φ)) y| ^ p :=
    integral_congr_ae ((flattenedNormalCoordinate_eq_partialDeriv_ae
      (n := n) (Ω := Ω) (p := ENNReal.ofReal p) i φ).fun_comp fun z ↦ |z| ^ p)
  have hnorm : ‖hq.toLp q‖ ≤ p / (p - 1) * ‖hd.toLp d‖ := by
    refine (Real.rpow_le_rpow_iff (norm_nonneg _) (mul_nonneg hconst.le (norm_nonneg _))
      hp0).mp ?_
    rw [Real.mul_rpow hconst.le (norm_nonneg _), norm_toLp_rpow_eq_integral_abs hp0 hq,
      norm_toLp_rpow_eq_integral_abs hp0 hd, hqIntegral, hdIntegral]
    exact hardy_upperHalfSpace_lp_of_hasCompactSupport_of_posDim (n := n) hp
      (flattenedBoundaryPiece_contDiff i φ) (flattenedBoundaryPiece_hasCompactSupport i φ)
      (flattenedBoundaryPiece_tsupport_subset_upper i φ)
  have h := ENNReal.ofReal_le_ofReal hnorm
  rw [ENNReal.ofReal_mul hconst.le, ofReal_norm, ofReal_norm,
    show hd.toLp d = D from Lp.ext hd.coeFn_toLp] at h
  rw [← Lp.enorm_toLp hq]
  exact h

/--
Each boundary chart has a finite Hardy constant controlling the physical
boundary-distance quotient by the original `W^{1,p}` graph norm.
-/
theorem exists_eLpNorm_boundaryDistanceQuotient_le_graphNorm
    (i : Fin hΩ.N)
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) :
    ∃ C : ENNReal, C ≠ ∞ ∧
      ∀ φ : GraphSpace.TestFunctionOn n Ω,
        eLpNorm (boundaryDistanceQuotient (n := n) (Ω := Ω) i φ)
            (ENNReal.ofReal p)
            (domainMeasure n
              (Boundary.C1ExtensionAtlas.Charts.chartOnΩ
                (n := n) (Ω := Ω) i).source) ≤
          C *
            ‖GraphSpace.testFunctionToWkp
              (n := n) (k := 1) (p := ENNReal.ofReal p)
              (Ω := Ω) φ‖ₑ := by
  let E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i
  obtain ⟨Cchart, hCchart, hpull⟩ :=
    exists_eLpNorm_boundaryDistanceQuotient_le_flattenedHeightQuotient
      (n := n) (Ω := Ω) (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top i
  have htarget : domainMeasure n E.target ≤ domainMeasure n (HalfSpace.upper n) :=
    Measure.restrict_mono
      (Boundary.C1ExtensionAtlas.Charts.chartOnΩ_target_subset_upper (n := n) (Ω := Ω) i) le_rfl
  refine ⟨Cchart * ENNReal.ofReal (p / (p - 1)) * ‖Extension.C1.BoundaryPiece.flattenCLM
    (n := n) (p := ENNReal.ofReal p) (Ω := Ω) i‖ₑ, by finiteness, fun φ ↦ ?_⟩
  have hnormal : ‖flattenedNormalCoordinate (n := n) (Ω := Ω) (p := ENNReal.ofReal p) i φ‖ₑ ≤
      ‖Extension.C1.BoundaryPiece.flattenCLM (n := n) (p := ENNReal.ofReal p) (Ω := Ω) i‖ₑ *
        ‖GraphSpace.testFunctionToWkp (n := n) (k := 1) (p := ENNReal.ofReal p) (Ω := Ω) φ‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_flattenedNormalCoordinate_le i φ)
  calc _ ≤ Cchart * eLpNorm (flattenedHeightQuotient i φ) (ENNReal.ofReal p)
        (domainMeasure n E.target) := hpull φ
    _ ≤ Cchart * (ENNReal.ofReal (p / (p - 1)) *
        (‖Extension.C1.BoundaryPiece.flattenCLM (n := n) (p := ENNReal.ofReal p) (Ω := Ω) i‖ₑ *
          ‖GraphSpace.testFunctionToWkp (n := n) (k := 1) (p := ENNReal.ofReal p) (Ω := Ω)
            φ‖ₑ)) := by
      gcongr
      exact (eLpNorm_mono_measure _ htarget).trans
        ((eLpNorm_flattenedHeightQuotient_le_normalCoordinate i φ hp).trans (by gcongr))
    _ = _ := by ring

end SobolevSpace.Hardy
