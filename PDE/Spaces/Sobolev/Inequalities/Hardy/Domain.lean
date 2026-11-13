/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Geometry
import PDE.Spaces.Sobolev.Inequalities.Hardy.ChartLocal

/-!
# The Hardy inequality on a bounded smooth domain

The interior cutoff has compact support strictly inside the domain. Boundary
distance therefore has a positive minimum on that support. Dividing the
interior partition piece by boundary distance is consequently a bounded
zeroth-order operation, uniformly over the smooth test-function core.

The boundary pieces are controlled after flattening by the upper-half-space
Hardy inequality. The final theorem assembles the interior and boundary
estimates through the atlas partition of unity.

## Main results

* `interiorDistanceQuotient`, `exists_eLpNorm_interiorDistanceQuotient_le_graphNorm`: the
  interior piece `χ₀ φ / dist(·, ∂Ω)` is bounded in `Lᵖ(Ω)` by the graph norm for every
  `p ≥ 1`, because `dist(·, ∂Ω)` has a positive lower bound on the compact support of `χ₀`.
* `domainDistanceQuotient`, `exists_eLpNorm_domainDistanceQuotient_le_graphNorm`: for `p > 1`
  there is a finite `C` with `‖φ / dist(·, ∂Ω)‖_{Lᵖ(Ω)} ≤ C ‖φ‖_{W^{1,p}(Ω)}` for every smooth
  test function `φ` compactly supported in `Ω`.

The estimate is on the smooth core and against the full `W^{1,p}` graph norm, with an
existential constant. `Hardy.DomainCompletion` extends it to `W^{1,p}_0(Ω)` by density and
replaces the graph norm by the weak gradient.

## References

Nečas proves distance-to-boundary Hardy inequalities on Lipschitz domains by localizing to
boundary charts. Brezis and Marcus discuss the `L²` case and its best constant, which is at most
`1/4` when the boundary has a tangent plane at some point and equals `1/4` on convex domains.

* J. Nečas, "Sur une méthode pour résoudre les équations aux dérivées partielles du type elliptique,
  voisine de la variationnelle", *Ann. Scuola Norm. Sup. Pisa Cl. Sci. (3)* 16 (1962), no. 4,
  305-326, §1, Théorèmes 1.4-1.6.
  <https://www.numdam.org/item/ASNSP_1962_3_16_4_305_0/>
* H. Brezis and M. Marcus, "Hardy's inequalities revisited",
  *Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4)* 25 (1997), no. 1-2, 217-237, Introduction, (0.5)-(0.6).
  <https://www.numdam.org/item/ASNSP_1997_4_25_1-2_217_0/>
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace.Hardy

open MeasureTheory Set
open scoped ENNReal Topology

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- The interior partition piece divided by physical boundary distance. -/
noncomputable def interiorDistanceQuotient
    (φ : GraphSpace.TestFunctionOn n Ω) : ℝ^n → ℝ :=
  fun x ↦
    hΩ.interiorCutoff.toFun x * φ.1.toFun x /
      Metric.infDist x (frontier Ω)

private theorem interiorDistanceQuotient_aestronglyMeasurable
    (φ : GraphSpace.TestFunctionOn n Ω) :
    AEStronglyMeasurable
      (interiorDistanceQuotient (n := n) (Ω := Ω) φ)
      (domainMeasure n Ω) :=
  ((hΩ.interiorCutoff.continuous.mul φ.1.continuous).continuousOn.div
    (Metric.continuous_infDist_pt (frontier Ω)).continuousOn fun _ hx ↦
      (Trace.C1.infDist_frontier_pos_of_mem (n := n) (Ω := Ω) hx).ne').aestronglyMeasurable
    hΩ.isOpen.measurableSet

/--
The interior partition piece divided by boundary distance is uniformly
controlled by the `W^{1,p}` graph norm.
-/
theorem exists_eLpNorm_interiorDistanceQuotient_le_graphNorm
    {p : ENNReal} [Fact (1 ≤ p)] :
    ∃ C : ENNReal, C ≠ ∞ ∧
      ∀ φ : GraphSpace.TestFunctionOn n Ω,
        eLpNorm (interiorDistanceQuotient (n := n) (Ω := Ω) φ) p
            (domainMeasure n Ω) ≤
          C *
            ‖GraphSpace.testFunctionToWkp
              (n := n) (k := 1) (p := p) (Ω := Ω) φ‖ₑ := by
  open Boundary.C1ExtensionAtlas.DerivedCutoffs in
  obtain ⟨δ, hδpos, hδ⟩ := (isCompact_interiorSupport (n := n) (Ω := Ω)).exists_forall_le'
    (Metric.continuous_infDist_pt (frontier Ω)).continuousOn fun _ hx ↦
      Trace.C1.infDist_frontier_pos_of_mem (n := n) (Ω := Ω)
        (interiorSupport_subset_domain (n := n) (Ω := Ω) hx)
  obtain ⟨M, hM⟩ :=
    hΩ.interiorCutoff.hasCompactSupport.exists_bound_of_continuous hΩ.interiorCutoff.continuous
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨ENNReal.ofReal (M / δ), ENNReal.ofReal_ne_top, fun φ ↦ ?_⟩
  set U := GraphSpace.testFunctionToWkp (n := n) (k := 1) (p := p) (Ω := Ω) φ
  have hbase : ((U : GraphSpace.WkpAmbientOn n 1 p Ω) (GraphSpace.baseIndex n 1) :
      ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] φ.1.toFun := by
    simpa [U, GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
      GraphSpace.testFunctionToWkp_coordinate_ae (n := n) (k := 1) (p := p) (Ω := Ω) φ
        (GraphSpace.baseIndex n 1)
  have hpoint (x : ℝ^n) (hxΩ : x ∈ Ω) :
      ‖interiorDistanceQuotient (n := n) (Ω := Ω) φ x‖ ≤ M / δ * ‖φ.1.toFun x‖ := by
    by_cases hxK : x ∈ Boundary.C1ExtensionAtlas.DerivedCutoffs.interiorSupport (n := n) (Ω := Ω)
    · have hd := Trace.C1.infDist_frontier_pos_of_mem (n := n) (Ω := Ω) hxΩ
      rw [interiorDistanceQuotient, norm_div, norm_mul, Real.norm_of_nonneg hd.le,
        mul_div_right_comm]
      gcongr
      exacts [hM x, hδ x hxK]
    · rw [interiorDistanceQuotient, image_eq_zero_of_notMem_tsupport hxK, zero_mul, zero_div,
        norm_zero]
      positivity
  calc eLpNorm (interiorDistanceQuotient (n := n) (Ω := Ω) φ) p (domainMeasure n Ω)
      ≤ ENNReal.ofReal (M / δ) * eLpNorm φ.1.toFun p (domainMeasure n Ω) :=
        eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (interiorDistanceQuotient_aestronglyMeasurable (n := n) (Ω := Ω) φ)
          (ae_restrict_of_forall_mem hΩ.isOpen.measurableSet hpoint) p
    _ = ENNReal.ofReal (M / δ) *
        ‖(U : GraphSpace.WkpAmbientOn n 1 p Ω) (GraphSpace.baseIndex n 1)‖ₑ := by
      rw [Lp.enorm_def, eLpNorm_congr_ae hbase]
    _ ≤ ENNReal.ofReal (M / δ) * ‖U‖ₑ := by
      gcongr
      exact PiLp.enorm_apply_le _ _

/-- A smooth test function divided by physical boundary distance. -/
noncomputable def domainDistanceQuotient
    (φ : GraphSpace.TestFunctionOn n Ω) : ℝ^n → ℝ :=
  fun x ↦ φ.1.toFun x / Metric.infDist x (frontier Ω)

private theorem boundaryDistanceQuotient_support_subset_chartSource
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    Function.support
        (boundaryDistanceQuotient (n := n) (Ω := Ω) i φ) ⊆
      (Boundary.C1ExtensionAtlas.Charts.chartOnΩ
        (n := n) (Ω := Ω) i).source := by
  intro x hx
  have hnum : (hΩ.boundaryCutoff i).toFun x * φ.1.toFun x ≠ 0 := fun h ↦
    hx (by rw [boundaryDistanceQuotient, h, zero_div])
  rw [Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source]
  exact ⟨hΩ.boundaryCutoff_support i (subset_tsupport _ (left_ne_zero_of_mul hnum)),
    φ.2 (subset_tsupport _ (right_ne_zero_of_mul hnum))⟩

private theorem domainDistanceQuotient_ae_partition
    (φ : GraphSpace.TestFunctionOn n Ω) :
    domainDistanceQuotient (n := n) (Ω := Ω) φ =ᵐ[
        domainMeasure n Ω]
      fun x ↦
        interiorDistanceQuotient (n := n) (Ω := Ω) φ x +
          ∑ i,
            boundaryDistanceQuotient (n := n) (Ω := Ω) i φ x := by
  refine ae_restrict_of_forall_mem hΩ.isOpen.measurableSet ?_
  intro x hxΩ
  simp only [domainDistanceQuotient, interiorDistanceQuotient,
    boundaryDistanceQuotient]
  rw [← Finset.sum_div, ← add_div]
  congr 1
  rw [← Finset.sum_mul, ← add_mul, hΩ.cutoff_sum_eq_one x hxΩ]
  simp

private theorem boundaryDistanceQuotient_aestronglyMeasurable
    (i : Fin hΩ.N) (φ : GraphSpace.TestFunctionOn n Ω) :
    AEStronglyMeasurable
      (boundaryDistanceQuotient (n := n) (Ω := Ω) i φ)
      (domainMeasure n Ω) :=
  (((hΩ.boundaryCutoff i).continuous.mul φ.1.continuous).continuousOn.div
    (Metric.continuous_infDist_pt (frontier Ω)).continuousOn fun _ hx ↦
      (Trace.C1.infDist_frontier_pos_of_mem (n := n) (Ω := Ω) hx).ne').aestronglyMeasurable
    hΩ.isOpen.measurableSet

/--
The boundary-distance quotient of a smooth compactly supported test function
is controlled in `L^p(Ω)` by its `W^{1,p}(Ω)` graph norm.

The proof uses the atlas partition of unity. The interior piece is bounded
because its support stays a positive distance from the boundary. Each boundary
piece is flattened to the upper half-space, where the classical one-dimensional
Hardy estimate controls the normal direction.
-/
theorem exists_eLpNorm_domainDistanceQuotient_le_graphNorm
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 < p) :
    ∃ C : ENNReal, C ≠ ∞ ∧
      ∀ φ : GraphSpace.TestFunctionOn n Ω,
        eLpNorm (domainDistanceQuotient (n := n) (Ω := Ω) φ)
            (ENNReal.ofReal p) (domainMeasure n Ω) ≤
          C *
            ‖GraphSpace.testFunctionToWkp
              (n := n) (k := 1) (p := ENNReal.ofReal p)
              (Ω := Ω) φ‖ₑ := by
  obtain ⟨C₀, hC₀, hinterior⟩ :=
    exists_eLpNorm_interiorDistanceQuotient_le_graphNorm (n := n) (Ω := Ω) (p := ENNReal.ofReal p)
  choose C hC hbound using fun i ↦
    exists_eLpNorm_boundaryDistanceQuotient_le_graphNorm (n := n) (Ω := Ω) i hp
  refine ⟨C₀ + ∑ i, C i,
    ENNReal.add_ne_top.mpr ⟨hC₀, ENNReal.sum_ne_top.mpr fun i _ ↦ hC i⟩, fun φ ↦ ?_⟩
  set U := GraphSpace.testFunctionToWkp (n := n) (k := 1) (p := ENNReal.ofReal p) (Ω := Ω) φ
  have hboundaryDomain (i : Fin hΩ.N) :
      eLpNorm (boundaryDistanceQuotient (n := n) (Ω := Ω) i φ)
          (ENNReal.ofReal p) (domainMeasure n Ω) ≤ C i * ‖U‖ₑ := by
    set E := Boundary.C1ExtensionAtlas.Charts.chartOnΩ (n := n) (Ω := Ω) i
    have hsource : E.source ⊆ Ω := fun x hx ↦ by
      rw [Boundary.C1ExtensionAtlas.Charts.chartOnΩ_source] at hx
      exact hx.2
    have hmeasure : (domainMeasure n Ω).restrict E.source = domainMeasure n E.source := by
      simpa [domainMeasure] using
        Measure.restrict_restrict_of_subset (μ := (volume : Measure (ℝ^n))) hsource
    rw [← eLpNorm_restrict_eq_of_support_subset
      (boundaryDistanceQuotient_aestronglyMeasurable (n := n) (Ω := Ω) i φ)
      (boundaryDistanceQuotient_support_subset_chartSource (n := n) (Ω := Ω) i φ), hmeasure]
    exact hbound i φ
  have hsum : eLpNorm (fun x ↦ ∑ i, boundaryDistanceQuotient (n := n) (Ω := Ω) i φ x)
      (ENNReal.ofReal p) (domainMeasure n Ω) ≤
        ∑ i, eLpNorm (boundaryDistanceQuotient (n := n) (Ω := Ω) i φ)
          (ENNReal.ofReal p) (domainMeasure n Ω) := by
    simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := domainMeasure n Ω)
      (f := fun i ↦ boundaryDistanceQuotient (n := n) (Ω := Ω) i φ) (s := Finset.univ) Fact.out
  rw [eLpNorm_congr_ae (domainDistanceQuotient_ae_partition (n := n) (Ω := Ω) φ)]
  calc _ ≤ eLpNorm (interiorDistanceQuotient (n := n) (Ω := Ω) φ)
          (ENNReal.ofReal p) (domainMeasure n Ω) +
        eLpNorm (fun x ↦ ∑ i, boundaryDistanceQuotient (n := n) (Ω := Ω) i φ x)
          (ENNReal.ofReal p) (domainMeasure n Ω) := eLpNorm_add_le Fact.out
    _ ≤ C₀ * ‖U‖ₑ + ∑ i, C i * ‖U‖ₑ :=
      add_le_add (hinterior φ) (hsum.trans (Finset.sum_le_sum fun i _ ↦ hboundaryDomain i))
    _ = (C₀ + ∑ i, C i) * ‖U‖ₑ := by rw [add_mul, Finset.sum_mul]

end SobolevSpace.Hardy
