/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphConstruction
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.AtlasIndependence
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ContinuousApproximation

/-!
# Trace agreement for continuous Sobolev representatives

Evans §5.5, Theorem 1: the bounded trace agrees with restriction for every
`W^{1,p}` function having a continuous representative on the closure, for `1 ≤ p < ∞`.
Inward mollification gives smooth approximants converging both in the Sobolev graph
norm and pointwise on the closure. Continuity of the trace and an almost
everywhere convergent subsequence identify its boundary values.

The geometric endpoints construct the operational atlas from boundedness, openness,
and local C1 graph boundary. The measure is the Euclidean Hausdorff surface
measure restricted to the boundary.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1, pp. 271-273, the trace theorem for bounded
  open sets with C¹ boundary, whose part (i) is the agreement `Tu = u|∂U` for
  `u ∈ W^{1,p}(U) ∩ C(Ū)`, and App. C.1, pp. 710-711, for C¹ boundaries as local graphs.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set Filter Metric
open scoped Distributions ENNReal Topology Sobolev

namespace SobolevSpace.Trace.C1

open Approximation.UpToBoundary GraphSpace Boundary
open Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}

/-- The trace equals any continuous representative on the closure.
An inward partition supplies simultaneous Sobolev and pointwise approximation. -/
theorem traceLp_eq_ae_of_continuousOn [H : C1ExtensionAtlas (m + 1) Ω]
    (P : InwardPartition Ω) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (U : W^{1,ENNReal.ofReal p}(Ω)) {f : ℝ^(m + 1) → ℝ}
    (hf : ContinuousOn f (closure Ω))
    (hUf : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] f) :
    (traceLp p U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] f := by
  obtain ⟨g, hg, hc, hSob, hpoint⟩ := continuous_approximation P
    ENNReal.ofReal_ne_top U hf hUf
  let A (j : ℕ) : W^{1,ENNReal.ofReal p}(Ω) :=
    mkWkpSpaceOnOfContDiff (g j) (hg j) (hc j)
  have htrace := (traceLp (Ω := Ω) p).continuous.continuousAt.tendsto.comp hSob
  obtain ⟨s, hs, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp htrace).exists_seq_tendsto_ae
  have hclass (j : ℕ) :
      (traceLp p (A j) : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] g j := by
    let φ : HalfSpace.GlobalTestFunction m :=
      ⟨⟨g j, hg j, hc j, subset_univ _⟩, subset_univ _⟩
    have hin : globalTestFunctionToDomainW1pLinear (Ω := Ω) (ENNReal.ofReal p) φ =
        A j := by
      rw [globalTestFunctionToDomainW1pLinear_eq_mk]
    rw [← hin, traceLp_classical]
    exact globalTestFunctionBoundaryLpLinear_apply_ae (ENNReal.ofReal p) φ
  have hfrontier : ∀ᵐ x ∂surfaceMeasure Ω, x ∈ frontier Ω := by
    simpa only [surfaceMeasure, Nat.add_sub_cancel] using
      ae_restrict_mem (μ := Measure.euclideanHausdorffMeasure m) isClosed_frontier.measurableSet
  filter_upwards [hlim, ae_all_iff.mpr hclass, hfrontier] with x hx hc hxΩ
  have heq : (fun j ↦ traceLp p (A (s j)) x) = fun j ↦ g (s j) x :=
    funext fun j ↦ hc (s j)
  exact tendsto_nhds_unique hx (heq ▸ (hpoint x (frontier_subset_closure hxΩ)).comp
    hs.tendsto_atTop)

/-- Agreement with continuous representatives uniquely determines the finite-exponent trace. -/
theorem eq_traceLp_of_continuousOn [H : C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (T : W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
      Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω))
    (hT : ∀ (U : W^{1,ENNReal.ofReal p}(Ω)) (f : ℝ^(m + 1) → ℝ),
      ContinuousOn f (closure Ω) →
      baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] f →
      (T U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] f) :
    T = traceLp p := by
  apply eq_traceLp_of_classical p T
  intro φ
  apply Lp.ext
  have hbase : baseRepresentative
      (mkWkpSpaceOnOfContDiff (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := Ω) φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport)
        =ᵐ[domainMeasure (m + 1) Ω] φ.1.toFun := by
    simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (Ω := Ω) φ.1.toFun φ.1.contDiff
        φ.1.hasCompactSupport (baseIndex (m + 1) 1)
  exact (hT _ φ.1.toFun φ.1.contDiff.continuous.continuousOn hbase).trans
    (globalTestFunctionBoundaryLpLinear_apply_ae (ENNReal.ofReal p) φ).symm

/-- The Hilbert trace agrees with continuous representatives on the closure. -/
theorem trace_eq_ae_of_continuousOn [H : C1ExtensionAtlas (m + 1) Ω]
    (P : InwardPartition Ω) (U : H¹(Ω)) {f : ℝ^(m + 1) → ℝ}
    (hf : ContinuousOn f (closure Ω))
    (hUf : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] f) :
    (trace U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] f := by
  obtain ⟨V, rfl⟩ := (domainW1pTwoEquivH1 (Ω := Ω)).surjective U
  rw [show baseRepresentative (domainW1pTwoEquivH1 V) = baseRepresentative V from
    domainW1pTwoEquivH1_coordinate V (baseIndex (m + 1) 1)] at hUf
  rw [← boundaryLpTwoEquivL2_traceLp, boundaryLpTwoEquivL2, Lp.coeFn_congrExponent]
  exact traceLp_eq_ae_of_continuousOn P 2 V hf hUf

/-- Continuous-representative agreement under bounded open C1 graph boundary.
The atlas used by `traceLp` is constructed from these geometric hypotheses. -/
theorem traceLp_eq_ae_of_continuousOn_of_local_graph (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hgraph : HasC1GraphBoundary Ω)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (U : W^{1,ENNReal.ofReal p}(Ω)) {f : ℝ^(m + 1) → ℝ}
    (hf : ContinuousOn f (closure Ω))
    (hUf : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] f) :
    let := hgraph.c1ExtensionAtlas hΩ hb
    (traceLp p U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] f := by
  let := hgraph.c1ExtensionAtlas hΩ hb
  obtain ⟨P⟩ := exists_inwardPartition hΩ hb (hasC1Boundary_of_local_graph hgraph)
  exact traceLp_eq_ae_of_continuousOn P p U hf hUf

/-- Evans §5.5, Theorem 1: for a bounded open `Ω` with C1 graph boundary and real `p ≥ 1`, there
is a bounded linear trace `W^{1,p}(Ω) → Lᵖ(∂Ω)` that agrees almost everywhere on the boundary
with every representative continuous on the closure. -/
theorem exists_trace_of_local_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ T : W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
        Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω),
      (∃ C : ℝ, 0 < C ∧ ∀ U, ‖T U‖ ≤ C * ‖U‖) ∧
      ∀ (U : W^{1,ENNReal.ofReal p}(Ω)) (f : ℝ^(m + 1) → ℝ),
        ContinuousOn f (closure Ω) →
        baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] f →
        (T U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] f := by
  let := hgraph.c1ExtensionAtlas hΩ hb
  refine ⟨traceLp p, ⟨max ‖traceLp (Ω := Ω) p‖ 1, ?_, ?_⟩, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro U
    exact ((traceLp p).le_opNorm U).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg U))
  · intro U f hf hUf
    exact traceLp_eq_ae_of_continuousOn_of_local_graph hΩ hb hgraph p U hf hUf

/-- Raw local-graph geometry determines a unique bounded trace with continuous-representative
agreement. The statement does not require a choice of atlas or inward partition. -/
theorem existsUnique_trace_of_local_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃! T : W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
        Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω),
      (∃ C : ℝ, 0 < C ∧ ∀ U, ‖T U‖ ≤ C * ‖U‖) ∧
      ∀ (U : W^{1,ENNReal.ofReal p}(Ω)) (f : ℝ^(m + 1) → ℝ),
        ContinuousOn f (closure Ω) →
        baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] f →
        (T U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] f := by
  obtain ⟨T, hT⟩ := exists_trace_of_local_graph hΩ hb hgraph p
  refine ⟨T, hT, ?_⟩
  intro S hS
  let := hgraph.c1ExtensionAtlas hΩ hb
  exact (eq_traceLp_of_continuousOn p S hS.2).trans
    (eq_traceLp_of_continuousOn p T hT.2).symm

/-- Evans §5.5, Theorem 1 when, near each boundary point, `Ω` is the region above the graph of a
C1 function after a rigid motion (Evans's definition of a C¹ boundary, App. C.1), for bounded
open `Ω` and real `p ≥ 1`.
No operational atlas, approximation, or boundary agreement is assumed. -/
theorem exists_trace_of_rigid_local_graph (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hgraph : ∀ x ∈ frontier Ω,
      ∃ R : (ℝ^(m + 1)) ≃ᵃⁱ[ℝ] (ℝ^(m + 1)), ∃ r : ℝ, ∃ g : ℝ^m → ℝ,
        0 < r ∧ ContDiffOn ℝ 1 g (ball (HalfSpace.splitTangentialNormal (R x)).1 r) ∧
        ∀ y ∈ ball x r,
          y ∈ Ω ↔ g (HalfSpace.splitTangentialNormal (R y)).1 <
            (HalfSpace.splitTangentialNormal (R y)).2)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ T : W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
        Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω),
      (∃ C : ℝ, 0 < C ∧ ∀ U, ‖T U‖ ≤ C * ‖U‖) ∧
      ∀ (U : W^{1,ENNReal.ofReal p}(Ω)) (f : ℝ^(m + 1) → ℝ),
        ContinuousOn f (closure Ω) →
        baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] f →
        (T U : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] f :=
  exists_trace_of_local_graph hΩ hb (hasC1GraphBoundary_of_rigid_local_graph hgraph) p

end SobolevSpace.Trace.C1
