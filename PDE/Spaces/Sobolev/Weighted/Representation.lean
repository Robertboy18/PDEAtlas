/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.Algebra.Module.LinearPMap
public import PDE.Spaces.Sobolev.Weighted.Hilbert
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Faithful realization of weighted Sobolev derivative rows

The weighted row map from `Weighted.Hilbert` can lose information when a density vanishes.
It is faithful (injective) under the natural nondegeneracy condition that the
density assigned to the zeroth derivative row is positive almost everywhere. Only that row
needs to be positive: on an open domain, equality of the underlying Sobolev functions forces
equality of all weak derivatives by uniqueness.

Consequently both `derivativeL2RowsLinearMap` and the canonical map
`CompletedHkSpaceOn.ofGraph` are injective on their Sobolev graph domains. No finiteness,
reciprocal-integrability, or lower-bound assumption on the density is required for this
separation result.

The completion argument is formulated with Mathlib's `LinearPMap` API.
The partial weighted-jet operator sends its order-zero weighted `L²` row to the full derivative
jet. Positivity makes this operator single-valued on realizable Sobolev graphs. If it is closable,
every point of `CompletedHkSpaceOn` is the value of its closed extension at the completed
order-zero row. This is a function-valued representation: the base row is a Mathlib `Lp`
class, and the remaining rows are attached to it by the closure of the derivative graph.

Closability of `weightedJetOperator w` is a hypothesis here. `Weighted.Density` proves it
on open domains when each row measure controls the base measure by a finite constant. Positive
uniform lower bounds on the densities suffice; no upper bounds are required. Weights without these
lower comparisons require a separate argument. The classical discussion of when completion in a
weighted norm gives a space of functions is due to Kufner and Opic.

## Main results

* `eq_of_baseRow_eq`, `derivativeL2RowsLinearMap_injective`, `CompletedHkSpaceOn.ofGraph_injective`:
  faithfulness under almost-everywhere positivity of the order-zero density on an open domain.
* `weightedJetOperator`, `weightedJetOperator_graph`: the partial operator and the
  identification of its graph with `weightedJetGraph`.
* `CompletedHkSpaceOn.exists_closedOperator_representation`,
  `weightedJetOperator_closure_range`: under closability, every completed jet is the value of the
  closed operator at its base row, and the range of the closed operator is the completion.

## References

* A. Kufner and B. Opic, "How to define reasonably weighted Sobolev spaces",
  *Comment. Math. Univ. Carolin.* 25 (1984), no. 3, 537-554, Remark 3.6 and Examples 1.12, 2.5 and
  2.6, for completions in a weighted norm whose elements are not functions with weak derivatives.
  <https://dml.cz/handle/10338.dmlcz/106324>
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace
namespace Weighted

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- Equality of order-zero weighted rows determines an element of the Sobolev graph space when
the domain is open and the order-zero density is positive almost everywhere. -/
theorem eq_of_baseRow_eq
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x)
    {U V : W^{k,2}(Ω)}
    (hU : CoordinatesMemL2WithDensities w U)
    (hV : CoordinatesMemL2WithDensities w V)
    (hbase :
      baseRowCLM w (toDerivativeL2Rows w U hU) =
        baseRowCLM w (toDerivativeL2Rows w V hV)) :
    U = V := by
  apply GraphSpace.WkpSpaceOn.ext_of_base_ae hΩ
  have hbaseWeighted :
      GraphSpace.baseRepresentative U =ᵐ[
        (domainMeasure n Ω).withDensity (w (GraphSpace.baseIndex n k))]
        GraphSpace.baseRepresentative V := by
    exact (MemLp.toLp_eq_toLp_iff
      (hU (GraphSpace.baseIndex n k))
      (hV (GraphSpace.baseIndex n k))).mp hbase
  have hμw :
      domainMeasure n Ω ≪
        (domainMeasure n Ω).withDensity (w (GraphSpace.baseIndex n k)) :=
    withDensity_absolutelyContinuous' hw <|
      hw_pos.mono fun _ hx ↦ hx.ne'
  exact hμw.ae_eq hbaseWeighted

/-- Equality of weighted derivative rows determines an element of the Sobolev graph space when
the domain is open and the density of the zeroth row is positive almost everywhere. -/
theorem eq_of_toDerivativeL2Rows_eq
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x)
    {U V : W^{k,2}(Ω)}
    (hU : CoordinatesMemL2WithDensities w U)
    (hV : CoordinatesMemL2WithDensities w V)
    (hrows : toDerivativeL2Rows w U hU = toDerivativeL2Rows w V hV) :
    U = V := by
  exact eq_of_baseRow_eq hΩ hw hw_pos hU hV <|
    congrArg (baseRowCLM w) hrows

/-! ## The partially defined weighted derivative operator -/

/-- Realize the order-zero weighted `L²` row of an integrable Sobolev graph. -/
def weightedBaseRowLinearMap
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    coordinatesMemL2WithDensitiesSubmodule (Ω := Ω) w →ₗ[ℝ]
      BaseL2On n k Ω w :=
  (baseRowCLM w).toLinearMap.comp
    (derivativeL2RowsLinearMap (Ω := Ω) w)

/-- Positivity of the order-zero density makes the base-row realization faithful. -/
theorem weightedBaseRowLinearMap_injective
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x) :
    Function.Injective (weightedBaseRowLinearMap (Ω := Ω) w) := by
  intro U V hUV
  apply Subtype.ext
  apply eq_of_baseRow_eq hΩ hw hw_pos U.property V.property
  exact hUV

/-- The graph relating a realizable order-zero weighted `L²` function to all of its weighted
Sobolev derivative rows. -/
def weightedJetGraph
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    Submodule ℝ (BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w) :=
  LinearMap.range <|
    (weightedBaseRowLinearMap (Ω := Ω) w).prod
      (derivativeL2RowsLinearMap (Ω := Ω) w)

/-- Membership in the realizable weighted jet graph consists of a realizable full jet together
with its order-zero row. -/
theorem mem_weightedJetGraph_iff
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    {x : BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w} :
    x ∈ weightedJetGraph (Ω := Ω) w ↔
      x.2 ∈ (derivativeL2RowsLinearMap (Ω := Ω) w).range ∧
        x.1 = baseRowCLM w x.2 := by
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨⟨U, rfl⟩, rfl⟩
  · rintro ⟨⟨U, hU⟩, hbase⟩
    refine ⟨U, ?_⟩
    apply Prod.ext
    · change weightedBaseRowLinearMap w U = x.1
      change baseRowCLM w (derivativeL2RowsLinearMap w U) = x.1
      rw [hU]
      exact hbase.symm
    · exact hU

/-- The partial derivative-jet operator determined by realizable Sobolev graphs.

Its graph is proved to be `weightedJetGraph` below when the order-zero density is positive
almost everywhere. Outside that hypothesis, Mathlib's graph constructor has no intended
representation semantics. -/
noncomputable def weightedJetOperator
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    BaseL2On n k Ω w →ₗ.[ℝ] DerivativeL2RowsOn n k Ω w :=
  (weightedJetGraph (Ω := Ω) w).toLinearPMap

private theorem weightedJetGraph_fst_eq_zero
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x)
    (x : BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w)
    (hx : x ∈ weightedJetGraph (Ω := Ω) w)
    (hx_zero : x.1 = 0) :
    x.2 = 0 := by
  obtain ⟨U, rfl⟩ := hx
  simp only [LinearMap.prod_apply, Function.prod_apply] at hx_zero ⊢
  have hU : U = 0 :=
    weightedBaseRowLinearMap_injective hΩ hw hw_pos <| by
      simpa using hx_zero
  subst U
  exact LinearMap.map_zero _

/-- Under positivity of the order-zero density, `weightedJetOperator` has exactly the graph of
realizable weighted Sobolev derivative jets. -/
theorem weightedJetOperator_graph
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x) :
    (weightedJetOperator (Ω := Ω) w).graph = weightedJetGraph (Ω := Ω) w :=
  Submodule.toLinearPMap_graph_eq _
    (weightedJetGraph_fst_eq_zero hΩ hw hw_pos)

/-- Embed a full weighted jet into the graph ambient space by pairing it with its base row. -/
def weightedJetGraphEmbedding
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    DerivativeL2RowsOn n k Ω w →L[ℝ]
      BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w :=
  (baseRowCLM w).prod (ContinuousLinearMap.id ℝ _)

/-- The graph embedding pairs a jet with its order-zero row. -/
@[simp] theorem weightedJetGraphEmbedding_apply
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : DerivativeL2RowsOn n k Ω w) :
    weightedJetGraphEmbedding w U = (baseRowCLM w U, U) :=
  rfl

/-- Pair a completed weighted Sobolev jet with its order-zero `L²` row. -/
def CompletedHkSpaceOn.graphEmbedding
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    CompletedHkSpaceOn n k Ω w →L[ℝ]
      BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w :=
  (CompletedHkSpaceOn.baseRow w).prod
    (Submodule.subtypeL (completedHkSubmoduleOn (Ω := Ω) w))

/-- The graph embedding of a completed jet is its base row paired with the underlying element of
`DerivativeL2RowsOn`. -/
@[simp] theorem CompletedHkSpaceOn.graphEmbedding_apply
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : CompletedHkSpaceOn n k Ω w) :
    CompletedHkSpaceOn.graphEmbedding w U =
      (CompletedHkSpaceOn.baseRow w U,
        (U : DerivativeL2RowsOn n k Ω w)) :=
  rfl

/-- Every completed derivative jet determines a point in the closure of the realizable
base-function/jet graph. -/
theorem CompletedHkSpaceOn.pair_mem_weightedJetGraph_closure
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : CompletedHkSpaceOn n k Ω w) :
    (CompletedHkSpaceOn.baseRow w U,
        (U : DerivativeL2RowsOn n k Ω w)) ∈
      (weightedJetGraph (Ω := Ω) w).topologicalClosure := by
  have hU :
      (U : DerivativeL2RowsOn n k Ω w) ∈
        closure
          ((derivativeL2RowsLinearMap (Ω := Ω) w).range :
            Set (DerivativeL2RowsOn n k Ω w)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact U.property
  have hmaps :
      Set.MapsTo (weightedJetGraphEmbedding (Ω := Ω) w)
        ((derivativeL2RowsLinearMap (Ω := Ω) w).range :
          Set (DerivativeL2RowsOn n k Ω w))
        (weightedJetGraph (Ω := Ω) w :
          Set (BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w)) := by
    rintro V ⟨Z, rfl⟩
    exact ⟨Z, rfl⟩
  have hpair :
      weightedJetGraphEmbedding (Ω := Ω) w
          (U : DerivativeL2RowsOn n k Ω w) ∈
        closure (weightedJetGraph (Ω := Ω) w :
          Set (BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w)) :=
    map_mem_closure
      (weightedJetGraphEmbedding (Ω := Ω) w).continuous hU hmaps
  exact hpair

/-- A closable weighted derivative graph represents every completed jet by its order-zero
weighted `L²` function. The closed operator returns the entire derivative jet at that function,
so the higher rows are not independent completion data. -/
theorem CompletedHkSpaceOn.exists_closedOperator_representation
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x)
    (hclosable : (weightedJetOperator (Ω := Ω) w).IsClosable)
    (U : CompletedHkSpaceOn n k Ω w) :
    ∃ u : (weightedJetOperator (Ω := Ω) w).closure.domain,
      (u : BaseL2On n k Ω w) = CompletedHkSpaceOn.baseRow w U ∧
        (weightedJetOperator (Ω := Ω) w).closure u =
          (U : DerivativeL2RowsOn n k Ω w) := by
  have hpair :
      (CompletedHkSpaceOn.baseRow w U,
          (U : DerivativeL2RowsOn n k Ω w)) ∈
        (weightedJetOperator (Ω := Ω) w).closure.graph := by
    rw [← hclosable.graph_closure_eq_closure_graph,
      weightedJetOperator_graph hΩ hw hw_pos]
    exact U.pair_mem_weightedJetGraph_closure w
  rw [LinearPMap.mem_graph_iff] at hpair
  exact hpair

/-- The base row of a completed jet belongs to the domain of the closed weighted derivative
operator. -/
theorem CompletedHkSpaceOn.baseRow_mem_weightedJetOperator_closure_domain
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x)
    (hclosable : (weightedJetOperator (Ω := Ω) w).IsClosable)
    (U : CompletedHkSpaceOn n k Ω w) :
    CompletedHkSpaceOn.baseRow w U ∈
      (weightedJetOperator (Ω := Ω) w).closure.domain := by
  obtain ⟨u, hu, _⟩ :=
    U.exists_closedOperator_representation hΩ hw hw_pos hclosable
  rw [← hu]
  exact u.property

/-- Applying the closed weighted derivative operator to the completed base function recovers the
entire completed jet. -/
theorem CompletedHkSpaceOn.weightedJetOperator_closure_apply_baseRow
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x)
    (hclosable : (weightedJetOperator (Ω := Ω) w).IsClosable)
    (U : CompletedHkSpaceOn n k Ω w) :
    (weightedJetOperator (Ω := Ω) w).closure
        ⟨CompletedHkSpaceOn.baseRow w U,
          U.baseRow_mem_weightedJetOperator_closure_domain
            hΩ hw hw_pos hclosable⟩ =
      (U : DerivativeL2RowsOn n k Ω w) := by
  obtain ⟨u, hu, hjet⟩ :=
    U.exists_closedOperator_representation hΩ hw hw_pos hclosable
  have heu :
      (⟨CompletedHkSpaceOn.baseRow w U,
          U.baseRow_mem_weightedJetOperator_closure_domain
            hΩ hw hw_pos hclosable⟩ :
        (weightedJetOperator (Ω := Ω) w).closure.domain) = u :=
    Subtype.ext hu.symm
  rw [heu]
  exact hjet

/-- The range of the closed weighted derivative operator is exactly the completed derivative-jet
space. Thus closability upgrades the abstract row completion to a function-based graph space. -/
theorem weightedJetOperator_closure_range
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x)
    (hclosable : (weightedJetOperator (Ω := Ω) w).IsClosable) :
    LinearMap.range (weightedJetOperator (Ω := Ω) w).closure.toFun =
      completedHkSubmoduleOn (Ω := Ω) w := by
  ext U
  constructor
  · rintro ⟨u, rfl⟩
    have hgraph :
        ((u : BaseL2On n k Ω w),
            (weightedJetOperator (Ω := Ω) w).closure u) ∈
          (weightedJetGraph (Ω := Ω) w).topologicalClosure := by
      rw [← weightedJetOperator_graph hΩ hw hw_pos,
        hclosable.graph_closure_eq_closure_graph]
      exact LinearPMap.mem_graph _ u
    have hmaps :
        Set.MapsTo
          (ContinuousLinearMap.snd ℝ (BaseL2On n k Ω w)
            (DerivativeL2RowsOn n k Ω w))
          (weightedJetGraph (Ω := Ω) w :
            Set (BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w))
          ((derivativeL2RowsLinearMap (Ω := Ω) w).range :
            Set (DerivativeL2RowsOn n k Ω w)) := by
      rintro Z ⟨V, rfl⟩
      exact ⟨V, rfl⟩
    have hsnd := map_mem_closure
      (ContinuousLinearMap.snd ℝ (BaseL2On n k Ω w)
        (DerivativeL2RowsOn n k Ω w)).continuous hgraph hmaps
    change (weightedJetOperator (Ω := Ω) w).closure u ∈
      (derivativeL2RowsLinearMap (Ω := Ω) w).range.topologicalClosure
    change (weightedJetOperator (Ω := Ω) w).closure u ∈
      (↑(derivativeL2RowsLinearMap (Ω := Ω) w).range.topologicalClosure :
        Set (DerivativeL2RowsOn n k Ω w))
    rw [Submodule.topologicalClosure_coe]
    exact hsnd
  · intro hU
    let Z : CompletedHkSpaceOn n k Ω w := ⟨U, hU⟩
    obtain ⟨u, _, hu⟩ :=
      Z.exists_closedOperator_representation hΩ hw hw_pos hclosable
    exact ⟨u, hu⟩

/-- The linear realization of weighted derivative rows is injective if the zeroth-row density
is positive almost everywhere on an open domain. -/
theorem derivativeL2RowsLinearMap_injective
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x) :
    Function.Injective (derivativeL2RowsLinearMap (Ω := Ω) w) := by
  intro U V hrows
  apply Subtype.ext
  exact eq_of_toDerivativeL2Rows_eq hΩ hw hw_pos U.property V.property hrows

/-- The canonical inclusion of Sobolev graph elements into the completed weighted row space is
injective if the zeroth-row density is positive almost everywhere on an open domain. -/
theorem CompletedHkSpaceOn.ofGraph_injective
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x) :
    Function.Injective (CompletedHkSpaceOn.ofGraph (Ω := Ω) w) := by
  intro U V hUV
  apply derivativeL2RowsLinearMap_injective hΩ hw hw_pos
  exact congrArg Subtype.val hUV

end Weighted
end SobolevSpace
