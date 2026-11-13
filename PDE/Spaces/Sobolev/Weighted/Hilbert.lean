/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.Parity

/-!
# Hilbert completions of weighted Sobolev derivative rows

Let `ι` be finite, let `μ` be a measure, and assign a nonnegative density `w i` to every row.
The space `L2Rows μ w` is the Hilbert direct sum

\[
  \bigoplus_{i \in \iota} L^2(w_i\,d\mu).
\]

For the Sobolev derivative indices through order `k`, `DerivativeL2RowsOn` specializes this
construction to the restricted Lebesgue measure on a domain. An element of the
unweighted graph space whose derivative rows have the required weighted integrability maps
linearly into this Hilbert space. `CompletedHkSpaceOn` is the closure of the range of that map,
so it is a complete real Hilbert space for arbitrary nonnegative densities.

We complete because, without assumptions on the densities, weighted integrability need not
define a closed subspace of the unweighted Sobolev graph space. If a density vanishes, a limit
in the weighted norm can also lose information needed to recover a single distributional base
function, so a completed jet need not be represented by a function with weak derivatives.
Positivity, local reciprocal integrability, or a closability theorem can identify the
completion with a function-based weighted Sobolev space.

## Main results

* `L2Rows`: the finite weighted `L²` direct sum, with Mathlib's `PiLp` completeness,
  inner product, and norm formula.
* `CoordinatesMemL2WithDensities`, `coordinatesMemL2WithDensitiesSubmodule`,
  `toDerivativeL2Rows`, `derivativeL2RowsLinearMap`: weighted integrability of a Sobolev graph
  element and its realization as weighted rows.
* `completedHkSubmoduleOn`, `CompletedHkSpaceOn`: the closure of the realized rows, complete
  by `Submodule.topologicalClosure.completeSpace` for arbitrary nonnegative densities.
* `CompletedHkSpaceOn.ofGraph`, `CompletedHkSpaceOn.denseRange_ofGraph`: realizable Sobolev
  graphs are dense in the completion.
* `CompletedHkSpaceOn.coordinate`, `CompletedHkSpaceOn.baseRow`,
  `CompletedHkSpaceOn.norm_sq_eq_sum`: the row projections and the norm formula.

## References

* A. Kufner and B. Opic, "How to define reasonably weighted Sobolev spaces",
  *Comment. Math. Univ. Carolin.* 25 (1984), no. 3, 537-554, Examples 1.12, 2.5 and 2.6 and
  Remark 3.6, for the difference between the completion in a weighted norm and the space of
  functions with weighted-integrable weak derivatives, which fail to agree for degenerate power
  weights.
  <https://dml.cz/handle/10338.dmlcz/106324>
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace
namespace Weighted

/-! ## Finite rowwise weighted `L²` products -/

/-- The Hilbert direct sum of a finite family of scalar weighted `L²` spaces. -/
abbrev L2Rows {ι α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : ι → α → ℝ≥0∞) : Type _ :=
  PiLp 2 fun i ↦ Lp ℝ 2 (μ.withDensity (w i))

/-! ## Weighted Sobolev derivative rows -/

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- One weighted `L²` space for every symmetric derivative index through order `k`. -/
abbrev DerivativeL2RowsOn (n k : ℕ) (Ω : Set (ℝ^n))
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) : Type :=
  L2Rows (domainMeasure n Ω) w

/-- The weighted `L²` space containing the order-zero row of a derivative jet. -/
abbrev BaseL2On (n k : ℕ) (Ω : Set (ℝ^n))
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) : Type :=
  Lp ℝ 2
    ((domainMeasure n Ω).withDensity (w (GraphSpace.baseIndex n k)))

/-- Project a weighted derivative jet to its order-zero row. -/
def baseRowCLM
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    DerivativeL2RowsOn n k Ω w →L[ℝ] BaseL2On n k Ω w :=
  PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
    (β := fun a : GraphSpace.DerivIndex n k ↦
      Lp ℝ 2 ((domainMeasure n Ω).withDensity (w a)))
    (GraphSpace.baseIndex n k)

/-- The base-row projection evaluates a jet at the order-zero index. -/
@[simp] theorem baseRowCLM_apply
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : DerivativeL2RowsOn n k Ω w) :
    baseRowCLM w U = U (GraphSpace.baseIndex n k) :=
  rfl

/-- Every Sobolev graph coordinate is square-integrable against its assigned density. -/
def CoordinatesMemL2WithDensities
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : W^{k,2}(Ω)) : Prop :=
  ∀ a, CoordinateMemLpWithDensity (w a) U a

/-- The integrability domain for the rowwise weighted realization map.

This submodule carries the norm inherited from the unweighted graph space, in which it need
not be complete. The complete weighted space is `CompletedHkSpaceOn` below. -/
def coordinatesMemL2WithDensitiesSubmodule
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    Submodule ℝ (W^{k,2}(Ω)) where
  carrier := {U | CoordinatesMemL2WithDensities w U}
  zero_mem' := by
    intro a
    have hcoe := (withDensity_absolutelyContinuous
      (domainMeasure n Ω) (w a)).ae_eq
      (Lp.coeFn_zero ℝ 2 (domainMeasure n Ω))
    exact (memLp_congr_ae hcoe).2 MemLp.zero
  add_mem' := by
    intro U V hU hV a
    have hcoe := (withDensity_absolutelyContinuous
      (domainMeasure n Ω) (w a)).ae_eq
      (Lp.coeFn_add
        ((U : GraphSpace.WkpAmbientOn n k 2 Ω) a)
        ((V : GraphSpace.WkpAmbientOn n k 2 Ω) a))
    exact (memLp_congr_ae hcoe).2 ((hU a).add (hV a))
  smul_mem' := by
    intro c U hU a
    have hcoe := (withDensity_absolutelyContinuous
      (domainMeasure n Ω) (w a)).ae_eq
      (Lp.coeFn_smul c ((U : GraphSpace.WkpAmbientOn n k 2 Ω) a))
    exact (memLp_congr_ae hcoe).2 ((hU a).const_smul c)

/-- Membership in the integrability submodule is the predicate `CoordinatesMemL2WithDensities w`. -/
@[simp] theorem mem_coordinatesMemL2WithDensitiesSubmodule_iff
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    {U : W^{k,2}(Ω)} :
    U ∈ coordinatesMemL2WithDensitiesSubmodule w ↔
      CoordinatesMemL2WithDensities w U :=
  Iff.rfl

/-- Assigning the same density to every row recovers the earlier whole-space submodule. -/
theorem coordinatesMemL2WithDensitiesSubmodule_const
    (k : ℕ) (w : ℝ^n → ℝ≥0∞) :
    coordinatesMemL2WithDensitiesSubmodule
        (n := n) (k := k) (Ω := Set.univ) (fun _ ↦ w) =
      coordinatesMemLpWithDensitySubmodule (n := n) (k := k) 2 w := by
  ext U
  rfl

/-- Realize all derivative coordinates of an integrable graph-space element in their respective
weighted `L²` quotients. -/
def toDerivativeL2Rows
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : W^{k,2}(Ω))
    (hU : CoordinatesMemL2WithDensities w U) :
    DerivativeL2RowsOn n k Ω w :=
  WithLp.toLp 2 fun a ↦
    (hU a).toLp
      (((U : GraphSpace.WkpAmbientOn n k 2 Ω) a :
        GraphSpace.DerivLp n 2 Ω) : ℝ^n → ℝ)

/-- Row `a` of the realization is the weighted `L²` class of the `a`-th unweighted
coordinate. -/
@[simp] theorem toDerivativeL2Rows_apply
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : W^{k,2}(Ω))
    (hU : CoordinatesMemL2WithDensities w U)
    (a : GraphSpace.DerivIndex n k) :
    toDerivativeL2Rows w U hU a =
      (hU a).toLp
        (((U : GraphSpace.WkpAmbientOn n k 2 Ω) a :
          GraphSpace.DerivLp n 2 Ω) : ℝ^n → ℝ) :=
  rfl

/-- The weighted realization of Sobolev derivative rows, as a linear map on its natural
integrability domain. -/
def derivativeL2RowsLinearMap
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    coordinatesMemL2WithDensitiesSubmodule (Ω := Ω) w →ₗ[ℝ]
      DerivativeL2RowsOn n k Ω w where
  toFun U := toDerivativeL2Rows w U U.property
  map_add' := by
    intro U V
    apply PiLp.ext
    intro a
    change ((U + V).property a).toLp _ = _
    calc
      ((U + V).property a).toLp
          ((((U + V : coordinatesMemL2WithDensitiesSubmodule w) :
            W^{k,2}(Ω)) :
              GraphSpace.WkpAmbientOn n k 2 Ω) a : ℝ^n → ℝ) =
          ((U.property a).add (V.property a)).toLp
            (fun x ↦
              (((U : W^{k,2}(Ω)) :
                GraphSpace.WkpAmbientOn n k 2 Ω) a : ℝ^n → ℝ) x +
              (((V : W^{k,2}(Ω)) :
                GraphSpace.WkpAmbientOn n k 2 Ω) a : ℝ^n → ℝ) x) := by
            apply MemLp.toLp_congr
            exact (withDensity_absolutelyContinuous
              (domainMeasure n Ω) (w a)).ae_eq
              (Lp.coeFn_add
                (((U : W^{k,2}(Ω)) :
                  GraphSpace.WkpAmbientOn n k 2 Ω) a)
                (((V : W^{k,2}(Ω)) :
                  GraphSpace.WkpAmbientOn n k 2 Ω) a))
      _ = (U.property a).toLp _ + (V.property a).toLp _ :=
        MemLp.toLp_add (U.property a) (V.property a)
  map_smul' := by
    intro c U
    apply PiLp.ext
    intro a
    change ((c • U).property a).toLp _ = _
    calc
      ((c • U).property a).toLp
          ((((c • U : coordinatesMemL2WithDensitiesSubmodule w) :
            W^{k,2}(Ω)) :
              GraphSpace.WkpAmbientOn n k 2 Ω) a : ℝ^n → ℝ) =
          ((U.property a).const_smul c).toLp
            (fun x ↦ c •
              (((U : W^{k,2}(Ω)) :
                GraphSpace.WkpAmbientOn n k 2 Ω) a : ℝ^n → ℝ) x) := by
            apply MemLp.toLp_congr
            exact (withDensity_absolutelyContinuous
              (domainMeasure n Ω) (w a)).ae_eq
              (Lp.coeFn_smul c
                (((U : W^{k,2}(Ω)) :
                  GraphSpace.WkpAmbientOn n k 2 Ω) a))
      _ = c • (U.property a).toLp _ :=
        MemLp.toLp_const_smul c (U.property a)

/-- The closed subspace generated by weighted derivative rows of Sobolev graph-space elements. -/
def completedHkSubmoduleOn
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    Submodule ℝ (DerivativeL2RowsOn n k Ω w) :=
  (derivativeL2RowsLinearMap (Ω := Ω) w).range.topologicalClosure

/-- The Hilbert completion of Sobolev derivative jets in the rowwise weighted `L²` norm. -/
abbrev CompletedHkSpaceOn
    (n k : ℕ) (Ω : Set (ℝ^n))
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) : Type :=
  completedHkSubmoduleOn (Ω := Ω) w

/-- The weighted derivative-jet completion is complete for every choice of densities. -/
instance CompletedHkSpaceOn.instCompleteSpace
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    CompleteSpace (CompletedHkSpaceOn n k Ω w) :=
  Submodule.topologicalClosure.completeSpace
    (derivativeL2RowsLinearMap (Ω := Ω) w).range

/-- Embed an integrable Sobolev graph element into its weighted completion. -/
def CompletedHkSpaceOn.ofGraph
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : coordinatesMemL2WithDensitiesSubmodule (Ω := Ω) w) :
    CompletedHkSpaceOn n k Ω w :=
  ⟨derivativeL2RowsLinearMap (Ω := Ω) w U,
    Submodule.le_topologicalClosure _
      (LinearMap.mem_range_self (derivativeL2RowsLinearMap (Ω := Ω) w) U)⟩

/-- The canonical inclusion of realizable Sobolev graphs into the weighted
completion is linear. -/
def CompletedHkSpaceOn.ofGraphLinearMap
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    coordinatesMemL2WithDensitiesSubmodule (Ω := Ω) w →ₗ[ℝ]
      CompletedHkSpaceOn n k Ω w where
  toFun := CompletedHkSpaceOn.ofGraph w
  map_add' U V := by
    apply Subtype.ext
    exact (derivativeL2RowsLinearMap (Ω := Ω) w).map_add U V
  map_smul' c U := by
    apply Subtype.ext
    exact (derivativeL2RowsLinearMap (Ω := Ω) w).map_smul c U

/-- The linear inclusion agrees with `CompletedHkSpaceOn.ofGraph` on elements. -/
@[simp] theorem CompletedHkSpaceOn.ofGraphLinearMap_apply
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : coordinatesMemL2WithDensitiesSubmodule (Ω := Ω) w) :
    CompletedHkSpaceOn.ofGraphLinearMap w U =
      CompletedHkSpaceOn.ofGraph w U :=
  rfl

/-- Realizable Sobolev graph elements are dense in the completed weighted
derivative-jet space, for arbitrary nonnegative row densities. This is graph
density; smooth compactly supported density requires additional hypotheses on
the weights. -/
theorem CompletedHkSpaceOn.denseRange_ofGraph
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    DenseRange (CompletedHkSpaceOn.ofGraph (Ω := Ω) w) := by
  rw [Metric.denseRange_iff]
  intro Z ε hε
  have hZ : (Z : DerivativeL2RowsOn n k Ω w) ∈
      closure ((derivativeL2RowsLinearMap (Ω := Ω) w).range :
        Set (DerivativeL2RowsOn n k Ω w)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact Z.property
  obtain ⟨Y, hY, hdist⟩ := (Metric.mem_closure_iff.1 hZ) ε hε
  obtain ⟨U, rfl⟩ := hY
  refine ⟨U, ?_⟩
  exact hdist

/-- The `a`-th weighted derivative row of a completed Sobolev jet. -/
def CompletedHkSpaceOn.coordinate
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (a : GraphSpace.DerivIndex n k) :
    CompletedHkSpaceOn n k Ω w →L[ℝ]
      Lp ℝ 2 ((domainMeasure n Ω).withDensity (w a)) :=
  (PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
      (β := fun b : GraphSpace.DerivIndex n k ↦
        Lp ℝ 2 ((domainMeasure n Ω).withDensity (w b))) a).comp
    (Submodule.subtypeL (completedHkSubmoduleOn (Ω := Ω) w))

/-- The order-zero weighted `L²` row of a completed Sobolev jet. -/
def CompletedHkSpaceOn.baseRow
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    CompletedHkSpaceOn n k Ω w →L[ℝ] BaseL2On n k Ω w :=
  (baseRowCLM w).comp
    (Submodule.subtypeL (completedHkSubmoduleOn (Ω := Ω) w))

/-- The base row is the coordinate at the order-zero index. -/
@[simp] theorem CompletedHkSpaceOn.baseRow_apply
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : CompletedHkSpaceOn n k Ω w) :
    CompletedHkSpaceOn.baseRow w U =
      CompletedHkSpaceOn.coordinate w (GraphSpace.baseIndex n k) U :=
  rfl

/-- A function representative of the order-zero row of a completed weighted jet.

As for every Mathlib `Lp` element, this representative is canonical only up to almost-everywhere
equality for the weighted measure. -/
def CompletedHkSpaceOn.baseRepresentative
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : CompletedHkSpaceOn n k Ω w) : ℝ^n → ℝ :=
  CompletedHkSpaceOn.baseRow w U

/-- The order-zero representative of a completed weighted jet belongs to its weighted `L²`
space. -/
theorem CompletedHkSpaceOn.baseRepresentative_memLp
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : CompletedHkSpaceOn n k Ω w) :
    MemLp (CompletedHkSpaceOn.baseRepresentative w U) 2
      ((domainMeasure n Ω).withDensity (w (GraphSpace.baseIndex n k))) :=
  Lp.memLp (CompletedHkSpaceOn.baseRow w U)

/-- The `a`-th coordinate of a completed jet is the `a`-th row of its underlying element of
`DerivativeL2RowsOn`. -/
@[simp] theorem CompletedHkSpaceOn.coordinate_apply
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (a : GraphSpace.DerivIndex n k)
    (U : CompletedHkSpaceOn n k Ω w) :
    CompletedHkSpaceOn.coordinate w a U =
      (U : DerivativeL2RowsOn n k Ω w) a :=
  rfl

/-- The completed weighted Sobolev norm is exactly the finite sum of its row norms. -/
theorem CompletedHkSpaceOn.norm_sq_eq_sum
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (U : CompletedHkSpaceOn n k Ω w) :
    ‖U‖ ^ 2 = ∑ a, ‖CompletedHkSpaceOn.coordinate w a U‖ ^ 2 := by
  change ‖(U : DerivativeL2RowsOn n k Ω w)‖ ^ 2 =
    ∑ a, ‖(U : DerivativeL2RowsOn n k Ω w) a‖ ^ 2
  exact PiLp.norm_sq_eq_of_L2 _ (U : DerivativeL2RowsOn n k Ω w)

end Weighted
end SobolevSpace
