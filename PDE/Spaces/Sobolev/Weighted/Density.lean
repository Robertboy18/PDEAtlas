/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.Representation
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
public import PDE.Spaces.Sobolev.Approximation.Mollification.Core
import PDE.Spaces.Sobolev.Approximation.Density.Global
import PDE.Spaces.Sobolev.GraphSpace.Topology.Completeness

/-!
# Density, completion, and closure for weighted Sobolev norms

If the base measure `μ` is bounded above by a finite multiple of each row measure `w a · μ`,
forgetting the weights gives a bounded injection from the weighted completion into the unweighted
Sobolev graph space. On an open domain, each completed jet is determined by its base row, and the
weighted derivative operator is closable. These results allow unbounded weights.

If each row measure is also bounded above by a finite multiple of `μ`, every unweighted Sobolev
graph element has weighted `L²` derivative rows. The weighted realization then has closed range,
and its Hilbert completion is exactly the image of the full unweighted Sobolev graph space.
These uniform measure comparisons are elementary sufficient conditions for the two identifications.

On the whole space, smooth compactly supported functions are dense in the weighted row norm whenever
the row measures have finite uniform upper bounds. Thus smooth-core density allows bounded weights
that vanish, although the closed-range identification does not. Weights that blow up or have
unbounded axis degeneracies require separate cutoff and mollification estimates; `HasSmoothCoreOn`
is the density property they would have to prove.

## Main results

* `derivativeL2RowsCLMOfMeasureLeSmul`, `forgetDerivativeL2RowsCLMOfMeasureLeSmul`: the bounded
  weighted realization and its bounded left inverse under one-sided finite comparisons.
* `CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul`,
  `CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul_injective`: a bounded injection into the unweighted
  Sobolev graph space under lower measure bounds alone.
* `CompletedHkSpaceOn.baseRow_injective_of_measure_le_smul`,
  `weightedJetOperator_isClosable_of_measure_le_smul`,
  `weightedJetOperator_isClosable_of_ae_lower_bound`: base-row uniqueness and closability on open
  domains under lower bounds, without upper bounds on the weights.
* `derivativeL2RowsCLMOfMeasureLeSmul_closedRange`,
  `completedHkSubmoduleOn_eq_range_of_measure_comparable`,
  `completedHkSubmoduleOn_eq_range_of_ae_bounds`: under two-sided comparison the completion is
  exactly the set of realized Sobolev jets.
* `smoothCoreOn`, `HasSmoothCoreOn`, `hasSmoothCoreOn_univ_of_measure_le_smul`,
  `hasSmoothCoreOn_univ_of_ae_upper_bound`: smooth density on `ℝ^n` under finite upper bounds.
* `weightedJetOperator_closure_hasSmoothCore`: under positivity, closability, and smooth density,
  the eligible test functions are a core of the closed weighted derivative operator.

## How it works

We build every map row by row from Mathlib's `Lp.LpToLpOfMeasureLeSMul`, the bounded map
`L²(ν) → L²(μ)` given by a bound `μ ≤ C • ν` (`l2RowsCLMOfMeasureLeSmul`): upper bounds give the
weighted realization `derivativeL2RowsCLMOfMeasureLeSmul`, lower bounds the forgetting map. The
forgetting map returns each realized jet to its Sobolev element, and the graph space is closed in
its ambient product (`GraphSpace.isClosed_WkpSubmoduleOn`), so it sends the whole completion into
`W^{k,2}(Ω)`. Closability reduces to injectivity of the base row, which on an open domain is
`GraphSpace.WkpSpaceOn.ext_of_base_ae`: weak derivatives are determined by the function. Under
two-sided bounds the forgetting map is a bounded left inverse of the realization
(`forgetDerivativeL2RowsCLM_comp_derivativeL2RowsCLM`), so the realization is antilipschitz and
Mathlib's `ContinuousLinearMap.closed_range_of_antilipschitz` closes its range. Smooth density on
`ℝ^n` pushes the unweighted mollifier approximation `GraphSpace.globalApproximation_WkpSpace`
through the bounded realization.

## References

* A. Kufner and B. Opic, "How to define reasonably weighted Sobolev spaces",
  *Comment. Math. Univ. Carolin.* 25 (1984), no. 3, 537-554, Theorem 1.11 and Remark 3.6, for
  weights under which the weighted Sobolev space of functions is complete, and for why defining it
  as a completion can produce elements that are not functions with weak derivatives.
  <https://dml.cz/handle/10338.dmlcz/106324>
-/

@[expose] public section

noncomputable section

open MeasureTheory
open TopologicalSpace
open scoped Distributions ENNReal Topology Sobolev

namespace SobolevSpace
namespace Weighted

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

/-! ## Comparison of a density measure with its base measure -/

/-- An almost-everywhere upper bound on a density gives the corresponding measure bound. -/
theorem withDensity_le_smul_of_ae_le
    (μ : Measure α) (w : α → ℝ≥0∞) (C : ℝ≥0∞)
    (hupper : w ≤ᵐ[μ] fun _ ↦ C) :
    μ.withDensity w ≤ C • μ := by
  rw [← MeasureTheory.withDensity_const]
  exact MeasureTheory.withDensity_mono hupper

/-- An almost-everywhere lower bound on a density gives the corresponding measure bound. -/
theorem smul_le_withDensity_of_ae_le
    (μ : Measure α) (w : α → ℝ≥0∞) (c : ℝ≥0∞)
    (hlower : (fun _ ↦ c) ≤ᵐ[μ] w) :
    c • μ ≤ μ.withDensity w := by
  rw [← MeasureTheory.withDensity_const]
  exact MeasureTheory.withDensity_mono hlower

/-- A strictly positive lower density bound controls the base measure by the weighted measure. -/
theorem le_inv_smul_withDensity_of_pos_le_ae
    (μ : Measure α) (w : α → ℝ≥0∞) (c : ℝ≥0∞)
    (hc : c ≠ 0) (hc_top : c ≠ ∞)
    (hlower : (fun _ ↦ c) ≤ᵐ[μ] w) :
    μ ≤ c⁻¹ • μ.withDensity w := by
  calc
    μ = c⁻¹ • (c • μ) := by
      ext s hs
      simp [Measure.smul_apply, ENNReal.inv_mul_cancel_left hc hc_top]
    _ ≤ c⁻¹ • μ.withDensity w := by
      gcongr
      exact smul_le_withDensity_of_ae_le μ w c hlower

/-! ## Bounded realization and forgetting maps -/

variable {n k : ℕ} {Ω : Set (ℝ^n)}

/-- Change the row measures in a finite weighted `L²` product.  The target
measure in row `a` may be at most a finite multiple `C a` of the source
measure. -/
def l2RowsCLMOfMeasureLeSmul
    (μ : Measure α) (w v : ι → α → ℝ≥0∞)
    (C : ι → ℝ≥0∞) (hC : ∀ a, C a ≠ ∞)
    (hmeasure : ∀ a, μ.withDensity (w a) ≤ C a • μ.withDensity (v a)) :
    L2Rows μ v →L[ℝ] L2Rows μ w :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun a : ι ↦ Lp ℝ 2 (μ.withDensity (w a)))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      (Lp.LpToLpOfMeasureLeSMul (hC a) (hmeasure a)).comp
        (PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
          (β := fun b : ι ↦ Lp ℝ 2 (μ.withDensity (v b))) a))

omit [Fintype ι] in
/-- Row `a` of the change-of-measure map is Mathlib's `Lp.LpToLpOfMeasureLeSMul` applied to
row `a`. -/
@[simp] theorem l2RowsCLMOfMeasureLeSmul_apply
    (μ : Measure α) (w v : ι → α → ℝ≥0∞)
    (C : ι → ℝ≥0∞) (hC : ∀ a, C a ≠ ∞)
    (hmeasure : ∀ a, μ.withDensity (w a) ≤ C a • μ.withDensity (v a))
    (U : L2Rows μ v) (a : ι) :
    l2RowsCLMOfMeasureLeSmul μ w v C hC hmeasure U a =
      Lp.LpToLpOfMeasureLeSMul (hC a) (hmeasure a) (U a) :=
  rfl

/-- Weighted integrability transfers along a finite rowwise domination of
the target measures by the source measures. -/
theorem coordinatesMemL2WithDensities_of_measure_le_smul_of_mem
    (w v : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞)
    (hmeasure : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤
        C a • (domainMeasure n Ω).withDensity (v a))
    (U : W^{k,2}(Ω))
    (hU : CoordinatesMemL2WithDensities v U) :
    CoordinatesMemL2WithDensities w U := by
  intro a
  exact (hU a).of_measure_le_smul (hC a) (hmeasure a)

/-- Changing row measures after realizing a Sobolev graph gives the same
weighted derivative representatives as realizing it directly in the target
weights. -/
theorem l2RowsCLMOfMeasureLeSmul_toDerivativeL2Rows
    (w v : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞)
    (hmeasure : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤
        C a • (domainMeasure n Ω).withDensity (v a))
    (U : W^{k,2}(Ω))
    (hU : CoordinatesMemL2WithDensities v U) :
    l2RowsCLMOfMeasureLeSmul (domainMeasure n Ω) w v C hC hmeasure
        (toDerivativeL2Rows v U hU) =
      toDerivativeL2Rows w U
        (coordinatesMemL2WithDensities_of_measure_le_smul_of_mem
          w v C hC hmeasure U hU) := by
  apply PiLp.ext
  intro a
  apply Lp.ext
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul
      (hC a) (hmeasure a) (toDerivativeL2Rows v U hU a)).trans <|
    ((Measure.absolutelyContinuous_of_le_smul (hmeasure a)).ae_eq
      (MemLp.coeFn_toLp (hU a))).trans
        (MemLp.coeFn_toLp
          (coordinatesMemL2WithDensities_of_measure_le_smul_of_mem
            w v C hC hmeasure U hU a)).symm

/-- Rowwise measure domination controls the distance between two realized
Sobolev graphs by the operator norm of the change-of-measure map. -/
theorem dist_toDerivativeL2Rows_of_measure_le_smul
    (w v : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞)
    (hmeasure : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤
        C a • (domainMeasure n Ω).withDensity (v a))
    (U V : W^{k,2}(Ω))
    (hU : CoordinatesMemL2WithDensities v U)
    (hV : CoordinatesMemL2WithDensities v V) :
    dist
        (toDerivativeL2Rows w U
          (coordinatesMemL2WithDensities_of_measure_le_smul_of_mem
            w v C hC hmeasure U hU))
        (toDerivativeL2Rows w V
          (coordinatesMemL2WithDensities_of_measure_le_smul_of_mem
            w v C hC hmeasure V hV)) ≤
      ‖l2RowsCLMOfMeasureLeSmul
          (domainMeasure n Ω) w v C hC hmeasure‖ *
        dist (toDerivativeL2Rows v U hU) (toDerivativeL2Rows v V hV) := by
  rw [← l2RowsCLMOfMeasureLeSmul_toDerivativeL2Rows w v C hC hmeasure U hU,
    ← l2RowsCLMOfMeasureLeSmul_toDerivativeL2Rows w v C hC hmeasure V hV]
  exact (l2RowsCLMOfMeasureLeSmul
    (domainMeasure n Ω) w v C hC hmeasure).lipschitzWith.dist_le_mul _ _

/-- Every derivative row is weighted-square-integrable when its weighted measure is bounded by a
finite multiple of the base measure. -/
theorem coordinatesMemL2WithDensities_of_measure_le_smul
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞)
    (hupper : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤ C a • domainMeasure n Ω)
    (U : W^{k,2}(Ω)) :
    CoordinatesMemL2WithDensities w U := by
  intro a
  exact (Lp.memLp
    ((U : GraphSpace.WkpAmbientOn n k 2 Ω) a)).of_measure_le_smul
      (hC a) (hupper a)

/-- The continuous map taking a Sobolev graph element to its weighted derivative rows, under a
finite rowwise upper comparison with the base measure. -/
def derivativeL2RowsCLMOfMeasureLeSmul
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞)
    (hupper : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤ C a • domainMeasure n Ω) :
    W^{k,2}(Ω) →L[ℝ] DerivativeL2RowsOn n k Ω w :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun a : GraphSpace.DerivIndex n k ↦
        Lp ℝ 2 ((domainMeasure n Ω).withDensity (w a)))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      (Lp.LpToLpOfMeasureLeSMul (hC a) (hupper a)).comp
        ((PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
          (β := fun _ : GraphSpace.DerivIndex n k ↦
            GraphSpace.DerivLp n 2 Ω) a).comp
          (Submodule.subtypeL (GraphSpace.wkpSubmoduleOn n k 2 Ω))))

/-- Forget the rowwise weights when the base measure is bounded by finite multiples of all
weighted row measures.  The codomain is the unweighted ambient row product; a general weighted
jet need not satisfy the weak-derivative compatibility equations. -/
def forgetDerivativeL2RowsCLMOfMeasureLeSmul
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤
        D a • (domainMeasure n Ω).withDensity (w a)) :
    DerivativeL2RowsOn n k Ω w →L[ℝ]
      GraphSpace.WkpAmbientOn n k 2 Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : GraphSpace.DerivIndex n k ↦
        GraphSpace.DerivLp n 2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      (Lp.LpToLpOfMeasureLeSMul (hD a) (hlower a)).comp
        (PiLp.proj (𝕜 := ℝ) (p := (2 : ℝ≥0∞))
          (β := fun b : GraphSpace.DerivIndex n k ↦
            Lp ℝ 2 ((domainMeasure n Ω).withDensity (w b))) a))

/-- Under a finite upper measure comparison, the continuous realization agrees with
`toDerivativeL2Rows`, the realization on the natural integrability domain. -/
theorem derivativeL2RowsCLMOfMeasureLeSmul_apply
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞)
    (hupper : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤ C a • domainMeasure n Ω)
    (U : W^{k,2}(Ω)) :
    derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper U =
      toDerivativeL2Rows w U
        (coordinatesMemL2WithDensities_of_measure_le_smul
          w C hC hupper U) := by
  apply PiLp.ext
  intro a
  apply Lp.ext
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul
    (hC a) (hupper a) ((U : GraphSpace.WkpAmbientOn n k 2 Ω) a)).trans
      (MemLp.coeFn_toLp
        (coordinatesMemL2WithDensities_of_measure_le_smul
          w C hC hupper U a)).symm

/-- Under a finite upper measure comparison, the weighted realization on its natural
integrability domain has the same range as the continuous realization on the full unweighted
Sobolev graph space. -/
theorem derivativeL2RowsLinearMap_range_eq_of_measure_le_smul
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞)
    (hupper : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤ C a • domainMeasure n Ω) :
    (derivativeL2RowsLinearMap (Ω := Ω) w).range =
      (derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper).range := by
  ext Z
  constructor
  · rintro ⟨U, rfl⟩
    refine ⟨U, ?_⟩
    exact derivativeL2RowsCLMOfMeasureLeSmul_apply
      w C hC hupper U
  · rintro ⟨U, rfl⟩
    let hU := coordinatesMemL2WithDensities_of_measure_le_smul
      w C hC hupper U
    refine ⟨⟨U, hU⟩, ?_⟩
    exact (derivativeL2RowsCLMOfMeasureLeSmul_apply
      w C hC hupper U).symm

/-- Forgetting the weights after weighted realization recovers all unweighted derivative rows. -/
theorem forgetDerivativeL2RowsCLM_comp_derivativeL2RowsCLM
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞) (hD : ∀ a, D a ≠ ∞)
    (hupper : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤ C a • domainMeasure n Ω)
    (hlower : ∀ a,
      domainMeasure n Ω ≤
        D a • (domainMeasure n Ω).withDensity (w a))
    (U : W^{k,2}(Ω)) :
    forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower
        (derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper U) =
      (U : GraphSpace.WkpAmbientOn n k 2 Ω) := by
  apply PiLp.ext
  intro a
  apply Lp.ext
  have hweighted := Lp.coeFn_LpToLpOfMeasureLeSMul
    (hC a) (hupper a) ((U : GraphSpace.WkpAmbientOn n k 2 Ω) a)
  have hbase := Lp.coeFn_LpToLpOfMeasureLeSMul
    (hD a) (hlower a)
    ((derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper U) a)
  exact hbase.trans ((Measure.absolutelyContinuous_of_le_smul (hlower a)).ae_eq hweighted)

/-! ## Lower bounds, completion, and closability -/

/-- Forgetting weights recovers the original graph on the natural weighted-integrability
domain; no upper bound on the weights is needed. -/
theorem forgetDerivativeL2RowsCLMOfMeasureLeSmul_toDerivativeL2Rows
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤ D a • (domainMeasure n Ω).withDensity (w a))
    (U : W^{k,2}(Ω)) (hU : CoordinatesMemL2WithDensities w U) :
    forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower
        (toDerivativeL2Rows w U hU) =
      (U : GraphSpace.WkpAmbientOn n k 2 Ω) := by
  apply PiLp.ext
  intro a
  apply Lp.ext
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul
    (hD a) (hlower a) ((toDerivativeL2Rows w U hU) a)).trans
      ((Measure.absolutelyContinuous_of_le_smul (hlower a)).ae_eq
        (MemLp.coeFn_toLp (hU a)))

/-- Forgetting weights is injective because each weighted measure is absolutely continuous
with respect to the base measure. -/
theorem forgetDerivativeL2RowsCLMOfMeasureLeSmul_injective
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤ D a • (domainMeasure n Ω).withDensity (w a)) :
    Function.Injective (forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower) := by
  intro U V hUV
  apply PiLp.ext
  intro a
  apply Lp.ext
  apply (withDensity_absolutelyContinuous (domainMeasure n Ω) (w a)).ae_eq
  have hU := Lp.coeFn_LpToLpOfMeasureLeSMul (hD a) (hlower a) (U a)
  have hV := Lp.coeFn_LpToLpOfMeasureLeSMul (hD a) (hlower a) (V a)
  have ha := congrArg (fun Z : GraphSpace.WkpAmbientOn n k 2 Ω ↦ Z a) hUV
  change Lp.LpToLpOfMeasureLeSMul (hD a) (hlower a) (U a) =
    Lp.LpToLpOfMeasureLeSMul (hD a) (hlower a) (V a) at ha
  rw [ha] at hU
  exact hU.symm.trans hV

/-- Forgetting a realized weighted graph recovers its unweighted ambient rows. -/
theorem forgetDerivativeL2RowsCLMOfMeasureLeSmul_derivativeL2RowsLinearMap
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤ D a • (domainMeasure n Ω).withDensity (w a))
    (U : coordinatesMemL2WithDensitiesSubmodule (Ω := Ω) w) :
    forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower
        (derivativeL2RowsLinearMap w U) =
      ((U : W^{k,2}(Ω)) : GraphSpace.WkpAmbientOn n k 2 Ω) :=
  forgetDerivativeL2RowsCLMOfMeasureLeSmul_toDerivativeL2Rows
    w D hD hlower U U.property

/-- The unweighted rows of a completed weighted jet still satisfy the weak-derivative
constraints: these constraints are closed in the unweighted ambient space. -/
theorem CompletedHkSpaceOn.forget_mem_wkpSubmoduleOn
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤ D a • (domainMeasure n Ω).withDensity (w a))
    (U : CompletedHkSpaceOn n k Ω w) :
    forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower U ∈
      GraphSpace.wkpSubmoduleOn n k 2 Ω := by
  have hmaps : Set.MapsTo
      (forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower)
      ((derivativeL2RowsLinearMap (Ω := Ω) w).range : Set _)
      (GraphSpace.wkpSubmoduleOn n k 2 Ω : Set _) := by
    rintro _ ⟨V, rfl⟩
    rw [forgetDerivativeL2RowsCLMOfMeasureLeSmul_derivativeL2RowsLinearMap]
    exact V.val.property
  exact hmaps.closure_left
    (forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower).continuous
    (GraphSpace.isClosed_WkpSubmoduleOn n k 2 Ω) U.property

/-- A rowwise lower measure bound gives a bounded map from the weighted completion into the
ordinary Sobolev graph space. The densities may be unbounded. -/
def CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤ D a • (domainMeasure n Ω).withDensity (w a)) :
    CompletedHkSpaceOn n k Ω w →L[ℝ] W^{k,2}(Ω) :=
  ((forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower).comp
    (Submodule.subtypeL (completedHkSubmoduleOn (Ω := Ω) w))).codRestrict
      (GraphSpace.wkpSubmoduleOn n k 2 Ω)
      (CompletedHkSpaceOn.forget_mem_wkpSubmoduleOn w D hD hlower)

/-- The completed-to-unweighted Sobolev map loses no derivative rows. -/
theorem CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul_injective
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤ D a • (domainMeasure n Ω).withDensity (w a)) :
    Function.Injective (CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul w D hD hlower) := by
  intro U V hUV
  apply Subtype.ext
  apply forgetDerivativeL2RowsCLMOfMeasureLeSmul_injective w D hD hlower
  exact congrArg Subtype.val hUV

/-- On realizable graphs, the completed-to-unweighted map returns the original Sobolev
element. -/
@[simp] theorem CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul_ofGraph
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤ D a • (domainMeasure n Ω).withDensity (w a))
    (U : coordinatesMemL2WithDensitiesSubmodule (Ω := Ω) w) :
    CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul w D hD hlower
        (CompletedHkSpaceOn.ofGraph w U) =
      (U : W^{k,2}(Ω)) := by
  apply Subtype.ext
  exact forgetDerivativeL2RowsCLMOfMeasureLeSmul_derivativeL2RowsLinearMap
    w D hD hlower U

/-- The Sobolev norm of a completed jet is controlled by its weighted norm and the
operator norm of the rowwise forgetting map. -/
theorem CompletedHkSpaceOn.norm_toHkCLMOfMeasureLeSmul_le
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤ D a • (domainMeasure n Ω).withDensity (w a))
    (U : CompletedHkSpaceOn n k Ω w) :
    ‖CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul w D hD hlower U‖ ≤
      ‖forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower‖ * ‖U‖ :=
  (forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower).le_opNorm U

/-- A completed weighted jet is determined by its base row on an open domain when
all weighted row norms control the unweighted row norms. -/
theorem CompletedHkSpaceOn.baseRow_injective_of_measure_le_smul
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤ D a • (domainMeasure n Ω).withDensity (w a))
    (hΩ : IsOpen Ω) :
    Function.Injective (CompletedHkSpaceOn.baseRow (Ω := Ω) w) := by
  intro U V hUV
  apply CompletedHkSpaceOn.toHkCLMOfMeasureLeSmul_injective w D hD hlower
  apply GraphSpace.WkpSpaceOn.ext_of_base_ae hΩ
  change (Lp.LpToLpOfMeasureLeSMul
      (hD (GraphSpace.baseIndex n k)) (hlower (GraphSpace.baseIndex n k))
      (CompletedHkSpaceOn.baseRow w U) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
    (Lp.LpToLpOfMeasureLeSMul
      (hD (GraphSpace.baseIndex n k)) (hlower (GraphSpace.baseIndex n k))
      (CompletedHkSpaceOn.baseRow w V) : ℝ^n → ℝ)
  rw [hUV]

/-- Rowwise lower measure bounds make the weighted derivative operator closable on
an open domain, including for unbounded densities. -/
theorem weightedJetOperator_isClosable_of_measure_le_smul
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hD : ∀ a, D a ≠ ∞)
    (hlower : ∀ a,
      domainMeasure n Ω ≤ D a • (domainMeasure n Ω).withDensity (w a))
    (hΩ : IsOpen Ω) :
    (weightedJetOperator (Ω := Ω) w).IsClosable := by
  have hgraph : ∀ x ∈ (weightedJetGraph (Ω := Ω) w).topologicalClosure,
      x.1 = 0 → x.2 = 0 := by
    intro x hx hxzero
    have hrows : x.2 ∈ completedHkSubmoduleOn (Ω := Ω) w :=
      map_mem_closure continuous_snd hx
        (fun _ hy ↦ (mem_weightedJetGraph_iff.mp hy).1)
    have hbase : x.1 = baseRowCLM w x.2 := by
      have hmaps : (weightedJetGraph (Ω := Ω) w : Set _) ⊆
          {y : BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w |
            y.1 = baseRowCLM w y.2} :=
        fun _ hy ↦ (mem_weightedJetGraph_iff.mp hy).2
      exact closure_minimal hmaps
        (isClosed_eq continuous_fst ((baseRowCLM w).continuous.comp continuous_snd)) hx
    let U : CompletedHkSpaceOn n k Ω w := ⟨x.2, hrows⟩
    have hU : U = 0 := by
      apply CompletedHkSpaceOn.baseRow_injective_of_measure_le_smul w D hD hlower hΩ
      exact (hbase.symm.trans hxzero).trans (map_zero _).symm
    exact congrArg Subtype.val hU
  refine ⟨(weightedJetGraph (Ω := Ω) w).topologicalClosure.toLinearPMap, ?_⟩
  change (weightedJetGraph (Ω := Ω) w).toLinearPMap.graph.topologicalClosure = _
  rw [Submodule.toLinearPMap_graph_eq _
    (fun x hx hxzero ↦ hgraph x
      ((weightedJetGraph (Ω := Ω) w).le_topologicalClosure hx) hxzero),
    Submodule.toLinearPMap_graph_eq _ hgraph]

/-- Positive lower bounds for the densities imply closability without any upper
bound or smoothness assumption on the weights. -/
theorem weightedJetOperator_isClosable_of_ae_lower_bound
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (c : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hc : ∀ a, c a ≠ 0) (hc_top : ∀ a, c a ≠ ∞)
    (hlower : ∀ a, (fun _ ↦ c a) ≤ᵐ[domainMeasure n Ω] w a)
    (hΩ : IsOpen Ω) :
    (weightedJetOperator (Ω := Ω) w).IsClosable :=
  weightedJetOperator_isClosable_of_measure_le_smul w (fun a ↦ (c a)⁻¹)
    (fun a ↦ ENNReal.inv_ne_top.mpr (hc a))
    (fun a ↦ le_inv_smul_withDensity_of_pos_le_ae
      (domainMeasure n Ω) (w a) (c a) (hc a) (hc_top a) (hlower a)) hΩ

/-! ## Two-sided comparison and identification of the completion -/

/-- Uniform two-sided measure comparison makes weighted realization antilipschitz. -/
theorem derivativeL2RowsCLMOfMeasureLeSmul_antilipschitz
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞) (hD : ∀ a, D a ≠ ∞)
    (hupper : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤ C a • domainMeasure n Ω)
    (hlower : ∀ a,
      domainMeasure n Ω ≤
        D a • (domainMeasure n Ω).withDensity (w a)) :
    AntilipschitzWith
      ‖forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower‖₊
      (derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro U V
  rw [show dist U V = dist
      (forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower
        (derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper U))
      (forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower
        (derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper V)) by
    simp only [forgetDerivativeL2RowsCLM_comp_derivativeL2RowsCLM]
    rfl]
  exact (forgetDerivativeL2RowsCLMOfMeasureLeSmul w D hD hlower).lipschitzWith.dist_le_mul _ _

/-- Under two-sided finite measure comparison, the weighted realization range is closed. -/
theorem derivativeL2RowsCLMOfMeasureLeSmul_closedRange
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞) (hD : ∀ a, D a ≠ ∞)
    (hupper : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤ C a • domainMeasure n Ω)
    (hlower : ∀ a,
      domainMeasure n Ω ≤
        D a • (domainMeasure n Ω).withDensity (w a)) :
    (derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper).range.topologicalClosure =
      (derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper).range :=
  ContinuousLinearMap.closed_range_of_antilipschitz
    (derivativeL2RowsCLMOfMeasureLeSmul_antilipschitz
      w C D hC hD hupper hlower)

/-- Under two-sided finite measure comparison, the completion of realizable weighted Sobolev
jets is precisely the range of unweighted Sobolev graph elements. -/
theorem completedHkSubmoduleOn_eq_range_of_measure_comparable
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C D : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞) (hD : ∀ a, D a ≠ ∞)
    (hupper : ∀ a,
      (domainMeasure n Ω).withDensity (w a) ≤ C a • domainMeasure n Ω)
    (hlower : ∀ a,
      domainMeasure n Ω ≤
        D a • (domainMeasure n Ω).withDensity (w a)) :
    completedHkSubmoduleOn (Ω := Ω) w =
      (derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper).range := by
  rw [completedHkSubmoduleOn]
  rw [derivativeL2RowsLinearMap_range_eq_of_measure_le_smul w C hC hupper,
    derivativeL2RowsCLMOfMeasureLeSmul_closedRange
    w C D hC hD hupper hlower]

/-- Pointwise version of the completion-identification theorem.  If every density lies almost
everywhere between a strictly positive constant and a finite constant, no new derivative jets are
created by completing in the weighted norm. -/
theorem completedHkSubmoduleOn_eq_range_of_ae_bounds
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (c C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hc : ∀ a, c a ≠ 0) (hc_top : ∀ a, c a ≠ ∞)
    (hC : ∀ a, C a ≠ ∞)
    (hlower : ∀ a, (fun _ ↦ c a) ≤ᵐ[domainMeasure n Ω] w a)
    (hupper : ∀ a, w a ≤ᵐ[domainMeasure n Ω] fun _ ↦ C a) :
    completedHkSubmoduleOn (Ω := Ω) w =
      (derivativeL2RowsCLMOfMeasureLeSmul w C hC
        (fun a ↦ withDensity_le_smul_of_ae_le
          (domainMeasure n Ω) (w a) (C a) (hupper a))).range := by
  exact completedHkSubmoduleOn_eq_range_of_measure_comparable
    (w := w) (C := C) (D := fun a ↦ (c a)⁻¹)
    (hC := hC) (hD := fun a ↦ ENNReal.inv_ne_top.mpr (hc a))
    (hupper := fun a ↦ withDensity_le_smul_of_ae_le
      (domainMeasure n Ω) (w a) (C a) (hupper a))
    (hlower := fun a ↦ le_inv_smul_withDensity_of_pos_le_ae
      (domainMeasure n Ω) (w a) (c a) (hc a) (hc_top a) (hlower a))

/-! ## Smooth density in the weighted row norm -/

/-- Global smooth compactly supported functions whose Sobolev derivative
rows are integrable against their assigned weights.  This is a submodule of
Mathlib's test-function space; membership is the concrete integrability
obligation for a possibly singular weight. -/
def smoothCoreOn
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    Submodule ℝ 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
  (coordinatesMemL2WithDensitiesSubmodule (Ω := Ω) w).comap
    (GraphSpace.globalTestFunctionToWkpOnLinear
      (n := n) (k := k) (p := 2) (Ω := Ω))

/-- A test function lies in the smooth core iff the rows of its Sobolev graph are
square-integrable against their assigned weights. -/
@[simp] theorem mem_smoothCoreOn_iff
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    {φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)} :
    φ ∈ smoothCoreOn (Ω := Ω) w ↔
      CoordinatesMemL2WithDensities w
        (GraphSpace.globalTestFunctionToWkpOnLinear
          (n := n) (k := k) (p := 2) (Ω := Ω) φ) :=
  Iff.rfl

/-- Regard an eligible test function as an integrable weighted Sobolev
graph. -/
def smoothCoreToGraphLinearMap
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    smoothCoreOn (Ω := Ω) w →ₗ[ℝ]
      coordinatesMemL2WithDensitiesSubmodule (Ω := Ω) w where
  toFun φ :=
    ⟨GraphSpace.globalTestFunctionToWkpOnLinear
      (n := n) (k := k) (p := 2) (Ω := Ω) φ, φ.property⟩
  map_add' φ ψ := by
    apply Subtype.ext
    exact (GraphSpace.globalTestFunctionToWkpOnLinear
      (n := n) (k := k) (p := 2) (Ω := Ω)).map_add φ ψ
  map_smul' c φ := by
    apply Subtype.ext
    exact (GraphSpace.globalTestFunctionToWkpOnLinear
      (n := n) (k := k) (p := 2) (Ω := Ω)).map_smul c φ

/-- The Sobolev graph underlying a smooth-core element is the graph of the test function. -/
@[simp] theorem smoothCoreToGraphLinearMap_apply
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (φ : smoothCoreOn (Ω := Ω) w) :
    (smoothCoreToGraphLinearMap w φ : W^{k,2}(Ω)) =
      GraphSpace.globalTestFunctionToWkpOnLinear
        (n := n) (k := k) (p := 2) (Ω := Ω) φ :=
  rfl

/-- The canonical map from the eligible smooth core into the completed
weighted derivative-jet space. -/
def smoothCoreToCompletedLinearMap
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    smoothCoreOn (Ω := Ω) w →ₗ[ℝ] CompletedHkSpaceOn n k Ω w :=
  (CompletedHkSpaceOn.ofGraphLinearMap w).comp
    (smoothCoreToGraphLinearMap w)

/-- A row weight has a smooth core when eligible global test functions are
dense in its completed weighted Sobolev derivative-jet space.

It holds under the uniform upper bounds proved below; singular or unbounded
weights require their own cutoff and mollification estimates. -/
def HasSmoothCoreOn
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) : Prop :=
  DenseRange (smoothCoreToCompletedLinearMap (Ω := Ω) w)

/-! ## Smooth cores of the closed weighted derivative operator -/

/-- The full weighted derivative jet of an eligible smooth function. -/
def smoothCoreToDerivativeL2RowsLinearMap
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    smoothCoreOn (Ω := Ω) w →ₗ[ℝ] DerivativeL2RowsOn n k Ω w :=
  (derivativeL2RowsLinearMap (Ω := Ω) w).comp
    (smoothCoreToGraphLinearMap w)

/-- The graph of the weighted derivative operator restricted to eligible smooth compactly
supported functions. -/
def smoothWeightedJetGraph
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    Submodule ℝ (BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w) :=
  LinearMap.range <|
    ((weightedBaseRowLinearMap (Ω := Ω) w).comp
      (smoothCoreToGraphLinearMap w)).prod
        (smoothCoreToDerivativeL2RowsLinearMap w)

/-- The partially defined weighted derivative operator on the eligible smooth core. -/
noncomputable def smoothWeightedJetOperator
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    BaseL2On n k Ω w →ₗ.[ℝ] DerivativeL2RowsOn n k Ω w :=
  (smoothWeightedJetGraph (Ω := Ω) w).toLinearPMap

private theorem smoothWeightedJetGraph_fst_eq_zero
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x)
    (x : BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w)
    (hx : x ∈ smoothWeightedJetGraph (Ω := Ω) w)
    (hx_zero : x.1 = 0) :
    x.2 = 0 := by
  obtain ⟨φ, rfl⟩ := hx
  simp only [LinearMap.prod_apply, Function.prod_apply] at hx_zero ⊢
  have hgraph : smoothCoreToGraphLinearMap w φ = 0 :=
    weightedBaseRowLinearMap_injective hΩ hw hw_pos <| by
      simpa using hx_zero
  rw [smoothCoreToDerivativeL2RowsLinearMap, LinearMap.comp_apply, hgraph]
  exact LinearMap.map_zero _

/-- Under positivity of the order-zero density, the smooth partial operator has precisely the
graph generated by eligible test functions. -/
theorem smoothWeightedJetOperator_graph
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x) :
    (smoothWeightedJetOperator (Ω := Ω) w).graph =
      smoothWeightedJetGraph (Ω := Ω) w :=
  Submodule.toLinearPMap_graph_eq _
    (smoothWeightedJetGraph_fst_eq_zero hΩ hw hw_pos)

/-- Every smooth weighted jet is a realizable Sobolev jet. -/
theorem smoothWeightedJetGraph_le_weightedJetGraph
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞) :
    smoothWeightedJetGraph (Ω := Ω) w ≤ weightedJetGraph (Ω := Ω) w := by
  rintro _ ⟨φ, rfl⟩
  exact ⟨smoothCoreToGraphLinearMap w φ, rfl⟩

/-- Smooth density in the completed jet norm is exactly density of the corresponding smooth
operator graph inside the realizable weighted derivative graph. -/
theorem smoothWeightedJetGraph_topologicalClosure_eq
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hcore : HasSmoothCoreOn (Ω := Ω) w) :
    (smoothWeightedJetGraph (Ω := Ω) w).topologicalClosure =
      (weightedJetGraph (Ω := Ω) w).topologicalClosure := by
  apply le_antisymm
  · exact Submodule.topologicalClosure_mono
      (smoothWeightedJetGraph_le_weightedJetGraph (Ω := Ω) w)
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨U, rfl⟩
      let Z : CompletedHkSpaceOn n k Ω w := CompletedHkSpaceOn.ofGraph w U
      have hZ :
          Z ∈ closure
            (Set.range (smoothCoreToCompletedLinearMap (Ω := Ω) w)) := by
        rw [hcore.closure_range]
        exact Set.mem_univ Z
      have hmaps :
          Set.MapsTo (CompletedHkSpaceOn.graphEmbedding (Ω := Ω) w)
            (Set.range (smoothCoreToCompletedLinearMap (Ω := Ω) w))
            (smoothWeightedJetGraph (Ω := Ω) w :
              Set (BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w)) := by
        rintro _ ⟨φ, rfl⟩
        exact ⟨φ, rfl⟩
      have hpair :
          CompletedHkSpaceOn.graphEmbedding (Ω := Ω) w Z ∈
            closure (smoothWeightedJetGraph (Ω := Ω) w :
              Set (BaseL2On n k Ω w × DerivativeL2RowsOn n k Ω w)) :=
        map_mem_closure
          (CompletedHkSpaceOn.graphEmbedding (Ω := Ω) w).continuous hZ hmaps
      exact hpair
    · exact (smoothWeightedJetGraph (Ω := Ω) w).isClosed_topologicalClosure

/-- If the realizable weighted derivative operator is closable and eligible test functions are
dense, closing the smooth operator gives the same closed operator. -/
theorem smoothWeightedJetOperator_closure_eq
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x)
    (hcore : HasSmoothCoreOn (Ω := Ω) w)
    (hclosable : (weightedJetOperator (Ω := Ω) w).IsClosable) :
    (smoothWeightedJetOperator (Ω := Ω) w).closure =
      (weightedJetOperator (Ω := Ω) w).closure := by
  have hsmooth : (smoothWeightedJetOperator (Ω := Ω) w).IsClosable := by
    refine ⟨(weightedJetOperator (Ω := Ω) w).closure, ?_⟩
    rw [smoothWeightedJetOperator_graph hΩ hw hw_pos,
      smoothWeightedJetGraph_topologicalClosure_eq hcore,
      ← weightedJetOperator_graph hΩ hw hw_pos,
      hclosable.graph_closure_eq_closure_graph]
  apply LinearPMap.eq_of_eq_graph
  rw [← hsmooth.graph_closure_eq_closure_graph,
    smoothWeightedJetOperator_graph hΩ hw hw_pos,
    smoothWeightedJetGraph_topologicalClosure_eq hcore,
    ← weightedJetOperator_graph hΩ hw hw_pos,
    hclosable.graph_closure_eq_closure_graph]

/-- Under positivity, closability, and smooth density, eligible smooth compactly supported
functions form a core for the closed weighted derivative operator in Mathlib's graph sense. -/
theorem weightedJetOperator_closure_hasSmoothCore
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hΩ : IsOpen Ω)
    (hw : AEMeasurable (w (GraphSpace.baseIndex n k)) (domainMeasure n Ω))
    (hw_pos : ∀ᵐ x ∂domainMeasure n Ω, 0 < w (GraphSpace.baseIndex n k) x)
    (hcore : HasSmoothCoreOn (Ω := Ω) w)
    (hclosable : (weightedJetOperator (Ω := Ω) w).IsClosable) :
    (weightedJetOperator (Ω := Ω) w).closure.HasCore
      (smoothWeightedJetOperator (Ω := Ω) w).domain := by
  rw [← smoothWeightedJetOperator_closure_eq hΩ hw hw_pos hcore hclosable]
  exact (smoothWeightedJetOperator (Ω := Ω) w).closureHasCore

/-- Two continuous forms on the completed weighted Sobolev space are equal if
they agree on its smooth core.  In particular, a weighted integration-by-parts
identity proved for eligible smooth compactly supported functions extends to
every completed jet once both sides define continuous forms in the completed
weighted norm. -/
theorem HasSmoothCoreOn.continuous_ext
    {β : Type*} [TopologicalSpace β] [T2Space β]
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (hcore : HasSmoothCoreOn (Ω := Ω) w)
    {F G : CompletedHkSpaceOn n k Ω w → β}
    (hF : Continuous F) (hG : Continuous G)
    (h_eq : ∀ φ : smoothCoreOn (Ω := Ω) w,
      F (smoothCoreToCompletedLinearMap w φ) =
        G (smoothCoreToCompletedLinearMap w φ)) :
    F = G :=
  hcore.equalizer hF hG (funext h_eq)

/-- It suffices to approximate every realizable weighted Sobolev graph by
eligible test functions.  The result then follows for the completion because
realizable graphs are dense there by construction. -/
theorem HasSmoothCoreOn.of_graph_approximation
    {w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞}
    (happrox : ∀ U : coordinatesMemL2WithDensitiesSubmodule (Ω := Ω) w,
      ∀ ε > 0, ∃ φ : smoothCoreOn (Ω := Ω) w,
        dist (smoothCoreToCompletedLinearMap w φ)
          (CompletedHkSpaceOn.ofGraph w U) < ε) :
    HasSmoothCoreOn (Ω := Ω) w := by
  rw [HasSmoothCoreOn, Metric.denseRange_iff]
  intro Z ε hε
  obtain ⟨U, hUZ⟩ :=
    (Metric.denseRange_iff.mp
      (CompletedHkSpaceOn.denseRange_ofGraph (Ω := Ω) w)) Z (ε / 2) (half_pos hε)
  obtain ⟨φ, hφU⟩ := happrox U (ε / 2) (half_pos hε)
  refine ⟨φ, (dist_triangle Z (CompletedHkSpaceOn.ofGraph w U)
    (smoothCoreToCompletedLinearMap w φ)).trans_lt ?_⟩
  calc
    dist Z (CompletedHkSpaceOn.ofGraph w U) +
        dist (CompletedHkSpaceOn.ofGraph w U)
          (smoothCoreToCompletedLinearMap w φ) < ε / 2 + ε / 2 := by
      apply add_lt_add hUZ
      simpa only [dist_comm] using hφU
    _ = ε := by ring

/-- Whole-space smooth compactly supported Sobolev functions approximate every graph element in
the weighted derivative-row norm when each weight has a finite uniform upper measure bound. -/
theorem globalApproximation_derivativeL2Rows
    (mollifier : Approximation.Mollifier n)
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞)
    (hupper : ∀ a,
      (domainMeasure n Set.univ).withDensity (w a) ≤
        C a • domainMeasure n Set.univ)
    (U : W^{k,2}(ℝ^n)) :
    ∃ f_m : ℕ → (ℝ^n → ℝ),
    ∃ hf_m : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (f_m m),
    ∃ hcs_m : ∀ m, HasCompactSupport (f_m m),
      Filter.Tendsto
        (fun m ↦
          derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper
            (GraphSpace.mkWkpSpaceOnOfContDiff
              (n := n) (k := k) (p := 2) (Ω := Set.univ)
              (f_m m) (hf_m m) (hcs_m m)))
        Filter.atTop
        (𝓝 (derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper U)) := by
  obtain ⟨f_m, hf_m, hcs_m, hconv⟩ :=
    GraphSpace.globalApproximation_WkpSpace mollifier (by norm_num) k U
  refine ⟨f_m, hf_m, hcs_m, ?_⟩
  have hconv' :
      Filter.Tendsto
        (fun m ↦ GraphSpace.mkWkpSpaceOnOfContDiff
          (n := n) (k := k) (p := 2) (Ω := Set.univ)
          (f_m m) (hf_m m) (hcs_m m))
        Filter.atTop (𝓝 U) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa using hconv
  exact ((derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper).continuous.tendsto U).comp hconv'

/-- Uniform finite upper bounds on all row measures give the completed
whole-space weighted Sobolev space a smooth compactly supported core.  A
positive lower bound is not needed: the conclusion concerns the derivative-jet
completion and therefore remains valid for bounded weights that vanish. -/
theorem hasSmoothCoreOn_univ_of_measure_le_smul
    (mollifier : Approximation.Mollifier n)
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞)
    (hupper : ∀ a,
      (domainMeasure n Set.univ).withDensity (w a) ≤
        C a • domainMeasure n Set.univ) :
    HasSmoothCoreOn (Ω := Set.univ) w := by
  apply HasSmoothCoreOn.of_graph_approximation
  intro U ε hε
  obtain ⟨f, hf, hcompact, hconv⟩ :=
    globalApproximation_derivativeL2Rows mollifier w C hC hupper U
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv ε hε
  let φ₀ : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    ⟨f N, hf N, hcompact N, Set.subset_univ _⟩
  have hφ₀ : CoordinatesMemL2WithDensities w
      (GraphSpace.globalTestFunctionToWkpOnLinear
        (n := n) (k := k) (p := 2) (Ω := Set.univ) φ₀) :=
    coordinatesMemL2WithDensities_of_measure_le_smul
      w C hC hupper _
  let φ : smoothCoreOn (Ω := Set.univ) w := ⟨φ₀, hφ₀⟩
  refine ⟨φ, ?_⟩
  have hsmoothRows :
      derivativeL2RowsLinearMap (Ω := Set.univ) w
          (smoothCoreToGraphLinearMap w φ) =
        derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper
          (GraphSpace.globalTestFunctionToWkpOnLinear
            (n := n) (k := k) (p := 2) (Ω := Set.univ) φ₀) := by
    exact (derivativeL2RowsCLMOfMeasureLeSmul_apply
      w C hC hupper _).symm
  have hURows :
      derivativeL2RowsLinearMap (Ω := Set.univ) w U =
        derivativeL2RowsCLMOfMeasureLeSmul w C hC hupper U := by
    exact (derivativeL2RowsCLMOfMeasureLeSmul_apply
      w C hC hupper U).symm
  change dist
    (derivativeL2RowsLinearMap (Ω := Set.univ) w
      (smoothCoreToGraphLinearMap w φ))
    (derivativeL2RowsLinearMap (Ω := Set.univ) w U) < ε
  rw [hsmoothRows, hURows]
  simpa [φ₀, GraphSpace.globalTestFunctionToWkpOnLinear,
    GraphSpace.globalTestFunctionToWkpOn] using hN N le_rfl

/-- Pointwise almost-everywhere upper bounds are a convenient sufficient
condition for whole-space smooth-core density. -/
theorem hasSmoothCoreOn_univ_of_ae_upper_bound
    (mollifier : Approximation.Mollifier n)
    (w : GraphSpace.DerivIndex n k → ℝ^n → ℝ≥0∞)
    (C : GraphSpace.DerivIndex n k → ℝ≥0∞)
    (hC : ∀ a, C a ≠ ∞)
    (hupper : ∀ a,
      w a ≤ᵐ[domainMeasure n Set.univ] fun _ ↦ C a) :
    HasSmoothCoreOn (Ω := Set.univ) w :=
  hasSmoothCoreOn_univ_of_measure_le_smul mollifier w C hC fun a ↦
    withDensity_le_smul_of_ae_le
      (domainMeasure n Set.univ) (w a) (C a) (hupper a)

end Weighted
end SobolevSpace
