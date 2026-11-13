/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Constraints.Determinant.Existence
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ContinuousRepresentative
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A nonaffine volume-preserving shear on the three-dimensional ball

The polynomial map `(x₀ + x₁², x₁, x₂)` is a Sobolev map at every finite
exponent. Its weak derivative has determinant one, and its boundary trace is
the polynomial itself. It is the admissible competitor for the constrained
minimizer examples.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary.Atlas.UnitBall
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Matrix.Norms.Elementwise Sobolev

namespace PDE.Examples.Constraints.Determinant

/-- A polynomial shear with nonconstant derivative. -/
def shear (x : ℝ^3) : ℝ^3 := WithLp.toLp 2 ![x 0 + x 1 ^ 2, x 1, x 2]

/-- Each component is smooth. -/
theorem shear_component_contDiff (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ shear x i) := by
  fin_cases i <;>
    simp only [shear, PiLp.toLp_apply, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    cas

/-- The Jacobian matrix of the shear is `!![1, 2x₁, 0; 0, 1, 0; 0, 0, 1]`. -/
theorem shear_partial (i j : Fin 3) (x : ℝ^3) :
    iteratedPartialDeriv [j] (fun y ↦ shear y i) x =
      (!![(1 : ℝ), 2 * x 1, 0; 0, 1, 0; 0, 0, 1]) i j := by
  fin_cases i <;> fin_cases j <;>
    simp only [shear, PiLp.toLp_apply, Matrix.cons_val_zero', Matrix.cons_val_succ',
      iteratedPartialDeriv, Matrix.of_apply] <;>
    cas

/-- The variable triangular derivative has determinant exactly one. -/
theorem shear_derivative_det (x : ℝ^3) :
    (!![(1 : ℝ), 2 * x 1, 0; 0, 1, 0; 0, 0, 1]).det = 1 := by
  rw [Matrix.det_fin_three]
  cas

/-- The nonlinear second derivative is nonzero. -/
theorem shear_second_partial (x : ℝ^3) :
    iteratedPartialDeriv [1, 1] (fun y ↦ shear y 0) x = 2 := by
  change iteratedPartialDeriv [1, 1] (fun y : ℝ^3 ↦ y 0 + y 1 ^ 2) x = 2
  dsimp only [iteratedPartialDeriv]
  cas

/-- Every partial derivative of a shear component is in `Lp` on the ball. -/
theorem shear_row_memLp (p : ℝ≥0∞) (i : Fin 3) (a : DerivIndex 3 1) :
    MemLp (iteratedPartialDeriv a.toList (fun x ↦ shear x i)) p
      (domainMeasure 3 (domain 3)) := by
  let := isFiniteMeasure_domainMeasure_of_isBounded (bounded_domain 3)
  exact (WeakChangeOfVariables.memLp_top_on_bounded_of_continuous (bounded_domain 3)
    (contDiff_top_iteratedPartialDeriv (shear_component_contDiff i)
      a.toList).continuous).mono_exponent le_top

/-- The shear as a map in `W^{1,p}` on the ball, component by component. -/
def shearData (p : ℝ≥0∞) : Fin 3 → W^{1,p}(domain 3) :=
  fun i ↦ mkWkpSpaceOnOfContDiffMemLp (fun x ↦ shear x i)
    (shear_component_contDiff i) (shear_row_memLp p i)

/-- The Sobolev field is represented by the shear almost everywhere. -/
theorem shearData_base_ae (p : ℝ≥0∞) (i : Fin 3) :
    baseRepresentative (shearData p i) =ᵐ[domainMeasure 3 (domain 3)] fun x ↦ shear x i := by
  simpa only [shearData, baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
    mkWkpSpaceOnOfContDiffMemLp_apply_ae (fun x ↦ shear x i)
      (shear_component_contDiff i) (shear_row_memLp p i) (baseIndex 3 1)

/-- Every weak derivative coordinate equals the classical derivative. -/
theorem shearData_derivative_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∀ᵐ x ∂domainMeasure 3 (domain 3), ∀ i j : Fin 3,
      wkpCoordinateCLM (singleDerivIndex 3 j) (shearData p i) x =
        (!![(1 : ℝ), 2 * x 1, 0; 0, 1, 0; 0, 0, 1]) i j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  have hrow := mkWkpSpaceOnOfContDiffMemLp_apply_ae (fun x ↦ shear x i)
    (shear_component_contDiff i) (shear_row_memLp p i) (singleDerivIndex 3 j)
  filter_upwards [hrow] with x hx
  simpa only [wkpCoordinateCLM_apply, shearData, singleDerivIndex_toList, shear_partial] using hx

/-- The weak Jacobian determinant equals one almost everywhere. -/
theorem shearData_det_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∀ᵐ x ∂domainMeasure 3 (domain 3),
      (Matrix.of fun i j ↦ wkpCoordinateCLM (singleDerivIndex 3 j) (shearData p i) x).det = 1 := by
  filter_upwards [shearData_derivative_ae p] with x hx
  have he : (Matrix.of fun i j ↦ wkpCoordinateCLM (singleDerivIndex 3 j) (shearData p i) x) =
      !![(1 : ℝ), 2 * x 1, 0; 0, 1, 0; 0, 0, 1] := Matrix.ext hx
  rw [he, shear_derivative_det]

/-- Unflattening the weak gradient gives the classical derivative matrix. -/
theorem shearData_gradient_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∀ᵐ x ∂domainMeasure 3 (domain 3),
      Matrix.euclideanEquiv.symm (∇ (shearData p) x) =
        !![(1 : ℝ), 2 * x 1, 0; 0, 1, 0; 0, 0, 1] := by
  have hgrad := ae_all_iff.mpr fun i ↦ wkpGradientCLM_apply_ae (shearData p i)
  filter_upwards [vectorWkpGradientCLM_apply_ae (shearData p), hgrad, shearData_derivative_ae p]
    with x hx hy hz
  ext i j
  rw [Matrix.euclideanEquiv_symm_apply, hx i j, hy i j]
  simpa only [wkpCoordinateCLM_apply] using hz i j

/-- On the ball, the geometric trace of the Sobolev field is the shear. -/
theorem shearData_trace (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] :
    letI : Boundary.C1ExtensionAtlas 3 (domain 3) :=
      ((hasContDiffGraphBoundary 3 1).hasC1GraphBoundary le_rfl).c1ExtensionAtlas
        (isOpen_domain 3) (bounded_domain 3)
    (Trace.C1.vectorTraceLp q (shearData (ENNReal.ofReal q)) : ℝ^3 → ℝ^3)
      =ᵐ[surfaceMeasure (domain 3)] shear := by
  let : Boundary.C1ExtensionAtlas 3 (domain 3) :=
    ((hasContDiffGraphBoundary 3 1).hasC1GraphBoundary le_rfl).c1ExtensionAtlas
      (isOpen_domain 3) (bounded_domain 3)
  have hcoord : ∀ᵐ x ∂surfaceMeasure (domain 3), ∀ i : Fin 3,
      Trace.C1.traceLp q (shearData (ENNReal.ofReal q) i) x = shear x i := by
    apply ae_all_iff.mpr
    intro i
    exact Trace.C1.traceLp_eq_ae_of_continuousOn_of_local_graph (isOpen_domain 3)
      (bounded_domain 3) ((hasContDiffGraphBoundary 3 1).hasC1GraphBoundary le_rfl) q
      (shearData (ENNReal.ofReal q) i) (shear_component_contDiff i).continuous.continuousOn
      (shearData_base_ae (ENNReal.ofReal q) i)
  filter_upwards [Lp.euclideanTuple_apply_ae
    (fun i ↦ Trace.C1.traceLp q (shearData (ENNReal.ofReal q) i)), hcoord] with x hx hy
  exact PiLp.ext fun i ↦ (hx i).trans (hy i)

end PDE.Examples.Constraints.Determinant
