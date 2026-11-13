/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.CalculusOfVariations.Polyconvexity.Existence.Density
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ContinuousRepresentative
public import PDE.Spaces.Sobolev.Approximation.Density.Constructors
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A nonzero affine trace and its Sobolev gradient

On the two-dimensional unit ball, `g(x) = (x₀ + 1, 2x₁ - 1)` belongs to every
finite Sobolev exponent. Its weak derivative matrix is `diag(1,2)`, its
geometric trace is the affine map itself, and the quartic energy density equals
twenty-six. The map is the admissible competitor of `exists_quartic_affine_minimizer`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary.Atlas.UnitBall
open SobolevSpace.Boundary.Geometry.SurfaceMeasure
open PDE.CalculusOfVariations
open scoped ENNReal Matrix.Norms.Elementwise Sobolev

namespace PDE.Examples.Polyconvexity.Existence

/-- Nonzero affine boundary data with two different diagonal derivatives. -/
def affineMap (x : ℝ^2) : ℝ^2 := WithLp.toLp 2 ![x 0 + 1, 2 * x 1 - 1]

/-- Each component of `affineMap` is smooth. -/
theorem affineMap_component_contDiff (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ affineMap x i) := by
  fin_cases i <;> dsimp [affineMap] <;> cas

/-- The Jacobian matrix of `affineMap` is `diag(1, 2)`. -/
theorem affineMap_partial (i j : Fin 2) (x : ℝ^2) :
    iteratedPartialDeriv [j] (fun y ↦ affineMap y i) x = (!![(1 : ℝ), 0; 0, 2]) i j := by
  fin_cases i <;> fin_cases j <;> dsimp [affineMap, iteratedPartialDeriv] <;> cas

/-- Every partial derivative of a component of `affineMap` is in `Lp` on the disk. -/
theorem affineMap_row_memLp (p : ℝ≥0∞) (i : Fin 2) (a : DerivIndex 2 1) :
    MemLp (iteratedPartialDeriv a.toList (fun x ↦ affineMap x i)) p
      (domainMeasure 2 (domain 2)) := by
  let := isFiniteMeasure_domainMeasure_of_isBounded (bounded_domain 2)
  exact (WeakChangeOfVariables.memLp_top_on_bounded_of_continuous (bounded_domain 2)
    (contDiff_top_iteratedPartialDeriv (affineMap_component_contDiff i)
      a.toList).continuous).mono_exponent le_top

/-- The affine map as a Sobolev field. -/
def affineData (p : ℝ≥0∞) : Fin 2 → W^{1,p}(domain 2) :=
  fun i ↦ mkWkpSpaceOnOfContDiffMemLp (fun x ↦ affineMap x i)
    (affineMap_component_contDiff i) (affineMap_row_memLp p i)

/-- The Sobolev field is represented by the affine map almost everywhere. -/
theorem affineData_base_ae (p : ℝ≥0∞) (i : Fin 2) :
    baseRepresentative (affineData p i) =ᵐ[domainMeasure 2 (domain 2)]
      fun x ↦ affineMap x i := by
  simpa only [affineData, baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
    mkWkpSpaceOnOfContDiffMemLp_apply_ae (fun x ↦ affineMap x i)
      (affineMap_component_contDiff i) (affineMap_row_memLp p i) (baseIndex 2 1)

/-- Unflattening the weak gradient gives the constant matrix `diag(1,2)`. -/
theorem affineData_gradient_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∀ᵐ x ∂domainMeasure 2 (domain 2),
      Matrix.euclideanEquiv.symm (∇ (affineData p) x) =
        !![(1 : ℝ), 0; 0, 2] := by
  have hrows : ∀ᵐ x ∂domainMeasure 2 (domain 2), ∀ i j : Fin 2,
      (affineData p i).val (singleDerivIndex 2 j) x =
        (!![(1 : ℝ), 0; 0, 2]) i j := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    have hrow := mkWkpSpaceOnOfContDiffMemLp_apply_ae (fun x ↦ affineMap x i)
      (affineMap_component_contDiff i) (affineMap_row_memLp p i) (singleDerivIndex 2 j)
    filter_upwards [hrow] with x hx
    simpa only [affineData, singleDerivIndex_toList, affineMap_partial] using hx
  have hgrad := ae_all_iff.mpr fun i ↦ wkpGradientCLM_apply_ae (affineData p i)
  filter_upwards [vectorWkpGradientCLM_apply_ae (affineData p), hgrad, hrows]
    with x hx hy hz
  ext i j
  rw [Matrix.euclideanEquiv_symm_apply, hx i j, hy i j, hz i j]

/-- On the ball, the geometric trace of the Sobolev field is the affine map. -/
theorem affineData_trace (q : ℝ) [Fact (1 ≤ ENNReal.ofReal q)] :
    letI : Boundary.C1ExtensionAtlas 2 (domain 2) :=
      ((hasContDiffGraphBoundary 2 1).hasC1GraphBoundary le_rfl).c1ExtensionAtlas
        (isOpen_domain 2) (bounded_domain 2)
    (Trace.C1.vectorTraceLp q (affineData (ENNReal.ofReal q)) : ℝ^2 → ℝ^2)
      =ᵐ[surfaceMeasure (domain 2)] affineMap := by
  let : Boundary.C1ExtensionAtlas 2 (domain 2) :=
    ((hasContDiffGraphBoundary 2 1).hasC1GraphBoundary le_rfl).c1ExtensionAtlas
      (isOpen_domain 2) (bounded_domain 2)
  have hcoord : ∀ᵐ x ∂surfaceMeasure (domain 2), ∀ i : Fin 2,
      Trace.C1.traceLp q (affineData (ENNReal.ofReal q) i) x = affineMap x i := by
    apply ae_all_iff.mpr
    intro i
    exact Trace.C1.traceLp_eq_ae_of_continuousOn_of_local_graph (isOpen_domain 2)
      (bounded_domain 2) ((hasContDiffGraphBoundary 2 1).hasC1GraphBoundary le_rfl) q
      (affineData (ENNReal.ofReal q) i) (affineMap_component_contDiff i).continuous.continuousOn
      (affineData_base_ae (ENNReal.ofReal q) i)
  filter_upwards [Lp.euclideanTuple_apply_ae
    (fun i ↦ Trace.C1.traceLp q (affineData (ENNReal.ofReal q) i)), hcoord] with x hx hy
  exact PiLp.ext fun i ↦ (hx i).trans (hy i)

/-- The quartic determinant density along `affineData` equals `26` almost everywhere. -/
theorem quarticDensity_affineData_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (fun x ↦ determinantDensity quarticDensity x
      (vectorWkpValueCLM (affineData p) x, ∇ (affineData p) x))
        =ᵐ[domainMeasure 2 (domain 2)] fun _ ↦ (26 : ℝ) := by
  filter_upwards [affineData_gradient_ae p] with x hx
  simp only [determinantDensity, hx, Matrix.det_fin_two]
  dsimp [quarticDensity, quarticPolynomial]
  cas

end PDE.Examples.Polyconvexity.Existence
