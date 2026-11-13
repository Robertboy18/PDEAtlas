/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Normed.Operator.FiniteProduct
public import PDE.Spaces.Sobolev.Calculus.Pullback.Dilation.HigherOrder
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ZeroOrder

/-!
# Whole-space vector Sobolev fields

A vector field on `ℝⁿ` with components in `W^{k,2}(ℝⁿ)` carries the finite Hilbert
product norm, the square root of the sum of the squared component norms. Each
derivative index assembles the corresponding weak derivatives of the components into
one Euclidean-valued `L²` field, and spatial dilation acts component by component. At order
zero the base coordinates identify vector fields isometrically with the finite Hilbert product
of scalar `L²` spaces, which carries an inner product.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace
open scoped Sobolev

namespace SobolevSpace.GraphSpace

/-- Whole-space vector Sobolev fields with the sum-of-squares component norm. -/
abbrev VectorH (n k : ℕ) := PiLp 2 (fun _ : Fin n ↦ W^{k,2}(ℝ^n))

/-- The real normed space structure of the finite Hilbert product. -/
instance VectorH.instNormedSpace (n k : ℕ) : NormedSpace ℝ (VectorH n k) :=
  PiLp.normedSpace 2 ℝ (fun _ : Fin n ↦ W^{k,2}(ℝ^n))

/-- The operator norm between vector Sobolev spaces. Instance search does not reach
`ContinuousLinearMap.toNormedAddCommGroup` through the product instances of `VectorH`, so the
instance is given directly. -/
instance VectorH.instNormedAddCommGroupContinuousLinearMap (n k m p : ℕ) :
    NormedAddCommGroup (VectorH n k →L[ℝ] VectorH m p) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The normed space of operators between vector Sobolev spaces. -/
instance VectorH.instNormedSpaceContinuousLinearMap (n k m p : ℕ) :
    NormedSpace ℝ (VectorH n k →L[ℝ] VectorH m p) :=
  ContinuousLinearMap.toNormedSpace

variable {n k : ℕ}

/-- Assemble one whole-space vector derivative row. -/
def l2SobolevRow (a : DerivIndex n k) :
    VectorH n k →L[ℝ] Lp (ℝ^n) 2 (domainMeasure n Set.univ) :=
  Lp.euclideanTuple.comp (ContinuousLinearMap.pi fun j : Fin n ↦
    (wkpCoordinateCLM a).comp (PiLp.proj 2 (fun _ : Fin n ↦ W^{k,2}(ℝ^n)) j))

/-- The vector row is the Euclidean assembly of scalar graph coordinates. -/
@[simp]
theorem l2SobolevRow_apply (a : DerivIndex n k) (U : VectorH n k) :
    l2SobolevRow a U = Lp.euclideanTuple (fun j ↦ wkpCoordinateCLM a (U j)) :=
  rfl

/-- Vector fields of order zero are the finite Hilbert product of scalar `L²` spaces,
component by component through `lpEquivZeroOrder`. The product carries the inner product that
`VectorH n 0` does not. -/
def vectorLpEquivZeroOrder (n : ℕ) :
    PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 Set.univ) ≃ₗᵢ[ℝ] VectorH n 0 :=
  LinearIsometryEquiv.piLpCongrRight 2 fun _ ↦ lpEquivZeroOrder

@[simp]
theorem vectorLpEquivZeroOrder_apply (f : PiLp 2 (fun _ : Fin n ↦ DerivLp n 2 Set.univ))
    (j : Fin n) : vectorLpEquivZeroOrder n f j = lpToZeroOrder (f j) :=
  rfl

/-- The inverse of the zero-order identification takes the base coordinate of each
component. -/
@[simp]
theorem vectorLpEquivZeroOrder_symm_apply (u : VectorH n 0) (j : Fin n) :
    (vectorLpEquivZeroOrder n).symm u j = wkpBaseCoordinateCLM (u j) :=
  rfl

/-- Spatial dilation on vector Sobolev graphs, component by component. -/
def vectorDilation (n k : ℕ) (a : ℝ) (ha : a ≠ 0) :
    VectorH n k →L[ℝ] VectorH n k :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ↦ dilationWkpCLM (by norm_num) a ha)

/-- Each component of a dilated vector field is the dilated component. -/
@[simp]
theorem vectorDilation_apply (a : ℝ) (ha : a ≠ 0) (u : VectorH n k) (j : Fin n) :
    vectorDilation n k a ha u j = dilationWkpCLM (by norm_num) a ha (u j) := by
  simp only [vectorDilation, ContinuousLinearMap.piLpMap_apply]

end SobolevSpace.GraphSpace
