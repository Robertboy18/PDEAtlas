/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.WholeSpaceMultiplier
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceVector
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Bounded multipliers on whole-space vector `L²` fields

An `L∞` coefficient acts on whole-space vector `L²` fields component by component, through the
zeroth-order Sobolev multiplication. On base coordinates it is the `L∞ · L²` product.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ}

/-- Two whole-space vector Sobolev fields with the same base coordinates are equal. -/
theorem VectorH.ext_base {u v : VectorH n k}
    (h : ∀ j, wkpBaseCoordinateCLM (u j) = wkpBaseCoordinateCLM (v j)) : u = v :=
  PiLp.ext fun j ↦ wkpBaseCoordinateCLM_injective isOpen_univ (h j)

/-- Multiplication of a whole-space vector `L²` field by an `L∞` coefficient, component by
component. -/
def vectorMul (n : ℕ) (a : DerivLp n ∞ Set.univ) : VectorH n 0 →L[ℝ] VectorH n 0 :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ↦ wkMultiplication 0 (lpToZeroOrder a))

/-- Each component of the product is the zeroth-order product of the component. -/
@[simp]
theorem vectorMul_apply (a : DerivLp n ∞ Set.univ) (u : VectorH n 0) (j : Fin n) :
    vectorMul n a u j = wkMultiplication 0 (lpToZeroOrder a) (u j) := by
  simp only [vectorMul, ContinuousLinearMap.piLpMap_apply]

/-- On base coordinates the product is the `L∞ · L²` product. -/
theorem wkpBaseCoordinateCLM_vectorMul (a : DerivLp n ∞ Set.univ) (u : VectorH n 0)
    (j : Fin n) : wkpBaseCoordinateCLM (vectorMul n a u j) = a • wkpBaseCoordinateCLM (u j) := by
  rw [vectorMul_apply, wkpBaseCoordinateCLM_wkMultiplication, wkpBaseCoordinateCLM_lpToZeroOrder]
  rfl

end SobolevSpace.GraphSpace
