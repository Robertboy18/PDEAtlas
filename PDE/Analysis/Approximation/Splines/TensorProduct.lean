/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.NormalizedBasis
public import PDE.Common.Euclidean
import Mathlib.Tactic.Positivity.Finset

/-!
# Tensor products of normalized positive bases

Tensor-product spline profiles on a rectangle are built from two finite
one-dimensional bases.  Positivity and partition of unity are preserved by
the tensor product, so coefficient enclosures remain pointwise enclosures in
two dimensions.

The construction is stated first for arbitrary carrier types, then pulled back
to the radial and axial coordinates of the meridian plane.  In particular,
using `clampedSinglePanelNormalizedBasis` in both coordinates gives a
rectangular tensor-product B-spline basis.

References:

* C. de Boor, *A Practical Guide to Splines*, revised edition, Springer, 2001.
* L. L. Schumaker, *Spline Functions: Basic Theory*, third edition,
  Cambridge University Press, 2007.
-/

@[expose] public section

noncomputable section

namespace CAS.Splines

open Set
open scoped BigOperators


namespace NormalizedPositiveBasis

variable {X Y : Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Pull a normalized positive basis back along a map. -/
def pullback (B : NormalizedPositiveBasis Y ι) (f : X → Y) :
    NormalizedPositiveBasis X ι where
  carrier := f ⁻¹' B.carrier
  basis := fun i x ↦ B.basis i (f x)
  nonneg_on := fun i x hx ↦ B.nonneg_on i (f x) hx
  sum_eq_one_on := fun x hx ↦ B.sum_eq_one_on (f x) hx

/-- The tensor product of two normalized positive bases. -/
def prod (B : NormalizedPositiveBasis X ι)
    (C : NormalizedPositiveBasis Y κ) :
    NormalizedPositiveBasis (X × Y) (ι × κ) where
  carrier := B.carrier ×ˢ C.carrier
  basis := fun ij xy ↦ B.basis ij.1 xy.1 * C.basis ij.2 xy.2
  nonneg_on := fun ij xy hxy ↦
    mul_nonneg
      (B.nonneg_on ij.1 xy.1 hxy.1)
      (C.nonneg_on ij.2 xy.2 hxy.2)
  sum_eq_one_on := by
    intro xy hxy
    classical
    rw [Fintype.sum_prod_type]
    calc
      (∑ i, ∑ j, B.basis i xy.1 * C.basis j xy.2) =
          ∑ i, B.basis i xy.1 * ∑ j, C.basis j xy.2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ i, B.basis i xy.1 * 1 := by
        rw [C.sum_eq_one_on xy.2 hxy.2]
      _ = ∑ i, B.basis i xy.1 := by simp
      _ = 1 := B.sum_eq_one_on xy.1 hxy.1

end NormalizedPositiveBasis

/-- Radial and axial coordinates of a point in the meridian plane. -/
def meridianCoordinates (x : ℝ^2) : ℝ × ℝ :=
  (x (0 : Fin 2), x (1 : Fin 2))

/-- Tensor product of radial and axial normalized positive bases on the
meridian plane. -/
def meridianTensorProduct
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (radial : NormalizedPositiveBasis ℝ ι)
    (axial : NormalizedPositiveBasis ℝ κ) :
    NormalizedPositiveBasis (ℝ^2) (ι × κ) :=
  (radial.prod axial).pullback meridianCoordinates

/-- Meridian tensor product formed directly from two finite Cox–de Boor
partition certificates. -/
def finiteCoxDeBoorMeridianTensorProduct
    {radialKnots axialKnots : KnotSequence}
    {radialDegree radialCount axialDegree axialCount : ℕ}
    (radial :
      FiniteCoxDeBoorPartition
        radialKnots radialDegree radialCount)
    (axial :
      FiniteCoxDeBoorPartition
        axialKnots axialDegree axialCount) :
    NormalizedPositiveBasis (ℝ^2)
      (Fin radialCount × Fin axialCount) :=
  meridianTensorProduct
    radial.toNormalizedPositiveBasis
    axial.toNormalizedPositiveBasis

/-- Membership in a finite Cox–de Boor meridian tensor carrier is
coordinatewise. -/
@[simp]
theorem mem_finiteCoxDeBoorMeridianTensorProduct_carrier
    {radialKnots axialKnots : KnotSequence}
    {radialDegree radialCount axialDegree axialCount : ℕ}
    (radial :
      FiniteCoxDeBoorPartition
        radialKnots radialDegree radialCount)
    (axial :
      FiniteCoxDeBoorPartition
        axialKnots axialDegree axialCount)
    (x : ℝ^2) :
    x ∈ (finiteCoxDeBoorMeridianTensorProduct radial axial).carrier ↔
      x (0 : Fin 2) ∈ radial.carrier ∧
        x (1 : Fin 2) ∈ axial.carrier :=
  Iff.rfl

/-- A finite Cox–de Boor meridian tensor basis function is the product of
its radial and axial factors. -/
@[simp]
theorem finiteCoxDeBoorMeridianTensorProduct_basis
    {radialKnots axialKnots : KnotSequence}
    {radialDegree radialCount axialDegree axialCount : ℕ}
    (radial :
      FiniteCoxDeBoorPartition
        radialKnots radialDegree radialCount)
    (axial :
      FiniteCoxDeBoorPartition
        axialKnots axialDegree axialCount)
    (index : Fin radialCount × Fin axialCount) (x : ℝ^2) :
    (finiteCoxDeBoorMeridianTensorProduct radial axial).basis index x =
      finiteCoxDeBoorBasis radialKnots radialDegree radialCount
          index.1 (x (0 : Fin 2)) *
        finiteCoxDeBoorBasis axialKnots axialDegree axialCount
          index.2 (x (1 : Fin 2)) :=
  rfl

/-- Membership in the meridian tensor-product carrier is coordinatewise. -/
@[simp]
theorem mem_meridianTensorProduct_carrier
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (radial : NormalizedPositiveBasis ℝ ι)
    (axial : NormalizedPositiveBasis ℝ κ) (x : ℝ^2) :
    x ∈ (meridianTensorProduct radial axial).carrier ↔
      x (0 : Fin 2) ∈ radial.carrier ∧
        x (1 : Fin 2) ∈ axial.carrier :=
  Iff.rfl

/-- A meridian tensor-product basis function is the product of its radial and
axial factors. -/
@[simp]
theorem meridianTensorProduct_basis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (radial : NormalizedPositiveBasis ℝ ι)
    (axial : NormalizedPositiveBasis ℝ κ)
    (index : ι × κ) (x : ℝ^2) :
    (meridianTensorProduct radial axial).basis index x =
      radial.basis index.1 (x (0 : Fin 2)) *
        axial.basis index.2 (x (1 : Fin 2)) :=
  rfl

/-- Tensor-product expansion in radial and axial normalized bases. -/
def meridianTensorExpansion
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (radial : NormalizedPositiveBasis ℝ ι)
    (axial : NormalizedPositiveBasis ℝ κ)
    (coefficient : ι × κ → ℝ) (x : ℝ^2) : ℝ :=
  (meridianTensorProduct radial axial).expansion coefficient x

/-- Uniform tensor coefficients bound the meridian expansion pointwise. -/
theorem abs_meridianTensorExpansion_le
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (radial : NormalizedPositiveBasis ℝ ι)
    (axial : NormalizedPositiveBasis ℝ κ)
    {coefficient : ι × κ → ℝ} {bound : ℝ} {x : ℝ^2}
    (hcoefficient : ∀ index, |coefficient index| ≤ bound)
    (hx :
      x (0 : Fin 2) ∈ radial.carrier ∧
        x (1 : Fin 2) ∈ axial.carrier) :
    |meridianTensorExpansion radial axial coefficient x| ≤ bound :=
  (meridianTensorProduct radial axial).abs_expansion_le
    hcoefficient hx

end CAS.Splines
