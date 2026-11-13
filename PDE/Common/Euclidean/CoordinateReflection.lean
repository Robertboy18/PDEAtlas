/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Coordinate reflections in Euclidean space

Reflection in a single coordinate hyperplane, as a linear isometry that preserves the norm,
differences, and Lebesgue measure. Half-space and fluid arguments both use it.

The reflection `R_i` negates coordinate `i` and fixes the others. It is the
symmetry behind the method of images: the Green's function of the half-space
`{x_i > 0}` is obtained by subtracting the fundamental solution at the
reflected pole. For a harmonic function smooth across `{x_i = 0}`, odd symmetry
gives zero boundary values and even symmetry gives zero normal derivative.
Restricting to the half-space then gives the corresponding homogeneous
Dirichlet or Neumann condition. The predicates `IsOddUnderCoordinateReflection`,
`IsEvenUnderCoordinateReflection` and `VanishesOnCoordinateHyperplane` record
the corresponding pointwise symmetry conditions.

## Main results

* `coordinateReflectionLinearIsometryEquiv`, `coordinateReflection`: the
  reflection as a linear isometry equivalence and as a plain function, with the
  coordinate formulas `coordinateReflection_apply_same` and
  `coordinateReflection_apply_of_ne`.
* `coordinateReflection_involutive`, `coordinateReflection_eq_self_iff`: `R_i`
  is an involution whose fixed points are exactly the hyperplane `{x_i = 0}`.
* `norm_coordinateReflection`, `contDiff_coordinateReflection`,
  `measurePreserving_coordinateReflection`: `R_i` preserves the norm, is
  smooth, and preserves Lebesgue measure.
* `isOpen_coordinateUpperHalfSpace`, `closure_coordinateUpperHalfSpace`:
  topology of the half-space `{x_i > 0}`.
* `IsOddUnderCoordinateReflection.vanishesOnCoordinateHyperplane`: an odd
  function vanishes on the reflecting hyperplane.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), the reflection `x̃` in `∂ℝⁿ₊` and Green's
  function for the half-space, pp. 36-37.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


namespace PDE.Common

open Set
open MeasureTheory

/-- Reflection in the coordinate hyperplane `{x | x i = 0}`. -/
def coordinateReflectionLinearIsometryEquiv {n : ℕ} (i : Fin n) :
    ℝ^n ≃ₗᵢ[ℝ] ℝ^n :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j ↦
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

/-- The function underlying reflection in the coordinate hyperplane
`{x | x i = 0}`. -/
def coordinateReflection {n : ℕ} (i : Fin n) (x : ℝ^n) : ℝ^n :=
  coordinateReflectionLinearIsometryEquiv i x

/-- The open half-space on the positive side of the coordinate hyperplane
`{x | x i = 0}`. -/
def coordinateUpperHalfSpace {n : ℕ} (i : Fin n) : Set (ℝ^n) :=
  {x | 0 < x i}

/-- The coordinate hyperplane `{x | x i = 0}`. -/
def coordinateHyperplane {n : ℕ} (i : Fin n) : Set (ℝ^n) :=
  {x | x i = 0}

/-- A real-valued function is odd under reflection in coordinate `i`. -/
def IsOddUnderCoordinateReflection {n : ℕ} (i : Fin n)
    (f : ℝ^n → ℝ) : Prop :=
  ∀ x, f (coordinateReflection i x) = -f x

/-- A real-valued function is even under reflection in coordinate `i`. -/
def IsEvenUnderCoordinateReflection {n : ℕ} (i : Fin n)
    (f : ℝ^n → ℝ) : Prop :=
  ∀ x, f (coordinateReflection i x) = f x

/-- A real-valued function vanishes pointwise on coordinate hyperplane `i`.

This is a classical pointwise condition, not a Sobolev trace statement. -/
def VanishesOnCoordinateHyperplane {n : ℕ} (i : Fin n)
    (f : ℝ^n → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ coordinateHyperplane i → f x = 0

/-- Coordinate reflection negates the selected coordinate. -/
@[simp]
theorem coordinateReflection_apply_same {n : ℕ} (i : Fin n) (x : ℝ^n) :
    coordinateReflection i x i = -x i := by
  simp [coordinateReflection, coordinateReflectionLinearIsometryEquiv]

/-- Coordinate reflection fixes every unselected coordinate. -/
@[simp]
theorem coordinateReflection_apply_of_ne {n : ℕ} (i j : Fin n) (hji : j ≠ i)
    (x : ℝ^n) :
    coordinateReflection i x j = x j := by
  simp [coordinateReflection, coordinateReflectionLinearIsometryEquiv, hji]

/-- Reflecting the coordinate vector normal to the hyperplane negates it. -/
@[simp]
theorem coordinateReflection_single_same {n : ℕ} (i : Fin n) (c : ℝ) :
    coordinateReflection i (EuclideanSpace.single i c) =
      EuclideanSpace.single i (-c) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- Reflection in coordinate `i` fixes a coordinate vector in any distinct
direction `j`. -/
@[simp]
theorem coordinateReflection_single_of_ne {n : ℕ} (i j : Fin n)
    (hji : j ≠ i) (c : ℝ) :
    coordinateReflection i (EuclideanSpace.single j c) =
      EuclideanSpace.single j c := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [hji]
  · simp [coordinateReflection_apply_of_ne i k hki]

/-- A coordinate reflection is an involution. -/
theorem coordinateReflection_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (coordinateReflection i) := by
  intro x
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [coordinateReflection_apply_of_ne i j hji]

/-- A coordinate reflection fixes precisely its reflecting hyperplane. -/
theorem coordinateReflection_eq_self_iff {n : ℕ} (i : Fin n) (x : ℝ^n) :
    coordinateReflection i x = x ↔ x ∈ coordinateHyperplane i := by
  constructor
  · intro h
    have hi := congrArg (fun y : ℝ^n ↦ y i) h
    simp [coordinateHyperplane] at hi ⊢
    linarith
  · intro hx
    ext j
    by_cases hji : j = i
    · subst j
      rw [coordinateReflection_apply_same]
      change x i = 0 at hx
      simp [hx]
    · exact coordinateReflection_apply_of_ne i j hji x

/-- Reflection in one coordinate preserves a half-space defined by a
different coordinate. -/
theorem coordinateReflection_mem_coordinateUpperHalfSpace_iff_of_ne
    {n : ℕ} (i j : Fin n) (hji : j ≠ i) (x : ℝ^n) :
    coordinateReflection i x ∈ coordinateUpperHalfSpace j ↔
      x ∈ coordinateUpperHalfSpace j := by
  simp [coordinateUpperHalfSpace, coordinateReflection_apply_of_ne i j hji]

/-- A coordinate upper half-space is open. -/
theorem isOpen_coordinateUpperHalfSpace {n : ℕ} (i : Fin n) :
    IsOpen (coordinateUpperHalfSpace i) := by
  change IsOpen ((EuclideanSpace.proj i) ⁻¹' Set.Ioi 0)
  exact isOpen_Ioi.preimage (EuclideanSpace.proj i).continuous

/-- The closure of a coordinate upper half-space is the corresponding closed
half-space. -/
theorem closure_coordinateUpperHalfSpace {n : ℕ} (i : Fin n) :
    closure (coordinateUpperHalfSpace i) = {x : ℝ^n | 0 ≤ x i} := by
  change closure ((fun x : ℝ^n ↦ x i) ⁻¹' Set.Ioi 0) =
    (fun x : ℝ^n ↦ x i) ⁻¹' Set.Ici 0
  rw [← (PiLp.isOpenMap_apply (p := (2 : ENNReal))
      (β := fun _ : Fin n ↦ ℝ) i).preimage_closure_eq_closure_preimage
        (PiLp.continuous_apply (p := (2 : ENNReal))
          (β := fun _ : Fin n ↦ ℝ) i) (Set.Ioi 0)]
  rw [closure_Ioi]

/-- An odd function vanishes at every point fixed by the reflection. -/
theorem IsOddUnderCoordinateReflection.vanishesOnCoordinateHyperplane
    {n : ℕ} {i : Fin n} {f : ℝ^n → ℝ}
    (hf : IsOddUnderCoordinateReflection i f) :
    VanishesOnCoordinateHyperplane i f := by
  intro x hx
  have hfixed : coordinateReflection i x = x :=
    (coordinateReflection_eq_self_iff i x).2 hx
  have hodd := hf x
  rw [hfixed] at hodd
  linarith

/-- A coordinate reflection maps a point to zero exactly when the point is
zero. -/
@[simp]
theorem coordinateReflection_eq_zero_iff {n : ℕ} (i : Fin n) (x : ℝ^n) :
    coordinateReflection i x = 0 ↔ x = 0 := by
  exact (coordinateReflectionLinearIsometryEquiv i).map_eq_zero_iff

/-- Coordinate reflection preserves subtraction. -/
theorem coordinateReflection_sub {n : ℕ} (i : Fin n) (x y : ℝ^n) :
    coordinateReflection i (x - y) =
      coordinateReflection i x - coordinateReflection i y := by
  exact (coordinateReflectionLinearIsometryEquiv i).map_sub x y

/-- Coordinate reflection preserves the Euclidean norm. -/
theorem norm_coordinateReflection {n : ℕ} (i : Fin n) (x : ℝ^n) :
    ‖coordinateReflection i x‖ = ‖x‖ := by
  exact (coordinateReflectionLinearIsometryEquiv i).norm_map x

/-- Coordinate reflection is smooth to every requested finite or infinite
order. -/
theorem contDiff_coordinateReflection {n : ℕ} (i : Fin n) (m : ℕ∞) :
    ContDiff ℝ m (coordinateReflection i : ℝ^n → ℝ^n) := by
  exact
    (coordinateReflectionLinearIsometryEquiv i).toContinuousLinearEquiv
      |>.toContinuousLinearMap.contDiff

/-- Coordinate reflection preserves Lebesgue measure. -/
theorem measurePreserving_coordinateReflection {n : ℕ} (i : Fin n) :
    MeasurePreserving (coordinateReflection i : ℝ^n → ℝ^n)
      (volume : Measure (ℝ^n)) (volume : Measure (ℝ^n)) :=
  LinearIsometryEquiv.measurePreserving (coordinateReflectionLinearIsometryEquiv i)

end PDE.Common
