/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Globally represented graph-flattening charts

The triangular maps preserve tangential coordinates and replace the last coordinate by
`g(x') - xₙ` or `g(x') + xₙ`. They identify the appropriate side of a graph with the upper
half-space. A globally `C^m` height gives globally `C^m` maps and inverses. Restriction to
an open source yields a local chart, with bounded target whenever the source is bounded.

The height is a function on the full Euclidean space; each map evaluates it after setting
the normal coordinate to zero. The graph maps therefore depend only on its restriction to
the tangential hyperplane.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Extension.GraphChart

open Metric Set
open PDE.Common
open SobolevSpace.HalfSpace (boundaryProjection boundaryProjection_apply_last
  boundaryProjection_apply_of_ne_last boundaryProjection_idempotent contDiff_boundaryProjection)

variable (n : ℕ)

section PositiveDimension

variable [Fact (0 < n)]

/-- Positive-side triangular flattening:
`yₙ = g(x') - xₙ`.  It is its own inverse. -/
def positiveMap (g : ℝ^n → ℝ) (x : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 fun i ↦
    if i = lastIndex (n := n) then g (boundaryProjection n x) - x (lastIndex (n := n)) else x i

/-- Formula for the normal coordinate of the positive-side flattening map. -/
@[simp]
theorem positiveMap_apply_normal (g : ℝ^n → ℝ) (x : ℝ^n) :
    positiveMap n g x (lastIndex (n := n)) =
      g (boundaryProjection n x) - x (lastIndex (n := n)) := by
  simp [positiveMap]

/-- The positive-side flattening map preserves every tangential coordinate. -/
@[simp]
theorem positiveMap_apply_of_ne (g : ℝ^n → ℝ) (x : ℝ^n) {i : Fin n}
    (hi : i ≠ lastIndex (n := n)) :
    positiveMap n g x i = x i := by
  simp [positiveMap, hi]

/-- Positive-side flattening does not change the tangential projection. -/
@[simp]
theorem boundaryProjection_positiveMap (g : ℝ^n → ℝ) (x : ℝ^n) :
    boundaryProjection n (positiveMap n g x) = boundaryProjection n x := by
  ext i
  by_cases hi : i = lastIndex (n := n)
  · subst i
    simp
  · simp [boundaryProjection_apply_of_ne_last, positiveMap_apply_of_ne, hi]

/-- The positive-side triangular flattening map is its own inverse. -/
theorem positiveMap_involutive (g : ℝ^n → ℝ) :
    Function.Involutive (positiveMap n g) := by
  intro x
  ext i
  by_cases hi : i = lastIndex (n := n)
  · subst i
    simp
  · simp [positiveMap_apply_of_ne, hi]

/-- A `C^m` graph height induces a `C^m` positive-side flattening map. -/
theorem positiveMap_contDiff (m : ℕ∞) {g : ℝ^n → ℝ}
    (hg : ContDiff ℝ m g) :
    ContDiff ℝ m (positiveMap n g) := by
  rw [show positiveMap n g =
      (EuclideanSpace.equiv (Fin n) ℝ).symm ∘
        (fun x : ℝ^n ↦ fun i ↦
          if i = lastIndex (n := n) then
            g (boundaryProjection n x) - x (lastIndex (n := n))
          else x i) by
    funext x
    rfl]
  refine (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.comp (contDiff_pi' fun i ↦ ?_)
  by_cases hi : i = lastIndex (n := n)
  · subst i
    simpa using
      (hg.comp (contDiff_boundaryProjection n m)).sub
        (EuclideanSpace.proj (𝕜 := ℝ) (lastIndex (n := n))).contDiff
  · simpa [hi] using (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

/-- The positive-side flattening as a global homeomorphism. -/
def positiveHomeomorph (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) :
    ℝ^n ≃ₜ ℝ^n where
  toEquiv :=
    { toFun := positiveMap n g
      invFun := positiveMap n g
      left_inv := positiveMap_involutive n g
      right_inv := positiveMap_involutive n g }
  continuous_toFun :=
    (positiveMap_contDiff n 1 hg).continuous
  continuous_invFun :=
    (positiveMap_contDiff n 1 hg).continuous

/-- A point lies below the positive graph precisely when its flattened
image lies in the upper half-space. -/
theorem positiveMap_mem_upper_iff (g : ℝ^n → ℝ) (x : ℝ^n) :
    positiveMap n g x ∈ SobolevSpace.HalfSpace.upper n ↔
      x (lastIndex (n := n)) < g (boundaryProjection n x) := by
  change 0 < positiveMap n g x (lastIndex (n := n)) ↔
    x (lastIndex (n := n)) < g (boundaryProjection n x)
  rw [positiveMap_apply_normal]
  exact sub_pos

/-- Negative-side triangular flattening:
`yₙ = g(x') + xₙ`. -/
def negativeMap (g : ℝ^n → ℝ) (x : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 fun i ↦
    if i = lastIndex (n := n) then g (boundaryProjection n x) + x (lastIndex (n := n)) else x i

/-- Inverse of `negativeMap`: `xₙ = yₙ - g(y')`. -/
def negativeMapInverse (g : ℝ^n → ℝ) (y : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 fun i ↦
    if i = lastIndex (n := n) then y (lastIndex (n := n)) - g (boundaryProjection n y) else y i

/-- Formula for the normal coordinate of the negative-side flattening map. -/
@[simp]
theorem negativeMap_apply_normal (g : ℝ^n → ℝ) (x : ℝ^n) :
    negativeMap n g x (lastIndex (n := n)) =
      g (boundaryProjection n x) + x (lastIndex (n := n)) := by
  simp [negativeMap]

/-- Formula for the normal coordinate of the inverse negative-side map. -/
@[simp]
theorem negativeMapInverse_apply_normal (g : ℝ^n → ℝ) (y : ℝ^n) :
    negativeMapInverse n g y (lastIndex (n := n)) =
      y (lastIndex (n := n)) - g (boundaryProjection n y) := by
  simp [negativeMapInverse]

/-- The negative-side flattening map preserves every tangential coordinate. -/
@[simp]
theorem negativeMap_apply_of_ne (g : ℝ^n → ℝ) (x : ℝ^n) {i : Fin n}
    (hi : i ≠ lastIndex (n := n)) :
    negativeMap n g x i = x i := by
  simp [negativeMap, hi]

/-- The inverse negative-side map preserves every tangential coordinate. -/
@[simp]
theorem negativeMapInverse_apply_of_ne (g : ℝ^n → ℝ) (y : ℝ^n) {i : Fin n}
    (hi : i ≠ lastIndex (n := n)) :
    negativeMapInverse n g y i = y i := by
  simp [negativeMapInverse, hi]

/-- Negative-side flattening does not change the tangential projection. -/
@[simp]
theorem boundaryProjection_negativeMap (g : ℝ^n → ℝ) (x : ℝ^n) :
    boundaryProjection n (negativeMap n g x) = boundaryProjection n x := by
  ext i
  by_cases hi : i = lastIndex (n := n)
  · subst i
    simp
  · simp [boundaryProjection_apply_of_ne_last, negativeMap_apply_of_ne, hi]

/-- The inverse negative-side map does not change the tangential projection. -/
@[simp]
theorem boundaryProjection_negativeMapInverse (g : ℝ^n → ℝ) (y : ℝ^n) :
    boundaryProjection n (negativeMapInverse n g y) = boundaryProjection n y := by
  ext i
  by_cases hi : i = lastIndex (n := n)
  · subst i
    simp
  · simp [boundaryProjection_apply_of_ne_last, negativeMapInverse_apply_of_ne, hi]

/-- `negativeMapInverse` is a left inverse of `negativeMap`. -/
theorem negativeMapInverse_leftInverse (g : ℝ^n → ℝ) :
    Function.LeftInverse (negativeMapInverse n g) (negativeMap n g) := by
  intro x
  ext i
  by_cases hi : i = lastIndex (n := n)
  · subst i
    simp
  · simp [negativeMapInverse_apply_of_ne, negativeMap_apply_of_ne, hi]

/-- `negativeMapInverse` is a right inverse of `negativeMap`. -/
theorem negativeMapInverse_rightInverse (g : ℝ^n → ℝ) :
    Function.RightInverse (negativeMapInverse n g) (negativeMap n g) := by
  intro y
  ext i
  by_cases hi : i = lastIndex (n := n)
  · subst i
    simp
  · simp [negativeMapInverse_apply_of_ne, negativeMap_apply_of_ne, hi]

/-- A `C^m` graph height induces a `C^m` negative-side flattening map. -/
theorem negativeMap_contDiff (m : ℕ∞) {g : ℝ^n → ℝ}
    (hg : ContDiff ℝ m g) :
    ContDiff ℝ m (negativeMap n g) := by
  rw [show negativeMap n g =
      (EuclideanSpace.equiv (Fin n) ℝ).symm ∘
        (fun x : ℝ^n ↦ fun i ↦
          if i = lastIndex (n := n) then
            g (boundaryProjection n x) + x (lastIndex (n := n))
          else x i) by
    funext x
    rfl]
  refine (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.comp (contDiff_pi' fun i ↦ ?_)
  by_cases hi : i = lastIndex (n := n)
  · subst i
    simpa using
      (hg.comp (contDiff_boundaryProjection n m)).add
        (EuclideanSpace.proj (𝕜 := ℝ) (lastIndex (n := n))).contDiff
  · simpa [hi] using (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

/-- A `C^m` graph height induces a `C^m` inverse negative-side map. -/
theorem negativeMapInverse_contDiff (m : ℕ∞) {g : ℝ^n → ℝ}
    (hg : ContDiff ℝ m g) :
    ContDiff ℝ m (negativeMapInverse n g) := by
  rw [show negativeMapInverse n g =
      (EuclideanSpace.equiv (Fin n) ℝ).symm ∘
        (fun y : ℝ^n ↦ fun i ↦
          if i = lastIndex (n := n) then
            y (lastIndex (n := n)) - g (boundaryProjection n y)
          else y i) by
    funext y
    rfl]
  refine (EuclideanSpace.equiv (Fin n) ℝ).symm.contDiff.comp (contDiff_pi' fun i ↦ ?_)
  by_cases hi : i = lastIndex (n := n)
  · subst i
    simpa using
      (EuclideanSpace.proj (𝕜 := ℝ) (lastIndex (n := n))).contDiff.sub
        (hg.comp (contDiff_boundaryProjection n m))
  · simpa [hi] using (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

/-- The negative-side flattening as a global homeomorphism. -/
def negativeHomeomorph (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g) :
    ℝ^n ≃ₜ ℝ^n where
  toEquiv :=
    { toFun := negativeMap n g
      invFun := negativeMapInverse n g
      left_inv := negativeMapInverse_leftInverse n g
      right_inv := negativeMapInverse_rightInverse n g }
  continuous_toFun :=
    (negativeMap_contDiff n 1 hg).continuous
  continuous_invFun :=
    (negativeMapInverse_contDiff n 1 hg).continuous

/-- A point lies above the negative graph precisely when its flattened
image lies in the upper half-space. -/
theorem negativeMap_mem_upper_iff (g : ℝ^n → ℝ) (x : ℝ^n) :
    negativeMap n g x ∈ SobolevSpace.HalfSpace.upper n ↔
      -x (lastIndex (n := n)) < g (boundaryProjection n x) := by
  change 0 < negativeMap n g x (lastIndex (n := n)) ↔
    -x (lastIndex (n := n)) < g (boundaryProjection n x)
  rw [negativeMap_apply_normal]
  constructor <;> intro h <;> linarith

end PositiveDimension

/-- Restrict a global homeomorphism to an open source, with its image as target. -/
def restrictHomeomorph
    (e : ℝ^n ≃ₜ ℝ^n) (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) :
    OpenPartialHomeomorph (ℝ^n) (ℝ^n) :=
  e.toOpenPartialHomeomorphOfImageEq source hsourceOpen (e '' source) rfl

/-- Restricting a homeomorphism records the prescribed source exactly. -/
theorem restrictHomeomorph_source
    (e : ℝ^n ≃ₜ ℝ^n) (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) :
    (restrictHomeomorph n e source hsourceOpen).source = source := by
  rfl

/-- The target of a restricted homeomorphism is the image of its source. -/
theorem restrictHomeomorph_target
    (e : ℝ^n ≃ₜ ℝ^n) (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) :
    (restrictHomeomorph n e source hsourceOpen).target = e '' source := by
  rfl

/-- Restricting a Euclidean homeomorphism to a bounded source gives a bounded target. -/
theorem restrictHomeomorph_target_bounded
    (e : ℝ^n ≃ₜ ℝ^n) (source : Set (ℝ^n)) (hsourceOpen : IsOpen source)
    (hsourceBounded : Bornology.IsBounded source) :
    Bornology.IsBounded (restrictHomeomorph n e source hsourceOpen).target := by
  rw [restrictHomeomorph_target]
  have hcompact : IsCompact (closure source) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hsourceBounded.closure
  exact (hcompact.image e.continuous).isBounded.subset (image_mono subset_closure)

section PositiveDimension

variable [Fact (0 < n)]

/-- Positive graph chart restricted to an arbitrary open source. -/
def positiveChart
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) :
    OpenPartialHomeomorph (ℝ^n) (ℝ^n) :=
  restrictHomeomorph n (positiveHomeomorph n g hg) source hsourceOpen

/-- The positive chart agrees pointwise with the global positive flattening map. -/
@[simp]
theorem positiveChart_apply
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) (x : ℝ^n) :
    positiveChart n g hg source hsourceOpen x = positiveMap n g x :=
  rfl

/-- The inverse positive chart also agrees with the involutive positive flattening map. -/
@[simp]
theorem positiveChart_symm_apply
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) (y : ℝ^n) :
    (positiveChart n g hg source hsourceOpen).symm y = positiveMap n g y :=
  rfl

/-- The source of the restricted positive chart is the prescribed open set. -/
theorem positiveChart_source
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) :
    (positiveChart n g hg source hsourceOpen).source = source :=
  rfl

/-- A bounded source gives the restricted positive chart a bounded target. -/
theorem positiveChart_target_bounded
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (source : Set (ℝ^n)) (hsourceOpen : IsOpen source)
    (hsourceBounded : Bornology.IsBounded source) :
    Bornology.IsBounded (positiveChart n g hg source hsourceOpen).target :=
  restrictHomeomorph_target_bounded n
    (positiveHomeomorph n g hg) source hsourceOpen hsourceBounded

/-- Negative graph chart restricted to an arbitrary open source. -/
def negativeChart
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) :
    OpenPartialHomeomorph (ℝ^n) (ℝ^n) :=
  restrictHomeomorph n (negativeHomeomorph n g hg) source hsourceOpen

/-- The negative chart agrees pointwise with the global negative flattening map. -/
@[simp]
theorem negativeChart_apply
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) (x : ℝ^n) :
    negativeChart n g hg source hsourceOpen x = negativeMap n g x :=
  rfl

/-- The inverse negative chart agrees pointwise with `negativeMapInverse`. -/
@[simp]
theorem negativeChart_symm_apply
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) (y : ℝ^n) :
    (negativeChart n g hg source hsourceOpen).symm y = negativeMapInverse n g y :=
  rfl

/-- The source of the restricted negative chart is the prescribed open set. -/
theorem negativeChart_source
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (source : Set (ℝ^n)) (hsourceOpen : IsOpen source) :
    (negativeChart n g hg source hsourceOpen).source = source :=
  rfl

/-- A bounded source gives the restricted negative chart a bounded target. -/
theorem negativeChart_target_bounded
    (g : ℝ^n → ℝ) (hg : ContDiff ℝ 1 g)
    (source : Set (ℝ^n)) (hsourceOpen : IsOpen source)
    (hsourceBounded : Bornology.IsBounded source) :
    Bornology.IsBounded (negativeChart n g hg source hsourceOpen).target :=
  restrictHomeomorph_target_bounded n
    (negativeHomeomorph n g hg) source hsourceOpen hsourceBounded

end PositiveDimension

end SobolevSpace.Extension.GraphChart
