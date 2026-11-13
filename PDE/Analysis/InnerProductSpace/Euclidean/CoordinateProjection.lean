/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

/-!
# Removing the last Euclidean coordinate

The projection and its zero-coordinate right inverse are the two relevant
parts of Mathlib's `EuclideanSpace.finAddEquivProd`. The squared-norm identity
uses the Euclidean norm, independently of the product norm on that equivalence.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {n : ℕ}

/-- Project onto all coordinates except the last one. -/
def coordinateProjection : ℝ^(n + 1) →L[ℝ] ℝ^n :=
  (ContinuousLinearMap.fst ℝ (ℝ^n) (ℝ^1)).comp
    EuclideanSpace.finAddEquivProd.toContinuousLinearMap

/-- The projected coordinates retain their order. -/
@[simp]
theorem coordinateProjection_apply (x : ℝ^(n + 1)) (i : Fin n) :
    coordinateProjection x i = x i.castSucc := rfl

/-- Include Euclidean space by appending a zero coordinate. -/
def coordinateInclusion : ℝ^n →L[ℝ] ℝ^(n + 1) :=
  EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (ℝ^n) (ℝ^1))

/-- The included coordinates retain their values. -/
@[simp]
theorem coordinateInclusion_castSucc (x : ℝ^n) (i : Fin n) :
    coordinateInclusion x i.castSucc = x i := by
  simp [coordinateInclusion, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd]

/-- The appended coordinate is zero. -/
@[simp]
theorem coordinateInclusion_last (x : ℝ^n) :
    coordinateInclusion x (Fin.last n) = 0 := by
  simp [coordinateInclusion, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd]

/-- Projection is a left inverse to the inclusion. -/
@[simp]
theorem coordinateProjection_coordinateInclusion (x : ℝ^n) :
    coordinateProjection (coordinateInclusion x) = x := by
  ext i
  simp

/-- Squared norm under the last-coordinate splitting. -/
theorem norm_sq_coordinateProjection (x : ℝ^(n + 1)) :
    ‖x‖ ^ 2 = ‖coordinateProjection x‖ ^ 2 + (x (Fin.last n)) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc,
    coordinateProjection_apply]

/-- Projection preserves the retained coordinate directions. -/
@[simp]
theorem coordinateProjection_single_castSucc (i : Fin n) :
    coordinateProjection (EuclideanSpace.single i.castSucc 1) =
      EuclideanSpace.single i 1 := by
  ext j
  simp

/-- Projection annihilates the last coordinate direction. -/
@[simp]
theorem coordinateProjection_single_last :
    coordinateProjection (EuclideanSpace.single (Fin.last n) 1) = 0 := by
  ext j
  simp

/-- Removing the last coordinate cannot increase the Euclidean norm. -/
theorem norm_coordinateProjection_apply_le (x : ℝ^(n + 1)) :
    ‖coordinateProjection x‖ ≤ ‖x‖ := by
  nlinarith [norm_sq_coordinateProjection x, norm_nonneg (coordinateProjection x),
    norm_nonneg x, sq_nonneg (x (Fin.last n))]

/-- Appending a zero coordinate preserves the Euclidean norm. -/
@[simp]
theorem norm_coordinateInclusion_apply (x : ℝ^n) : ‖coordinateInclusion x‖ = ‖x‖ := by
  have h := norm_sq_coordinateProjection (coordinateInclusion x)
  simp only [coordinateProjection_coordinateInclusion, coordinateInclusion_last] at h
  nlinarith [norm_nonneg (coordinateInclusion x), norm_nonneg x]

/-- The last-coordinate projection is a contraction, including in dimension zero. -/
theorem norm_coordinateProjection_le : ‖coordinateProjection (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simpa only [one_mul] using norm_coordinateProjection_apply_le (n := n)

/-- The zero-coordinate inclusion is a contraction, including in dimension zero. -/
theorem norm_coordinateInclusion_le : ‖coordinateInclusion (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simp only [norm_coordinateInclusion_apply, one_mul, le_refl, implies_true]

/-- In positive target dimension the projection has operator norm one. -/
theorem norm_coordinateProjection (hn : 0 < n) :
    ‖coordinateProjection (n := n)‖ = 1 := by
  let i : Fin n := ⟨0, hn⟩
  apply le_antisymm norm_coordinateProjection_le
  have h := (coordinateProjection (n := n)).le_opNorm
    (coordinateInclusion (EuclideanSpace.single i 1))
  simpa only [coordinateProjection_coordinateInclusion, norm_coordinateInclusion_apply,
    PiLp.norm_single, norm_one, mul_one] using h

/-- In positive source dimension the inclusion has operator norm one. -/
theorem norm_coordinateInclusion (hn : 0 < n) :
    ‖coordinateInclusion (n := n)‖ = 1 := by
  let i : Fin n := ⟨0, hn⟩
  apply le_antisymm norm_coordinateInclusion_le
  have h := (coordinateInclusion (n := n)).le_opNorm (EuclideanSpace.single i 1)
  simpa only [norm_coordinateInclusion_apply, PiLp.norm_single, norm_one, mul_one] using h

end PDE.Analysis
