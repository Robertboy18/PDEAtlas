/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.Derivatives
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceVector

/-!
# The actual Leray projection on whole-space integer Sobolev spaces

Every derivative row is projected by the existing `L²` Leray operator.
Its translation commutation gives the first weak-derivative steps in this
family. Chaining those steps verifies all graph relations. Thus the resulting
Sobolev operator has exactly the original Leray projection as its base row and
commutes with all weak derivatives. Rowwise `L²` contraction gives contraction
in the full finite-Hilbert Sobolev norm.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped BigOperators Sobolev

namespace IncompressibleFlow

variable {n k : ℕ}

/-- The scalar derivative coordinate obtained from the actual Leray-projected row. -/
def projectedScalarRow (U : VectorH n k) (j : Fin n) (a : DerivIndex n k) :
    DerivLp n 2 Set.univ :=
  l2Coordinate j (lerayProjection n (l2SobolevRow a U))

private def projectedWord (U : VectorH n k) (j : Fin n) (α : List (Fin n)) : ℝ^n → ℝ :=
  if hα : α.length ≤ k then projectedScalarRow U j (derivIndexOfList α hα) else 0

private theorem projectedWord_step (U : VectorH n k) (j i : Fin n)
    (α : List (Fin n)) (hα : α.length < k) :
    HasWeakDerivativeOn Set.univ [i] (projectedWord U j α)
      (projectedWord U j (α ++ [i])) := by
  have hαi : (α ++ [i]).length ≤ k := by simpa using hα
  have hlength : α.length + 1 ≤ k := by omega
  have h := hasWeakDerivativeOn_lerayProjection_H1 i j
    (fun l ↦ derivativeWordCLM α hlength (U l))
  simpa only [projectedWord, dite_eq_left hα.le, dite_eq_left hαi, projectedScalarRow,
    l2SobolevRow_apply, wkpBaseCoordinateCLM_apply, wkpCoordinateCLM_apply,
    derivativeWordCLM_apply, derivativeWordIndex_baseIndex,
    derivativeWordIndex_singleDerivIndex] using h

/-- All projected derivative rows satisfy the genuine Sobolev graph relations. -/
theorem projectedScalarRows_isWkpOn (U : VectorH n k) (j : Fin n) :
    IsWkpOn (WithLp.toLp 2 (projectedScalarRow U j)) := by
  intro a
  have hnil : projectedWord U j [] = projectedScalarRow U j (baseIndex n k) := by
    simp only [projectedWord, List.length_nil, dite_eq_left (Nat.zero_le k), derivIndexOfList_nil]
  have hloc : LocallyIntegrableOn (projectedWord U j []) Set.univ volume := by
    rw [hnil]
    exact memLp_locallyIntegrableOn_domain (Lp.memLp _) (by norm_num)
  have h := hasWeakDerivativeOn_of_append_single_chain_order k (projectedWord U j)
    hloc (fun α i hα ↦ projectedWord_step U j i α hα) a.toList a.toList_length_le
  rw [hnil] at h
  simpa only [projectedWord, dite_eq_left a.toList_length_le,
    derivIndexOfList_toList] using h

/-- Projected scalar Sobolev graphs, retaining every actual projected derivative row. -/
def projectedVectorH (U : VectorH n k) : VectorH n k :=
  WithLp.toLp 2 (fun j ↦
    (⟨WithLp.toLp 2 (projectedScalarRow U j), projectedScalarRows_isWkpOn U j⟩ : W^{k,2}(ℝ^n)))

/-- Each derivative coordinate is the corresponding coordinate of the actual
whole-space `L²` projection. -/
theorem projectedVectorH_coordinate (U : VectorH n k) (j : Fin n) (a : DerivIndex n k) :
    wkpCoordinateCLM a (projectedVectorH U j) = projectedScalarRow U j a :=
  rfl

/-- Summing scalar coordinate energies recovers the exact vector `L²` energy. -/
theorem sum_norm_l2Coordinate_sq (v : WholeSpaceL2 n) :
    ∑ j : Fin n, ‖l2Coordinate j v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := Lp.norm_euclideanTuple_sq (fun j : Fin n ↦ l2Coordinate j v)
  rw [show Lp.euclideanTuple (fun j : Fin n ↦ l2Coordinate j v) = v from
    Lp.euclideanTuple_coordinates v] at h
  exact h.symm

/-- A vector derivative row retains the sum of scalar coordinate energies. -/
theorem norm_l2SobolevRow_sq (a : DerivIndex n k) (U : VectorH n k) :
    ‖l2SobolevRow a U‖ ^ 2 = ∑ j : Fin n, ‖wkpCoordinateCLM a (U j)‖ ^ 2 :=
  Lp.norm_euclideanTuple_sq _

/-- A scalar coordinate of a vector `L²` class has at most its norm. -/
theorem norm_l2Coordinate_le (j : Fin n) (v : WholeSpaceL2 n) :
    ‖l2Coordinate j v‖ ≤ ‖v‖ := by
  have h := Lp.norm_coordinate_le_norm_euclideanTuple (fun i ↦ l2Coordinate i v) j
  rwa [show Lp.euclideanTuple (fun i ↦ l2Coordinate i v) = v from
    Lp.euclideanTuple_coordinates v] at h

/-- A vector base row has at most the norm of the vector Sobolev class. -/
theorem norm_l2SobolevRow_le (a : DerivIndex n k) (U : VectorH n k) :
    ‖l2SobolevRow a U‖ ≤ ‖U‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_l2SobolevRow_sq, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum fun j _ ↦ pow_le_pow_left₀ (norm_nonneg _)
    (wkpCoordinateCLM_norm_le a (U j)) 2

/-- The actual Leray projection contracts the complete integer Sobolev norm. -/
theorem norm_projectedVectorH_le (U : VectorH n k) : ‖projectedVectorH U‖ ≤ ‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  have hnorm (V : W^{k,2}(ℝ^n)) :
      ‖V‖ ^ 2 = ∑ a : DerivIndex n k, ‖wkpCoordinateCLM a V‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ V.val
  simp_rw [hnorm, projectedVectorH_coordinate]
  change (∑ j : Fin n, ∑ a : DerivIndex n k, ‖projectedScalarRow U j a‖ ^ 2) ≤
    ∑ j : Fin n, ∑ a : DerivIndex n k, ‖wkpCoordinateCLM a (U j)‖ ^ 2
  rw [Finset.sum_comm, Finset.sum_comm (f := fun j a ↦ ‖wkpCoordinateCLM a (U j)‖ ^ 2)]
  apply Finset.sum_le_sum
  intro a _
  simp only [projectedScalarRow]
  rw [sum_norm_l2Coordinate_sq, ← norm_l2SobolevRow_sq]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_lerayProjection_le n _)

/-- The canonical bounded Leray operator on whole-space vector `Hᵏ`. -/
def leraySobolev (n k : ℕ) : VectorH n k →L[ℝ] VectorH n k := by
  let T : VectorH n k →ₗ[ℝ] VectorH n k :=
    { toFun := projectedVectorH
      map_add' U V := by
        apply PiLp.ext
        intro j
        apply Subtype.ext
        apply PiLp.ext
        intro a
        change projectedScalarRow (U + V) j a =
          projectedScalarRow U j a + projectedScalarRow V j a
        simp only [projectedScalarRow, map_add]
      map_smul' c U := by
        apply PiLp.ext
        intro j
        apply Subtype.ext
        apply PiLp.ext
        intro a
        change projectedScalarRow (c • U) j a = c • projectedScalarRow U j a
        simp only [projectedScalarRow, map_smul] }
  exact T.mkContinuous 1 (fun U ↦ by
    change ‖projectedVectorH U‖ ≤ 1 * ‖U‖
    simpa only [one_mul] using norm_projectedVectorH_le U)

/-- Applying the Sobolev operator retains the same projected derivative coordinates. -/
theorem leraySobolev_coordinate (U : VectorH n k) (j : Fin n) (a : DerivIndex n k) :
    wkpCoordinateCLM a (leraySobolev n k U j) =
      l2Coordinate j (lerayProjection n (l2SobolevRow a U)) :=
  rfl

/-- Every whole vector derivative row commutes with the original `L²` projector. -/
theorem l2SobolevRow_leraySobolev (U : VectorH n k) (a : DerivIndex n k) :
    l2SobolevRow a (leraySobolev n k U) = lerayProjection n (l2SobolevRow a U) := by
  rw [l2SobolevRow_apply]
  simp only [leraySobolev_coordinate]
  exact Lp.euclideanTuple_coordinates _

/-- The bounded whole-space Sobolev projection is contractive. -/
theorem norm_leraySobolev_le (U : VectorH n k) : ‖leraySobolev n k U‖ ≤ ‖U‖ :=
  norm_projectedVectorH_le U

/-- Coordinatewise weak differentiation between vector Sobolev spaces. -/
def vectorDerivativeWord {r : ℕ} (α : List (Fin n)) (hα : α.length + r ≤ k) :
    VectorH n k →L[ℝ] VectorH n r :=
  ContinuousLinearMap.piLpMap 2 (fun _ : Fin n ↦ derivativeWordCLM α hα)

/-- Extracted vector rows are the original rows with the derivative prefix. -/
theorem l2SobolevRow_vectorDerivativeWord {r : ℕ} (α : List (Fin n))
    (hα : α.length + r ≤ k) (U : VectorH n k) (a : DerivIndex n r) :
    l2SobolevRow a (vectorDerivativeWord α hα U) =
      l2SobolevRow (derivativeWordIndex α hα a) U := by
  simp only [l2SobolevRow_apply, vectorDerivativeWord, ContinuousLinearMap.piLpMap_apply,
    wkpCoordinateCLM_apply, derivativeWordCLM_apply]

/-- The actual whole-space Leray projection commutes with arbitrary weak
derivative words as entire Sobolev graph elements. -/
theorem leraySobolev_vectorDerivativeWord {r : ℕ} (α : List (Fin n))
    (hα : α.length + r ≤ k) (U : VectorH n k) :
    leraySobolev n r (vectorDerivativeWord α hα U) =
      vectorDerivativeWord α hα (leraySobolev n k U) := by
  apply PiLp.ext
  intro j
  apply Subtype.ext
  apply PiLp.ext
  intro a
  change wkpCoordinateCLM a (leraySobolev n r (vectorDerivativeWord α hα U) j) =
    wkpCoordinateCLM a (vectorDerivativeWord α hα (leraySobolev n k U) j)
  rw [leraySobolev_coordinate, l2SobolevRow_vectorDerivativeWord]
  change _ = wkpCoordinateCLM (derivativeWordIndex α hα a) (leraySobolev n k U j)
  exact (leraySobolev_coordinate U j _).symm

/-- The Sobolev lift is the same idempotent projection at every derivative row. -/
theorem leraySobolev_idempotent (U : VectorH n k) :
    leraySobolev n k (leraySobolev n k U) = leraySobolev n k U := by
  apply PiLp.ext
  intro j
  apply Subtype.ext
  apply PiLp.ext
  intro a
  change wkpCoordinateCLM a (leraySobolev n k (leraySobolev n k U) j) =
    wkpCoordinateCLM a (leraySobolev n k U j)
  simp only [leraySobolev_coordinate, l2SobolevRow_leraySobolev,
    lerayProjection_lerayProjection]

/-- The operator norm of the actual Sobolev Leray projection is at most one. -/
theorem norm_leraySobolev_operator_le : ‖leraySobolev n k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro U
  simpa only [one_mul] using norm_leraySobolev_le U

end IncompressibleFlow
