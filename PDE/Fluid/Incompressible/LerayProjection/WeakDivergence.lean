/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.Sobolev
public import PDE.Spaces.Sobolev.Calculus.Divergence.FirstOrder
public import PDE.Spaces.Sobolev.Evolution.VectorL2Triple
import PDE.Fluid.Incompressible.LerayProjection.SobolevDilation

/-!
# The actual weak divergence of a solenoidal Sobolev field

The orthogonal definition of the L² solenoidal space annihilates gradients
of completed whole-space H¹ tests. Integration by parts and density then
identify the sum of the stored first derivatives with zero as an L² element.
This connects the Leray projection to the weak derivative coordinates used
in the fluid energy calculation. Conversely, a vector H¹ field whose first
derivatives sum to zero has a solenoidal L² representative, so the Leray
projection fixes its L² field.
-/

@[expose] public noncomputable section

namespace IncompressibleFlow

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev InnerProductSpace

set_option linter.missingDocs true

/-- The scalar negative divergence of an H¹ flux vanishes when its actual
L² vector representative belongs to the solenoidal space. -/
theorem negativeDivergence_eq_zero_of_l2Solenoidal {n : ℕ}
    (Q : Fin n → H¹(ℝ^n))
    (hQ : Lp.euclideanTuple (fun i ↦ wkpBaseCoordinateCLM (Q i)) ∈ l2Solenoidal n) :
    negativeDivergence Q = 0 := by
  have hpair (v : H¹₀(ℝ^n)) : ⟪negativeDivergence Q, baseCoordCLM v⟫_ℝ = 0 := by
    rw [negativeDivergence_pairing]
    have heq : (∑ i, ⟪wkpBaseCoordinateCLM (Q i), derivCoordCLM i v⟫_ℝ) =
        ⟪Lp.euclideanTuple (fun i ↦ wkpBaseCoordinateCLM (Q i)),
          wkpGradientCLM (v : H¹(ℝ^n))⟫_ℝ := by
      change _ = ⟪Lp.euclideanTuple (fun i ↦ wkpBaseCoordinateCLM (Q i)),
        Lp.euclideanTuple (fun i ↦ wkpCoordinateCLM (singleDerivIndex n i)
          (v : H¹(ℝ^n)))⟫_ℝ
      rw [Lp.inner_euclideanTuple]
      rfl
    rw [heq]
    exact inner_solenoidal_wkpGradient_eq_zero _ hQ (v : H¹(ℝ^n))
  let L := innerSL ℝ (negativeDivergence Q)
  have htest : (fun v : H¹₀(ℝ^n) ↦ L (baseCoordCLM v)) = fun _ ↦ 0 := by
    funext v
    exact hpair v
  have hzero : (L : DerivLp n 2 Set.univ → ℝ) = fun _ ↦ 0 :=
    (baseCoordCLM_denseRange isOpen_univ).equalizer L.continuous continuous_const htest
  have hself : ⟪negativeDivergence Q, negativeDivergence Q⟫_ℝ = 0 :=
    congrFun hzero (negativeDivergence Q)
  exact inner_self_eq_zero.mp hself

/-- The sum of the stored first derivative coordinates is the genuine zero
L² divergence of a solenoidal vector H¹ field. -/
theorem sum_firstDerivatives_eq_zero_of_l2Solenoidal {n : ℕ} (U : VectorH n 1)
    (hU : l2SobolevRow (baseIndex n 1) U ∈ l2Solenoidal n) :
    (∑ i : Fin n, wkpCoordinateCLM (singleDerivIndex n i) (U i)) = 0 := by
  exact neg_eq_zero.mp (negativeDivergence_eq_zero_of_l2Solenoidal (fun i ↦ U i) hU)

/-- A vector H¹ field whose stored first derivative coordinates sum to zero has a solenoidal
L² representative: it is orthogonal to every test gradient. -/
theorem l2SobolevRow_mem_l2Solenoidal_of_sum_firstDerivatives_eq_zero {n : ℕ}
    (U : VectorH n 1)
    (hU : (∑ i : Fin n, wkpCoordinateCLM (singleDerivIndex n i) (U i)) = 0) :
    l2SobolevRow (baseIndex n 1) U ∈ l2Solenoidal n := by
  rw [mem_l2Solenoidal_iff_inner]
  intro φ
  have hdiv : negativeDivergence (fun i ↦ U i) = 0 := by
    change -(∑ i, wkpCoordinateCLM (singleDerivIndex n i) (U i)) = 0
    rw [hU, neg_zero]
  have h := negativeDivergence_pairing (fun i ↦ U i) (testFunctionToH10 φ)
  rw [hdiv, inner_zero_left] at h
  rw [h]
  change ⟪Lp.euclideanTuple (fun i ↦ wkpCoordinateCLM (baseIndex n 1) (U i)),
    Lp.euclideanTuple (fun i ↦ wkpCoordinateCLM (singleDerivIndex n i)
      ((testFunctionToH10 φ : H¹₀(ℝ^n)) : H¹(ℝ^n)))⟫_ℝ = _
  rw [Lp.inner_euclideanTuple]
  rfl

/-- The Leray projection fixes the L² field of a vector H¹ field whose first derivatives sum
to zero. -/
theorem leraySobolev_vectorLower_of_sum_firstDerivatives_eq_zero {n : ℕ} (U : VectorH n 1)
    (hU : (∑ i : Fin n, wkpCoordinateCLM (singleDerivIndex n i) (U i)) = 0) :
    leraySobolev n 0 (vectorLower n 0 U) = vectorLower n 0 U := by
  apply l2SobolevRow_base_injective
  rw [l2SobolevRow_leraySobolev, l2SobolevRow_base_vectorLower]
  exact lerayProjection_eq_self (l2SobolevRow_mem_l2Solenoidal_of_sum_firstDerivatives_eq_zero U hU)

/-- The contractive H¹ Leray lift has zero actual weak divergence, rather
than only a distributional constraint on its base representative. -/
theorem negativeDivergence_leraySobolev {n : ℕ} (U : VectorH n 1) :
    negativeDivergence (fun i ↦ leraySobolev n 1 U i) = 0 := by
  apply negativeDivergence_eq_zero_of_l2Solenoidal
  change l2SobolevRow (baseIndex n 1) (leraySobolev n 1 U) ∈ l2Solenoidal n
  rw [l2SobolevRow_leraySobolev]
  exact lerayProjection_mem n _

end IncompressibleFlow
