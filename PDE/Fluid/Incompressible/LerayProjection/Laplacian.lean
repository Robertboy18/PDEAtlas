/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.LerayProjection.Sobolev
public import PDE.Parabolic.Heat.WholeSpace.SobolevGenerator

/-!
# The Leray projection commutes with the Laplacian

The vector Laplacian from vector `H^{k+2}` to vector `Hᵏ` is the sum of the derivative words
`∂ᵢ∂ᵢ`, and the Sobolev Leray projection commutes with every derivative word, so it commutes
with the Laplacian.
-/

@[expose] public noncomputable section

open SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open scoped Sobolev

namespace IncompressibleFlow

variable {n k : ℕ}

/-- The vector Laplacian is the sum of the diagonal second derivative words. -/
theorem vectorLaplacian_eq_sum (v : VectorH n (k + 2)) :
    vectorLaplacian n k v =
      ∑ i : Fin n, vectorDerivativeWord [i, i] (by simp [Nat.add_comm]) v := by
  refine PiLp.ext fun j ↦ ?_
  rw [vectorLaplacian_apply, higherOrderLaplacianCLM, sum_apply]
  have h := map_sum (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n ↦ W^{k,2}(ℝ^n)) j)
    (fun i ↦ vectorDerivativeWord [i, i] (by simp [Nat.add_comm]) v) Finset.univ
  simp only [PiLp.proj_apply] at h
  rw [h]
  simp only [vectorDerivativeWord, ContinuousLinearMap.piLpMap_apply]

/-- The Sobolev Leray projection commutes with the vector Laplacian. -/
theorem leraySobolev_vectorLaplacian (v : VectorH n (k + 2)) :
    leraySobolev n k (vectorLaplacian n k v) =
      vectorLaplacian n k (leraySobolev n (k + 2) v) := by
  rw [vectorLaplacian_eq_sum, vectorLaplacian_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ leraySobolev_vectorDerivativeWord _ _ v

end IncompressibleFlow
