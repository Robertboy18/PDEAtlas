/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Weight

/-!
# Coordinate monomials and multilinear expansions

A coordinate word assigns one coordinate to each argument of a multilinear map.
Its product has operator norm at most one. Expanding a multilinear map on the
coordinate vectors therefore costs at most the number of coordinate words,
which grows exponentially with the degree.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace ContinuousMultilinearMap

variable {ι G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {n : ℕ}

/-- The multilinear monomial selecting the coordinates in `w`, with coefficient `z`. -/
def coordinateMonomial (w : Fin n → ι) (z : G) : (ι → ℝ) [×n]→L[ℝ] G :=
  (ContinuousMultilinearMap.mkPiRing ℝ (Fin n) z).compContinuousLinearMap
    (fun j ↦ ContinuousLinearMap.proj (w j))

/-- Evaluation of a coordinate monomial is the product of its selected coordinates. -/
@[simp]
theorem coordinateMonomial_apply (w : Fin n → ι) (z : G) (v : Fin n → ι → ℝ) :
    coordinateMonomial w z v = (∏ j, v j (w j)) • z := rfl

variable [Fintype ι]

/-- Coordinate monomials introduce no loss in the norm of their coefficient. -/
theorem norm_coordinateMonomial_le (w : Fin n → ι) (z : G) :
    ‖coordinateMonomial w z‖ ≤ ‖z‖ := by
  apply opNorm_le_bound (norm_nonneg _)
  intro v
  simp only [coordinateMonomial_apply, norm_smul, norm_prod]
  calc
    (∏ j, ‖v j (w j)‖) * ‖z‖ ≤ (∏ j, ‖v j‖) * ‖z‖ := by
      gcongr with j
      exact norm_le_pi_norm (v j) (w j)
    _ = ‖z‖ * ∏ j, ‖v j‖ := mul_comm _ _

/-- Values on coordinate words are bounded by the operator norm, including degree zero. -/
theorem norm_apply_coordinate_vectors_le [DecidableEq ι]
    (f : (ι → ℝ) [×n]→L[ℝ] G) (w : Fin n → ι) :
    ‖f (fun j ↦ Pi.single (w j) 1)‖ ≤ ‖f‖ := by
  apply (f.le_opNorm _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact le_of_eq (by simp [Pi.norm_single])

/-- The sum over coordinate words has only exponential growth in the degree. -/
theorem sum_norm_apply_coordinate_vectors_le [DecidableEq ι]
    (f : (ι → ℝ) [×n]→L[ℝ] G) :
    ∑ w : Fin n → ι, ‖f (fun j ↦ Pi.single (w j) 1)‖ ≤
      (Fintype.card ι : ℝ) ^ n * ‖f‖ := by
  calc
    _ ≤ ∑ _w : Fin n → ι, ‖f‖ :=
      Finset.sum_le_sum fun w _ ↦ f.norm_apply_coordinate_vectors_le w
    _ = _ := by simp

/-- Expansion in coordinate vectors recovers the original multilinear map. -/
theorem eq_sum_coordinateMonomial [DecidableEq ι] (f : (ι → ℝ) [×n]→L[ℝ] G) :
    f = ∑ w : Fin n → ι, coordinateMonomial w (f (fun j ↦ Pi.single (w j) 1)) := by
  ext v
  have hv (j : Fin n) : v j = ∑ i : ι, (v j i) • Pi.single i (1 : ℝ) := by
    ext i
    simp [Pi.single_apply]
  calc
    f v = f (fun j ↦ ∑ i : ι, (v j i) • Pi.single i (1 : ℝ)) := by
      congr 1
      funext j
      exact hv j
    _ = ∑ w : Fin n → ι, f (fun j ↦ (v j (w j)) • Pi.single (w j) (1 : ℝ)) :=
      f.map_sum _
    _ = _ := by simp [map_smul_univ]

end ContinuousMultilinearMap
