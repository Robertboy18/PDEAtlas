/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

/-!
# Orthonormal coordinate charts for every oriented Euclidean hyperplane

For a linear isometry `A` of `ℝ^(n+1)` and `d : ℝ`, the map `y ↦ A (d, y)` is an isometry
from `ℝ^n` onto the affine hyperplane `{x | ⟪A e₀, x⟫ = d}`. Every unit vector `ν` is `A e₀`
for some such `A` (a reflection), so every oriented hyperplane has such a chart.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Common

variable {n : ℕ}

/-- An isometric coordinate-plane chart preserves the ordinary Euclidean distance. -/
theorem isometry_spatialIsometry_plane (A : ℝ^(n + 1) ≃ₗᵢ[ℝ] ℝ^(n + 1)) (d : ℝ) :
    Isometry (fun y : ℝ^n ↦ A (timeSpaceCons d y)) := by
  apply A.isometry.comp
  apply isometry_iff_dist_eq.mpr
  intro x y
  simp only [dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, PiLp.sub_apply,
    timeSpaceCons_zero, timeSpaceCons_succ, sub_self, zero_pow (by norm_num : 2 ≠ 0), zero_add]

/-- The chart with normal `A e₀` covers exactly the corresponding affine hyperplane. -/
theorem range_spatialIsometry_plane (A : ℝ^(n + 1) ≃ₗᵢ[ℝ] ℝ^(n + 1)) (d : ℝ) :
    Set.range (fun y : ℝ^n ↦ A (timeSpaceCons d y)) =
      {x | inner ℝ (A (EuclideanSpace.single 0 1)) x = d} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp only [mem_ofPred_eq, A.inner_map_map, EuclideanSpace.inner_single_left,
      map_one, one_mul, timeSpaceCons_zero]
  · intro hx
    change inner ℝ (A (EuclideanSpace.single 0 1)) x = d at hx
    have hzero : (A.symm x) 0 = d := by
      have hi := A.inner_map_map (EuclideanSpace.single 0 1) (A.symm x)
      simp only [A.apply_symm_apply, EuclideanSpace.inner_single_left, map_one, one_mul] at hi
      exact hi.symm.trans hx
    refine ⟨spatialPart (A.symm x), ?_⟩
    change A (timeSpaceCons d (spatialPart (A.symm x))) = x
    simpa only [hzero, A.apply_symm_apply] using
      congrArg A (timeSpaceCons_spatialPart (A.symm x))

/-- Every unit normal is the first vector of an orthogonal spatial coordinate system. -/
theorem exists_linearIsometryEquiv_single_zero_eq {ν : ℝ^(n + 1)} (hν : ‖ν‖ = 1) :
    ∃ A : ℝ^(n + 1) ≃ₗᵢ[ℝ] ℝ^(n + 1), A (EuclideanSpace.single 0 1) = ν := by
  refine ⟨Submodule.reflection (ℝ ∙ (EuclideanSpace.single 0 1 - ν))ᗮ, ?_⟩
  exact Submodule.reflection_sub (by simp [hν])

end PDE.Common
