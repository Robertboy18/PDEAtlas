/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Changes of variables for Mathlib's Laplacian

Translations, reflections, and orthogonal changes of variables commute with `Δ`.
No regularity assumption is needed: the iterated Fréchet derivative transforms
under these invertible changes of variables even when it takes its default value.
The codomain can be any real normed space.
-/

@[expose] public noncomputable section

open scoped Laplacian

namespace InnerProductSpace

/-- Orthogonal changes of variables preserve the intrinsic Laplacian. -/
theorem laplacian_comp_linearIsometryEquiv
    {E G F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E ≃ₗᵢ[ℝ] G) (f : G → F) :
    Δ (f ∘ A) = Δ f ∘ A := by
  let b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ A) b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map A)]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  have h := A.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f
    uniqueDiffOn_univ (Set.mem_univ (A x)) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv] at h
  rw [h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    OrthonormalBasis.map_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Translation on the left commutes with `Δ`, without a regularity premise. -/
theorem laplacian_comp_add_left (f : E → F) (a x : E) :
    Δ (fun y ↦ f (a + y)) x = Δ f (a + x) := by
  simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_add_left]

/-- Translation on the right commutes with `Δ`, without a regularity premise. -/
theorem laplacian_comp_add_right (f : E → F) (a x : E) :
    Δ (fun y ↦ f (y + a)) x = Δ f (x + a) := by
  simpa only [add_comm] using laplacian_comp_add_left f a x

/-- Subtracting a fixed vector commutes with `Δ`, without a regularity premise. -/
theorem laplacian_comp_sub_right (f : E → F) (a x : E) :
    Δ (fun y ↦ f (y - a)) x = Δ f (x - a) := by
  simpa only [sub_eq_add_neg] using laplacian_comp_add_right f (-a) x

/-- Negating the argument commutes with `Δ`, without a regularity premise. -/
theorem laplacian_comp_neg (f : E → F) (x : E) :
    Δ (fun y ↦ f (-y)) x = Δ f (-x) :=
  congrFun (laplacian_comp_linearIsometryEquiv (LinearIsometryEquiv.neg ℝ) f) x

/-- Reflection about `a / 2` commutes with `Δ`, without a regularity premise. -/
theorem laplacian_comp_const_sub (f : E → F) (a x : E) :
    Δ (fun y ↦ f (a - y)) x = Δ f (a - x) := by
  simpa only [sub_eq_add_neg, laplacian_comp_add_left] using
    laplacian_comp_neg (fun y ↦ f (a + y)) x

end InnerProductSpace
