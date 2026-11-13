/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv.Energy
public import PDE.FDeriv.PartialDeriv.Norm
public import PDE.FDeriv.PartialDeriv.Support.Iterated

/-!
# Higher derivative norms controlled by coordinate derivatives

Repeatedly summing the norms of coordinate derivatives bounds the full
Fréchet derivative. This comparison allows estimates for mixed scalar
derivatives to be used with the general higher chain rule.
-/

@[expose] public noncomputable section

open scoped ContDiff

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- The sum of norms of all coordinate words of a prescribed length, recorded
recursively so no ordering convention on the words is needed. -/
def iteratedCoordinateNormSum : ℕ → (ℝ^n → F) → ℝ^n → ℝ
  | 0, f, x => ‖f x‖
  | k + 1, f, x => ∑ i : Fin n, iteratedCoordinateNormSum k (∂[i] f) x

theorem iteratedCoordinateNormSum_nonneg (k : ℕ) (f : ℝ^n → F) (x : ℝ^n) :
    0 ≤ iteratedCoordinateNormSum k f x := by
  induction k generalizing f with
  | zero => exact norm_nonneg _
  | succ k ih => exact Finset.sum_nonneg fun i _ ↦ ih (∂[i] f)

private theorem _root_.norm_multilinear_clm_le_sum {k : ℕ}
    (T : (ℝ^n) [×k]→L[ℝ] (ℝ^n →L[ℝ] F)) :
    ‖T‖ ≤ ∑ i : Fin n,
      ‖ContinuousLinearMap.compContinuousMultilinearMap
        (ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i (1 : ℝ))) T‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  intro v
  calc
    ‖T v‖ ≤ ∑ i, ‖T v (EuclideanSpace.single i 1)‖ :=
      (T v).norm_le_sum_norm_apply_single
    _ ≤ ∑ i : Fin n,
        ‖ContinuousLinearMap.compContinuousMultilinearMap
          (ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i (1 : ℝ))) T‖ *
            ∏ j, ‖v j‖ := by
      apply Finset.sum_le_sum
      intro i _
      let L := ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i (1 : ℝ))
      exact (L.compContinuousMultilinearMap T).le_opNorm v
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- The coordinate norm sum controls the complete derivative tensor in every
dimension, with only the finite differentiability needed for that derivative. -/
theorem norm_iteratedFDeriv_le_iteratedCoordinateNormSum (k : ℕ) {f : ℝ^n → F}
    {x : ℝ^n} (hf : ContDiffAt ℝ k f x) :
    ‖iteratedFDeriv ℝ k f x‖ ≤ iteratedCoordinateNormSum k f x := by
  induction k generalizing f with
  | zero => simp [iteratedCoordinateNormSum, norm_iteratedFDeriv_zero]
  | succ k ih =>
    have hfd : ContDiffAt ℝ k (fderiv ℝ f) x := hf.fderiv_right (by simp)
    rw [← norm_iteratedFDeriv_fderiv]
    apply (norm_multilinear_clm_le_sum _).trans
    apply Finset.sum_le_sum
    intro i _
    let L := ContinuousLinearMap.apply ℝ F (EuclideanSpace.single i (1 : ℝ))
    have heq := L.iteratedFDeriv_comp_left hfd (le_refl _)
    rw [← heq]
    exact ih (hfd.clm_apply contDiffAt_const)

/-- Smoothness of the input makes the coordinate norm sum continuous. -/
theorem continuous_iteratedCoordinateNormSum {f : ℝ^n → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) :
    Continuous (iteratedCoordinateNormSum k f) := by
  induction k generalizing f with
  | zero => exact hf.continuous.norm
  | succ k ih => exact continuous_finsetSum _ fun i _ ↦ ih (contDiff_top_partialDeriv hf)

end PDE

open PDE (iteratedCoordinateNormSum)

/-- Compact support is preserved by the coordinate norm sum. -/
theorem HasCompactSupport.iteratedCoordinateNormSum {f : ℝ^n → F}
    (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedCoordinateNormSum k f) := by
  induction k generalizing f with
  | zero => exact hf.norm
  | succ k ih =>
    have hcomp (i : Fin n) :
        HasCompactSupport (PDE.iteratedCoordinateNormSum k (∂[i] f)) :=
      ih (hf.iteratedPartialDeriv [i])
    have hsum := HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ ↦ hcomp i)
    convert hsum using 1
    ext x
    exact (Finset.sum_apply x _ _).symm
