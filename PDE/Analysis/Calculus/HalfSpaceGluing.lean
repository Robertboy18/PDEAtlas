/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus

/-!
# Classical gluing across a coordinate hyperplane

Matching values and derivatives on the common hyperplane glue derivatives from the two
closed half-spaces. Iterating this argument gives finite classical regularity when all
coordinate derivative words through that order match.
-/

@[expose] public section

open Set
open scoped Topology

namespace PDE.Analysis

variable {n : ℕ}

/-- A closed coordinate half-space has unique derivatives even on its boundary. -/
theorem uniqueDiffOn_coordinateHalfSpace (i : Fin n) :
    UniqueDiffOn ℝ {x : ℝ^n | 0 ≤ x i} := by
  apply uniqueDiffOn_convex
    (convex_halfSpace_ge (EuclideanSpace.proj i).isLinear 0)
  refine ⟨EuclideanSpace.single i 1, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Filter.mem_of_superset
    ((isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).mem_nhds
      (show (0 : ℝ) < (EuclideanSpace.single i 1 : ℝ^n) i by simp))
  intro x hx
  change 0 ≤ x i
  exact (show 0 < x i from hx).le

/-- Derivatives on the two closed half-spaces glue when their values and linear maps
agree on the separating hyperplane. -/
theorem hasFDerivAt_piecewise_halfSpace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin n) {f g : ℝ^n → F} {f' g' : ℝ^n → (ℝ^n →L[ℝ] F)}
    (hf : ∀ x, x i ≤ 0 → HasFDerivWithinAt f (f' x) {y | y i ≤ 0} x)
    (hg : ∀ x, 0 ≤ x i → HasFDerivWithinAt g (g' x) {y | 0 ≤ y i} x)
    (hfg : ∀ x, x i = 0 → f x = g x)
    (hfg' : ∀ x, x i = 0 → f' x = g' x) (x : ℝ^n) :
    HasFDerivAt (fun y ↦ if y i < 0 then f y else g y)
      (if x i < 0 then f' x else g' x) x := by
  have hu : HasFDerivWithinAt (fun y ↦ if y i < 0 then f y else g y)
      (if x i < 0 then f' x else g' x) {y | 0 ≤ y i} x := by
    by_cases hx : 0 ≤ x i
    · rw [ite_eq_right (not_lt.mpr hx)]
      exact (hg x hx).congr' (fun y hy ↦ ite_eq_right (not_lt.mpr hy)) hx
    · apply HasFDerivWithinAt.of_notMem_closure
      have hs : IsClosed {y : ℝ^n | 0 ≤ y i} :=
        isClosed_le continuous_const (EuclideanSpace.proj i).continuous
      simpa only [hs.closure_eq, mem_ofPred_eq] using hx
  have hl : HasFDerivWithinAt (fun y ↦ if y i < 0 then f y else g y)
      (if x i < 0 then f' x else g' x) {y | y i ≤ 0} x := by
    by_cases hx : x i ≤ 0
    · have hd : (if x i < 0 then f' x else g' x) = f' x := by
        split_ifs with h
        · rfl
        · exact (hfg' x (le_antisymm hx (not_lt.mp h))).symm
      rw [hd]
      apply (hf x hx).congr' ?_ hx
      intro y hy
      change (if y i < 0 then f y else g y) = f y
      split_ifs with h
      · rfl
      · exact (hfg y (le_antisymm hy (not_lt.mp h))).symm
    · apply HasFDerivWithinAt.of_notMem_closure
      have hs : IsClosed {y : ℝ^n | y i ≤ 0} :=
        isClosed_le (EuclideanSpace.proj i).continuous continuous_const
      simpa only [hs.closure_eq, mem_ofPred_eq] using hx
  have hcover : {y : ℝ^n | 0 ≤ y i} ∪ {y | y i ≤ 0} = univ := by
    ext y
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    exact le_total 0 (y i)
  rw [← hasFDerivWithinAt_univ, ← hcover]
  exact hu.union hl

/-- Two globally `C^k` functions with matching coordinate jets through order `k`
give a globally `C^k` piecewise function across a coordinate hyperplane. -/
theorem contDiff_piecewise_halfSpace (i : Fin n) {k : ℕ} {f g : ℝ^n → ℝ}
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g)
    (hjet : ∀ α : List (Fin n), α.length ≤ k → ∀ x, x i = 0 →
      iteratedPartialDeriv α f x = iteratedPartialDeriv α g x) :
    ContDiff ℝ k (fun x ↦ if x i < 0 then f x else g x) := by
  induction k generalizing f g with
  | zero =>
    apply contDiff_zero.mpr
    apply Continuous.piecewise (s := {x : ℝ^n | x i < 0}) ?_ hf.continuous hg.continuous
    intro x hx
    exact hjet [] (by simp) x
      (frontier_lt_subset_eq (EuclideanSpace.proj i).continuous continuous_const hx)
  | succ k ih =>
    let D : ℝ^n → (ℝ^n →L[ℝ] ℝ) := fun x ↦
      ∑ j, (if x i < 0 then (∂[j] f) x else (∂[j] g) x) •
        EuclideanSpace.proj j
    have hD : ContDiff ℝ k D := by
      apply ContDiff.sum
      intro j _
      apply ContDiff.smul_const
      apply ih (contDiff_partialDeriv_of_succ hf) (contDiff_partialDeriv_of_succ hg)
      intro α hα x hx
      simpa only [← iteratedPartialDeriv_append_single] using
        hjet (α ++ [j]) (by simp only [List.length_append, List.length_singleton]; omega) x hx
    have hDapply (x : ℝ^n) :
        D x = if x i < 0 then fderiv ℝ f x else fderiv ℝ g x := by
      ext v
      by_cases hx : x i < 0 <;>
        simp only [D, hx, ↓reduceIte, sum_apply, smul_apply, smul_eq_mul,
          fderiv_apply_eq_sum_partialDeriv_mul, EuclideanSpace.coe_proj]
    refine contDiff_succ_iff_hasFDerivAt.mpr ⟨D, hD, fun x ↦ ?_⟩
    rw [hDapply]
    apply hasFDerivAt_piecewise_halfSpace i
      (fun y _ ↦ (hf.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt)
      (fun y _ ↦ (hg.differentiable (by simp) y).hasFDerivAt.hasFDerivWithinAt)
      (fun y hy ↦ hjet [] (by simp) y hy)
    intro y hy
    ext v
    simp only [fderiv_apply_eq_sum_partialDeriv_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (· * v j) (hjet [j] (by simp) y hy)

end PDE.Analysis
