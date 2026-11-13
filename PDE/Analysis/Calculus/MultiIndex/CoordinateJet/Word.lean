/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.MultiIndex.PartialDeriv

/-!
# Coordinate jets as derivative words

Evaluating a smooth iterated Fréchet derivative on a coordinate tuple gives
the corresponding word `iteratedPartialDeriv` of partial derivatives. The sorted tuple
therefore connects unordered coordinate multiindices to explicit mixed
derivative computations.
-/

@[expose] public noncomputable section

open scoped ContDiff

namespace PDE.Analysis.MultiIndex

/-- A coordinate tuple evaluates the iterated Fréchet derivative as the
coordinate derivative word `iteratedPartialDeriv` in that order. -/
theorem iteratedFDeriv_basisFun_eq_iteratedPartialDeriv {n j : ℕ}
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ ∞ u)
    (v : Fin j → Fin n) (x : ℝ^n) :
    iteratedFDeriv ℝ j u x (fun i ↦ EuclideanSpace.basisFun (Fin n) ℝ (v i)) =
      iteratedPartialDeriv (List.ofFn v) u x := by
  induction j generalizing x with
  | zero => simp [iteratedPartialDeriv]
  | succ j ih =>
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j u) x :=
      hu.contDiffAt.differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl j)
    rw [hd.iteratedFDeriv_succ_apply_left']
    rw [List.ofFn_succ, iteratedPartialDeriv]
    simp only [EuclideanSpace.basisFun_apply] at ih ⊢
    change (∂[(v 0)] (fun y ↦ iteratedFDeriv ℝ j u y
        (fun i ↦ EuclideanSpace.single (v i.succ) (1 : ℝ)))) x =
      (∂[(v 0)] (iteratedPartialDeriv (List.ofFn fun i ↦ v i.succ) u)) x
    congr 1
    funext y
    exact ih (fun i ↦ v i.succ) y

/-- A mixed coordinate derivative is the partial-derivative word given by its
sorted multiindex tuple, so it can be computed by ordinary derivative calculations. -/
theorem coordinateDeriv_eq_iteratedPartialDeriv {n j : ℕ}
    {u : ℝ^n → ℝ} (hu : ContDiff ℝ ∞ u) (α : Sym (Fin n) j) (x : ℝ^n) :
    coordinateDeriv α u x = iteratedPartialDeriv (List.ofFn α.sortedTuple) u x :=
  iteratedFDeriv_basisFun_eq_iteratedPartialDeriv hu α.sortedTuple x

end PDE.Analysis.MultiIndex
