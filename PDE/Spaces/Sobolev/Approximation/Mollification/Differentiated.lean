/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.HigherOrderRegularity
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian.HigherOrder

/-!
# Differentiation of the mollifier

At a fixed positive scale a differentiated mollifier is a bounded operator
on L². Its action on a weak derivative agrees with differentiating the
smoothed function. In particular it commutes with the weak Laplacian.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Approximation

open GraphSpace
open scoped ENNReal Sobolev Laplacian

variable {n k r s : ℕ}

/-- An arbitrary derivative of positive-scale mollification as an L² operator. -/
def differentiatedMollifierCLM (α : List (Fin n)) (μ : Mollifier n)
    {δ : ℝ} (hδ : 0 < δ) : DerivLp n 2 Set.univ →L[ℝ] DerivLp n 2 Set.univ :=
  (wkpCoordinateCLM (derivIndexOfList α le_rfl)).comp
    (mollifierSmoothingCLM α.length μ hδ)

/-- The output coordinate is independent of how many additional derivatives
are retained in the smoothed graph. -/
theorem differentiatedMollifierCLM_eq_coordinate
    (α : List (Fin n)) (hα : α.length ≤ k)
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ) (f : DerivLp n 2 Set.univ) :
    differentiatedMollifierCLM α μ hδ f =
      wkpCoordinateCLM (derivIndexOfList α hα) (mollifierSmoothingCLM k μ hδ f) := by
  have hh := congrArg
    (fun U : W^{α.length,2}(ℝ^n) ↦ wkpCoordinateCLM (derivIndexOfList α le_rfl) U)
    (lowerOrderCLM_mollifierSmoothingCLM hα μ hδ f)
  exact hh.symm

/-- On a Sobolev input, the differentiated convolution is the
mollification of its weak derivative coordinate. -/
theorem differentiatedMollifierCLM_baseCoordinate
    (α : List (Fin n)) (hα : α.length ≤ k)
    (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ) (U : W^{k,2}(ℝ^n)) :
    differentiatedMollifierCLM α μ hδ (wkpBaseCoordinateCLM U) =
      mollifierRowCLM μ hδ (wkpCoordinateCLM (derivIndexOfList α hα) U) := by
  rw [differentiatedMollifierCLM_eq_coordinate α hα,
    mollifierSmoothingCLM_baseCoordinate]
  rfl

/-- The higher weak Laplacian of the smoothing is the smoothing of the
L² weak Laplacian; no further regularity of the input is needed. -/
theorem higherOrderLaplacianCLM_mollifierSmoothingCLM
    (h : r + 2 ≤ s) (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ)
    (U : W^{2,2}(ℝ^n)) :
    higherOrderLaplacianCLM h
        (mollifierSmoothingCLM s μ hδ (wkpBaseCoordinateCLM U)) =
      mollifierSmoothingCLM r μ hδ (Δ U) := by
  simp only [higherOrderLaplacianCLM, sum_apply, laplacian_eq_wkpLaplacianCLM,
    wkpLaplacianCLM_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact derivativeWordCLM_mollifierSmoothingCLM [i, i] (by simp)
    (by simpa [Nat.add_comm] using h) μ hδ U

/-- A first differentiated mollifier commutes with the H² weak Laplacian.
The right-hand side has two weak derivatives because it is smoothed. -/
theorem differentiatedMollifierCLM_laplacian
    (i : Fin n) (μ : Mollifier n) {δ : ℝ} (hδ : 0 < δ) (U : W^{2,2}(ℝ^n)) :
    differentiatedMollifierCLM [i] μ hδ (Δ U) =
      Δ (mollifierSmoothingCLM 2 μ hδ
        (wkpCoordinateCLM (derivIndexOfList [i] (by simp)) U)) := by
  let S := mollifierSmoothingCLM 3 μ hδ (wkpBaseCoordinateCLM U)
  have hS : higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) S =
      mollifierSmoothingCLM 1 μ hδ (Δ U) :=
    higherOrderLaplacianCLM_mollifierSmoothingCLM _ μ hδ U
  have hD := derivativeWordCLM_higherOrderLaplacianCLM
    [i] (by simp : [i].length + 0 ≤ 1) (by decide : 1 + 2 ≤ 3) S
  have hh := congrArg (wkpBaseCoordinateCLM (n := n) (m := 0) (p := 2)) hD
  rw [higherOrderLaplacianCLM_base, hS] at hh
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub] at hh
  rw [lowerOrderCLM_refl_apply (k := 2) (n := n) (p := 2)] at hh
  dsimp only [S] at hh
  rw [derivativeWordCLM_mollifierSmoothingCLM (r := 2) (s := 3) (k := 2)
    [i] (by simp)] at hh
  simpa only [laplacian_eq_wkpLaplacianCLM, differentiatedMollifierCLM,
    ContinuousLinearMap.comp_apply,
    wkpBaseCoordinateCLM_apply, derivativeWordCLM_apply, derivativeWordIndex_baseIndex,
    wkpCoordinateCLM_apply, List.length_cons, List.length_nil, Nat.reduceAdd] using hh

end SobolevSpace.Approximation
