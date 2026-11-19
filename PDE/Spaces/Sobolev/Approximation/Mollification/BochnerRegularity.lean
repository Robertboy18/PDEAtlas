/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.HigherOrderRegularity
import PDE.Analysis.WeakCompactness.Operators

/-!
# Recovering Bochner Sobolev regularity from mollifications

A uniform higher-order bound for the mollifications produces a
higher-order Bochner class. Weak compactness supplies that class; strong
convergence of the lower-order mollifications identifies its underlying
function. This also proves measurability of the recovered graph.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Approximation

open Filter GraphSpace MeasureTheory Set
open PDE.Analysis PDE.Analysis.Evolution
open scoped ENNReal Topology Sobolev

variable {n r k : ℕ} {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- A uniform bound in a higher Sobolev order for a sequence of
mollifications gives a Bochner class in that order, with the original
lower-order graph as its restriction. No spatial compactness is needed. -/
theorem exists_higherOrder_Lp_of_bounded_mollifications
    (hrk : r ≤ k) (μ : Mollifier n)
    (δ : ℕ → ℝ) (hδ : ∀ j, 0 < δ j) (hδ0 : Tendsto δ atTop (𝓝 0))
    (u : Lp (W^{r,2}(ℝ^n)) 2 ν)
    (hbound : Bornology.IsBounded (range (fun j ↦
      ((mollifierSmoothingCLM k μ (hδ j)).comp
        (wkpBaseCoordinateCLM : W^{r,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL 2 ν u))) :
    ∃ v : Lp (W^{k,2}(ℝ^n)) 2 ν,
      (lowerOrderCLM (n := n) (p := 2) hrk).compLpL 2 ν v = u := by
  let S (j : ℕ) : W^{r,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
    (mollifierSmoothingCLM k μ (hδ j)).comp wkpBaseCoordinateCLM
  let y (j : ℕ) : Lp (W^{k,2}(ℝ^n)) 2 ν := (S j).compLpL 2 ν u
  let B : W^{k,2}(ℝ^n) →L[ℝ] W^{r,2}(ℝ^n) := lowerOrderCLM hrk
  have hBy (j : ℕ) :
      B.compLpL 2 ν (y j) = (mollifierHkCLM (k := r) μ (hδ j)).compLpL 2 ν u := by
    apply Lp.ext
    filter_upwards [B.coeFn_compLpL (y j), (S j).coeFn_compLpL u,
      (mollifierHkCLM (k := r) μ (hδ j)).coeFn_compLpL u] with x hBx hSx hJx
    rw [hBx, hJx]
    change B ((S j).compLpL 2 ν u x) = _
    rw [hSx]
    exact (lowerOrderCLM_mollifierSmoothingCLM hrk μ (hδ j) _).trans
      (mollifierSmoothingCLM_baseCoordinate μ (hδ j) (u x))
  have hstrong : Tendsto (fun j ↦ B.compLpL 2 ν (y j)) atTop (𝓝 u) := by
    simp only [hBy]
    apply tendsto_compLpL_of_tendsto_strongly
      (fun j ↦ mollifierHkCLM (k := r) μ (hδ j)) 1 zero_le_one
    · intro j U
      simpa only [one_mul] using norm_mollifierHkCLM_apply_le μ (hδ j) U
    · exact tendsto_mollifierHkCLM μ δ hδ hδ0
  have hex := WeakCompactness.exists_preimage_of_isBounded_range_of_tendsto
    (H := Lp (W^{k,2}(ℝ^n)) 2 ν) (X := Lp (W^{r,2}(ℝ^n)) 2 ν)
    (ι := ℕ) (l := atTop)
  have hB := hex (B.compLpL 2 ν)
  exact hB y hbound hstrong

end SobolevSpace.Approximation
