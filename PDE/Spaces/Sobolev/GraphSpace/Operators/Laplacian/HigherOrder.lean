/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian
public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder

/-!
# The weak Laplacian between higher-order Sobolev spaces

The operator is the sum of the derivative-word maps, so it retains all
weak coordinates of the Laplacian. Order restriction and further weak
differentiation commute with it.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open scoped ENNReal Sobolev Laplacian

variable {n k r s : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- The weak Laplacian retaining derivatives through order `r`. -/
def higherOrderLaplacianCLM (h : r + 2 ≤ k) :
    W^{k,p}(Ω) →L[ℝ] W^{r,p}(Ω) :=
  ∑ i : Fin n, derivativeWordCLM [i, i] (by simpa [Nat.add_comm] using h)

/-- Each coordinate is the sum of its diagonal second weak derivatives. -/
theorem higherOrderLaplacianCLM_coordinate (h : r + 2 ≤ k)
    (U : W^{k,p}(Ω)) (a : DerivIndex n r) :
    (higherOrderLaplacianCLM h U : WkpAmbientOn n r p Ω) a =
      ∑ i : Fin n, (U : WkpAmbientOn n k p Ω)
        (derivativeWordIndex [i, i] (by simpa [Nat.add_comm] using h) a) := by
  simp [higherOrderLaplacianCLM, derivativeWordCLM_apply]

/-- The base of the higher-order Laplacian agrees with the `W^{2,p}`-to-Lᵖ
Laplacian after order restriction. -/
theorem higherOrderLaplacianCLM_base (h : r + 2 ≤ k) (U : W^{k,p}(Ω)) :
    wkpBaseCoordinateCLM (higherOrderLaplacianCLM h U) =
      Δ (lowerOrderCLM (show 2 ≤ k by omega) U) := by
  simp [wkpBaseCoordinateCLM_apply, higherOrderLaplacianCLM_coordinate,
    wkpLaplacianCLM_apply, derivIndexOfList_pair,
    DerivIndex.castOrder_pairDerivIndex]

/-- Forgetting some output derivatives commutes with the Laplacian. -/
theorem lowerOrderCLM_higherOrderLaplacianCLM (hrs : s ≤ r) (h : r + 2 ≤ k)
    (U : W^{k,p}(Ω)) :
    lowerOrderCLM hrs (higherOrderLaplacianCLM h U) =
      higherOrderLaplacianCLM (show s + 2 ≤ k by omega) U := by
  simp only [higherOrderLaplacianCLM, sum_apply, map_sum,
    lowerOrderCLM_derivativeWordCLM_apply]

/-- Weak derivative words commute with the Laplacian, without additional
regularity or a choice of classical representatives. -/
theorem derivativeWordCLM_higherOrderLaplacianCLM
    (α : List (Fin n)) (hα : α.length + s ≤ r) (h : r + 2 ≤ k)
    (U : W^{k,p}(Ω)) :
    derivativeWordCLM α hα (higherOrderLaplacianCLM h U) =
      higherOrderLaplacianCLM (show s + 2 ≤ k - α.length by omega)
        (derivativeWordCLM α (show α.length + (k - α.length) ≤ k by omega) U) := by
  simp only [higherOrderLaplacianCLM, sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivativeWordCLM_comp [i, i] _ α _ (by simpa using (by omega :
    α.length + 2 + s ≤ k)), derivativeWordCLM_comp α _ [i, i] _
    (by simpa using (by omega : α.length + 2 + s ≤ k))]
  apply Subtype.ext
  apply PiLp.ext
  intro a
  simp only [derivativeWordCLM_apply]
  exact congrArg (fun b : DerivIndex n k ↦ (U : WkpAmbientOn n k p Ω) b)
    (derivativeWordIndex_eq_of_perm _ _ _ _ _ _
      (List.perm_append_comm.append_right a.toList))

end SobolevSpace.GraphSpace
