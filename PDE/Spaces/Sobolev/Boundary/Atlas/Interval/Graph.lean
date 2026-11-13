/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Geometric.GraphBoundary
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Smooth graph geometry of arbitrary coordinate intervals

In one dimension the tangential space is zero-dimensional. Constant graph
heights and reversal of the normal coordinate give the two endpoint charts
for every nonempty bounded interval.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Boundary.Atlas.Interval

open Filter Set Trace.HalfSpace
open scoped Topology

/-- Every frontier point of an open coordinate interval is an endpoint. -/
theorem eq_endpoint_of_mem_frontier_Ioo {a b : ℝ} {x : ℝ^1}
    (hx : x ∈ frontier {y : ℝ^1 | a < y 0 ∧ y 0 < b}) :
    x 0 = a ∨ x 0 = b := by
  have hopen : IsOpen {y : ℝ^1 | a < y 0 ∧ y 0 < b} :=
    isOpen_Ioo.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous
  have hclosed : IsClosed {y : ℝ^1 | a ≤ y 0 ∧ y 0 ≤ b} :=
    isClosed_Icc.preimage (EuclideanSpace.proj (0 : Fin 1)).continuous
  have hbounds : a ≤ x 0 ∧ x 0 ≤ b :=
    closure_minimal (show {y : ℝ^1 | a < y 0 ∧ y 0 < b} ⊆
      {y : ℝ^1 | a ≤ y 0 ∧ y 0 ≤ b} from fun _ hy ↦ ⟨hy.1.le, hy.2.le⟩)
      hclosed (frontier_subset_closure hx)
  rw [hopen.frontier_eq] at hx
  by_cases ha : x 0 = a
  · exact Or.inl ha
  · exact Or.inr (le_antisymm hbounds.2
      (le_of_not_gt (fun hb ↦ hx.2 ⟨lt_of_le_of_ne hbounds.1 (Ne.symm ha), hb⟩)))

/-- A nonempty coordinate interval has smooth graph boundary at every
finite or infinite order, including the zero-dimensional tangential case. -/
theorem hasContDiffGraphBoundary_Ioo {a b : ℝ} (hab : a < b) (k : ℕ∞) :
    HasContDiffGraphBoundary k {x : ℝ^1 | a < x 0 ∧ x 0 < b} := by
  intro x hx
  let e : ℝ^1 ≃L[ℝ] (ℝ^0 × ℝ) := tangentialNormalContinuousLinearEquiv
  have he (y : ℝ^1) : (e y).2 = y 0 := rfl
  obtain ha | hb := eq_endpoint_of_mem_frontier_Ioo hx
  · refine ⟨e, fun _ ↦ a, univ, isOpen_univ, mem_univ _, contDiffOn_const, ?_, ?_⟩
    · exact (he x).trans ha
    · have hlt : ∀ᶠ y in 𝓝 x, y 0 < b :=
        (EuclideanSpace.proj (0 : Fin 1)).continuous.continuousAt.eventually_lt
          continuousAt_const (show x 0 < b by rw [ha]; exact hab)
      filter_upwards [hlt] with y hy
      change (a < y 0 ∧ y 0 < b) ↔ a < (e y).2
      rw [he]
      exact and_iff_left hy
  · let d := (LinearIsometryEquiv.neg ℝ : ℝ^1 ≃ₗᵢ[ℝ] ℝ^1
      ).toContinuousLinearEquiv.trans e
    have hd (y : ℝ^1) : (d y).2 = -y 0 := rfl
    refine ⟨d, fun _ ↦ -b, univ, isOpen_univ, mem_univ _, contDiffOn_const, ?_, ?_⟩
    · rw [hd, hb]
    · have hlt : ∀ᶠ y in 𝓝 x, a < y 0 :=
        continuousAt_const.eventually_lt
          (EuclideanSpace.proj (0 : Fin 1)).continuous.continuousAt
          (show a < x 0 by rw [hb]; exact hab)
      filter_upwards [hlt] with y hy
      change (a < y 0 ∧ y 0 < b) ↔ -b < (d y).2
      rw [hd, neg_lt_neg_iff]
      exact and_iff_right hy

end SobolevSpace.Boundary.Atlas.Interval
