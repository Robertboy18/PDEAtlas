/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.HigherOrder

/-!
# Assembling a Sobolev graph from its highest derivatives

Local regularity estimates often recover just the derivatives of the next order.
The lower rows already belong to the original Sobolev graph. Keeping those rows
and adjoining the recovered ones gives the next graph, with the same base function.
The norm estimate uses the finite row-count bound.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory

/-- An Hk graph and uniformly bounded L² weak derivatives of order k+1 give an
H(k+1) graph with the same base. The estimate keeps the original graph norm
and the bound for the new rows separate. -/
theorem exists_succ_order_of_top_derivatives
    {n k : ℕ} {Ω : Set ℝ^n} (U : W^{k,2}(Ω)) {C : ℝ} (hC : 0 ≤ C)
    (htop : ∀ α : List (Fin n), α.length = k + 1 →
      ∃ v : DerivLp n 2 Ω, ‖v‖ ≤ C ∧ HasWeakDerivativeOn Ω α (baseRepresentative U) v) :
    ∃ W : W^{k + 1,2}(Ω),
      baseRepresentative W =ᵐ[domainMeasure n Ω] baseRepresentative U ∧
      ‖W‖ ≤ succOrderAssemblyNormBound n k * (‖U‖ + C) := by
  classical
  let row (a : DerivIndex n (k + 1)) : DerivLp n 2 Ω :=
    if ha : a.toList.length ≤ k then
      (U : WkpAmbientOn n k 2 Ω) (derivIndexOfList a.toList ha)
    else
      (htop a.toList (by have := a.toList_length_le; omega)).choose
  have hbase : row (baseIndex n (k + 1)) =
      (U : WkpAmbientOn n k 2 Ω) (baseIndex n k) := by
    dsimp only [row]
    rw [dite_eq_left (by rw [baseIndex_toList]; simp)]
    simp only [baseIndex_toList, derivIndexOfList_nil]
  have hweak (a : DerivIndex n (k + 1)) :
      HasWeakDerivativeOn Ω a.toList (baseRepresentative U) (row a) := by
    dsimp only [row]
    split_ifs with ha
    · exact U.property.hasWeakDerivativeOn_list a.toList ha
    · exact (htop a.toList (by have := a.toList_length_le; omega)).choose_spec.2
  have hrow (a : DerivIndex n (k + 1)) : ‖row a‖ ≤ ‖U‖ + C := by
    dsimp only [row]
    split_ifs with ha
    · exact (PiLp.norm_apply_le (U : WkpAmbientOn n k 2 Ω) _).trans
        (le_add_of_nonneg_right hC)
    · exact (htop a.toList (by have := a.toList_length_le; omega)).choose_spec.1.trans
        (le_add_of_nonneg_left (norm_nonneg U))
  let V : WkpAmbientOn n (k + 1) 2 Ω := WithLp.toLp 2 row
  have hV : IsWkpOn V := by
    intro a
    change HasWeakDerivativeOn Ω a.toList (row (baseIndex n (k + 1))) (row a)
    rw [hbase]
    exact hweak a
  let W : W^{k + 1,2}(Ω) := ⟨V, hV⟩
  refine ⟨W, ?_, ?_⟩
  · change (row (baseIndex n (k + 1)) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] _
    rw [hbase]
    exact Filter.EventuallyEq.rfl
  · have hsum : ∑ a : DerivIndex n (k + 1), ‖row a‖ ^ 2 ≤
        (Fintype.card (DerivIndex n (k + 1)) : ℝ) * (‖U‖ + C) ^ 2 := by
      calc
        _ ≤ ∑ _a : DerivIndex n (k + 1), (‖U‖ + C) ^ 2 :=
          Finset.sum_le_sum fun a _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hrow a) 2
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change ‖V‖ ≤ _
    rw [PiLp.norm_eq_of_L2, succOrderAssemblyNormBound]
    apply (Real.sqrt_le_sqrt hsum).trans_eq
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (add_nonneg (norm_nonneg _) hC)]

end SobolevSpace.GraphSpace
