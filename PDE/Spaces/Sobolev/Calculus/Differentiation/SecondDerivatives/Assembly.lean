/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.SecondDerivatives
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Second-order assembly from first-order derivative fields

First-order Sobolev fields representing the gradient coordinates supply
second weak derivatives. Assembly preserves the entire original
first-order bundle, and its norm bound uses the gradients of the
derivative fields. No boundary or dimension hypothesis is needed.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Assemble first-order gradient fields into the second-order bundle.
Order restriction is an equality of Sobolev elements, and every
stored second coordinate is a derivative of its first field. -/
theorem exists_H2_of_gradient_H1
    (U : H¹(Ω)) (W : Fin n → H¹(Ω))
    (hW : ∀ i, (W i).val (baseIndex n 1) = U.val (singleDerivIndex n i)) :
    ∃ V : W^{2,2}(Ω),
      lowerOrderCLM (by omega : 1 ≤ 2) V = U ∧
      (∀ (a : DerivIndex n 2) (i j : Fin n), a.toList = [i, j] →
        V.val a = (W i).val (singleDerivIndex n j)) ∧
      ‖V‖ ≤ Fintype.card (DerivIndex n 2) *
        (‖U‖ + ∑ i, ‖∇ (W i)‖) := by
  let g (i j : Fin n) : ℝ^n → ℝ := (W i).val (singleDerivIndex n j)
  have hweak (i j : Fin n) :
      HasWeakDerivativeOn Ω [j] (U.val (singleDerivIndex n i) : ℝ^n → ℝ) (g i j) := by
    rw [← hW]
    simpa only [singleDerivIndex_toList] using (W i).property (singleDerivIndex n j)
  obtain ⟨V, hbase, hfirst, hsecond, _⟩ := exists_H2_of_firstDerivatives_haveWeakDerivatives
    U g (fun i j ↦ Lp.memLp _) hweak
  refine ⟨V, ?_, (fun a i j ha ↦ Lp.ext (hsecond a i j ha)), ?_⟩
  · apply Subtype.ext
    apply PiLp.ext
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex] using Lp.ext hbase
    · simpa only [lowerOrderCLM_apply, DerivIndex.castOrder_singleDerivIndex] using
        Lp.ext (hfirst i)
  · let M := ‖U‖ + ∑ i, ‖∇ (W i)‖
    have hsum : 0 ≤ ∑ i, ‖∇ (W i)‖ :=
      Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have hcoord (a : DerivIndex n 2) : ‖V.val a‖ ≤ M := by
      refine a.inductionOnOrderTwo (motive := fun b ↦ ‖V.val b‖ ≤ M) ?_ ?_ ?_
      · rw [Lp.ext hbase]
        exact (wkpCoordinateCLM_norm_le (baseIndex n 1) U).trans
          (le_add_of_nonneg_right hsum)
      · intro i
        rw [Lp.ext (hfirst i)]
        exact (wkpCoordinateCLM_norm_le (singleDerivIndex n i) U).trans
          (le_add_of_nonneg_right hsum)
      · intro a i j ha
        rw [Lp.ext (hsecond a i j ha)]
        have hi : ‖∇ (W i)‖ ≤ ∑ k, ‖∇ (W k)‖ :=
          Finset.single_le_sum (fun k _ ↦ norm_nonneg (∇ (W k)))
            (Finset.mem_univ i)
        exact (norm_derivCoordinate_le_wkpGradientCLM (W i) j).trans
          (hi.trans (le_add_of_nonneg_left (norm_nonneg U)))
    calc
      ‖V‖ ≤ ∑ a : DerivIndex n 2, ‖V.val a‖ := PiLp.norm_le_sum_norm V.val
      _ ≤ ∑ _ : DerivIndex n 2, M := Finset.sum_le_sum fun a _ ↦ hcoord a
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rfl

end SobolevSpace.GraphSpace
