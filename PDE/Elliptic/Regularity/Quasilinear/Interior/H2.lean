/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.Regularity.Quasilinear.Interior.Gradient
public import PDE.Spaces.Sobolev.Calculus.Differentiation.SecondDerivatives.Assembly

/-!
# Interior H² regularity for monotone Lipschitz equations

The constructed gradient fields supply the second weak derivatives.
The order-one restriction is exactly the original solution's
restriction. Both the full Sobolev norm and the sum of all ordered
second-derivative norms are bounded uniformly before the equation data
are chosen. The latter also controls the Euclidean Hessian norm.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω V : Set (ℝ^n)}

/-- Every `H¹` weak solution of an autonomous strongly monotone
Lipschitz divergence equation has interior `H²` regularity. There is no
boundary condition on the solution, and the estimate constant is
independent of its trace and of the flux's constant part. -/
theorem exists_interior_H2_of_monotone_weakEquation
    (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    {m C : ℝ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : ℝ^n → ℝ^n),
      (∀ z w, m * ‖z - w‖ * ‖z - w‖ ≤ ⟪A z - A w, z - w⟫) →
      (∀ z w, ‖A z - A w‖ ≤ C * ‖z - w‖) →
      ∀ (u : H¹(Ω)) (q : Fin n → DerivLp n 2 Ω) (f : DerivLp n 2 Ω),
      (∀ᵐ x ∂domainMeasure n Ω,
        A (Lp.euclideanTuple (fun i ↦ u.val (singleDerivIndex n i)) x) =
          Lp.euclideanTuple q x) →
      (∀ v : H¹₀(Ω), (∑ i, ⟪q i, derivCoordCLM i v⟫) = ⟪f, baseCoordCLM v⟫) →
      ∃ W : W^{2,2}(V),
        lowerOrderCLM (by omega : 1 ≤ 2) W =
          restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u ∧
        ‖W‖ ≤ K * (‖u‖ + ‖f‖) ∧
        (∑ i : Fin n, ∑ j : Fin n, ‖W.val (pairDerivIndex n i j)‖) ≤
          K * (‖∇ u‖ + ‖f‖) := by
  obtain ⟨B, hB, hgrad⟩ :=
    exists_interior_gradient_of_monotone_weakEquation (C := C) hΩ hV hVc hVΩ hm
  let d : ℝ := Fintype.card (DerivIndex n 2)
  let H := d * (1 + n * B * (n + 1))
  let J := (n : ℝ) ^ 2 * B
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hJ : 0 ≤ J := mul_nonneg (sq_nonneg _) hB.le
  refine ⟨1 + H + J, by positivity, ?_⟩
  intro A hmono hLip u q f hrep hweak
  obtain ⟨G, hbase, hG⟩ := hgrad A hmono hLip u q f hrep hweak
  let U := restrictCLM hV.measurableSet (subset_closure.trans hVΩ) u
  have hbase' (i : Fin n) : (G i).val (baseIndex n 1) = U.val (singleDerivIndex n i) :=
    hbase i
  obtain ⟨W, hW, hsecond, hnorm⟩ := exists_H2_of_gradient_H1 U G hbase'
  refine ⟨W, hW, ?_, ?_⟩
  · have hsum : (∑ i, ‖∇ (G i)‖) ≤
        n * (B * (‖f‖ + ‖∇ u‖)) := by
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hG i)
    have hdata : ‖f‖ + ‖∇ u‖ ≤ (n + 1) * (‖u‖ + ‖f‖) := by
      nlinarith [wkpGradientCLM_norm_le u, norm_nonneg u,
        mul_nonneg (Nat.cast_nonneg n) (norm_nonneg f)]
    have hsmall : ‖W‖ ≤ H * (‖u‖ + ‖f‖) := by
      apply hnorm.trans
      calc
        _ ≤ d * (‖u‖ + n * (B * (‖f‖ + ‖∇ u‖))) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (norm_restrictCLM_apply_le _ _ u) hsum) hd
        _ ≤ d * ((‖u‖ + ‖f‖) + n * (B * ((n + 1) * (‖u‖ + ‖f‖)))) := by
          have := hB.le
          gcongr
          exact le_add_of_nonneg_right (norm_nonneg _)
        _ = _ := by dsimp only [H]; ring
    exact hsmall.trans (mul_le_mul_of_nonneg_right
      (by linarith : H ≤ 1 + H + J) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  · have hcoord (a : DerivIndex n 2) (ha : a.toList.length = 2) :
        ‖W.val a‖ ≤ B * (‖f‖ + ‖∇ u‖) := by
      obtain ⟨i, j, hij⟩ := List.length_eq_two.mp ha
      rw [hsecond a i j hij]
      exact (norm_derivCoordinate_le_wkpGradientCLM (G i) j).trans (hG i)
    have hpairs (i j : Fin n) :
        ‖W.val (pairDerivIndex n i j)‖ ≤ B * (‖f‖ + ‖∇ u‖) :=
      hcoord _ (by simpa using (pairDerivIndex_toList_perm i j).length_eq)
    have hsum : (∑ i : Fin n, ∑ j : Fin n, ‖W.val (pairDerivIndex n i j)‖) ≤
        J * (‖∇ u‖ + ‖f‖) := by
      calc
        _ ≤ ∑ _ : Fin n, ∑ _ : Fin n, B * (‖f‖ + ‖∇ u‖) :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpairs i j
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]; dsimp only [J]; ring
    exact hsum.trans (mul_le_mul_of_nonneg_right
      (by linarith : J ≤ 1 + H + J) (add_nonneg (norm_nonneg _) (norm_nonneg _)))

end PDE.Elliptic.Regularity.Quasilinear
