/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Laplacian.HigherOrder
public import PDE.Spaces.Sobolev.GraphSpace.Norms.Hessian
import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder

/-!
# Whole-space Sobolev integration by parts

Density identifies H¹ with H¹₀ on the whole space. Thus integration by parts
needs neither compact support of the functions nor pointwise decay at infinity.
Applying it to derivative coordinates gives the dissipation of the weak
Laplacian in every Hilbert Sobolev graph.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal InnerProductSpace Sobolev Laplacian

variable {n k r : ℕ}

/-- On the whole space, a weak L² derivative can be tested against any H¹ field. -/
theorem weakDerivative_integrationByParts_H1_univ (i : Fin n)
    (f g : DerivLp n 2 Set.univ)
    (hfg : HasWeakDerivativeOn Set.univ [i] (f : ℝ^n → ℝ) (g : ℝ^n → ℝ))
    (V : W^{1,2}(ℝ^n)) :
    ⟪f, wkpCoordinateCLM (singleDerivIndex n i) V⟫_ℝ =
      -⟪g, wkpBaseCoordinateCLM V⟫_ℝ := by
  have hV : V ∈ (h10SubmoduleOn (n := n) (Ω := Set.univ)).toSubmodule := by
    simpa [h10SubmoduleOn] using wkpSpace_mem_Wkp0_univ (by norm_num) V
  simpa [derivCoordCLM, baseCoordCLM] using
    weakDerivative_integrationByParts_H10 i f g hfg ⟨V, hV⟩

/-- Moving one of two equal coordinate derivatives to the other factor gives
the negative square of the intervening derivative. -/
theorem inner_coordinate_second_eq_neg_norm_sq (U : W^{k,2}(ℝ^n))
    (α : List (Fin n)) (hα : α.length + 2 ≤ k) (i : Fin n) :
    ⟪(U : WkpAmbientOn n k 2 Set.univ) (derivIndexOfList α (by omega)),
      (U : WkpAmbientOn n k 2 Set.univ)
        (derivIndexOfList (α ++ [i, i]) (by simpa using hα))⟫_ℝ =
      -‖(U : WkpAmbientOn n k 2 Set.univ)
        (derivIndexOfList (α ++ [i]) (by
          simp only [List.length_append, List.length_singleton]
          omega))‖ ^ 2 := by
  let V : W^{1,2}(ℝ^n) := derivativeWordCLM α (by omega) U
  have hw := U.property.hasWeakDerivativeOn_from_coordinate (α ++ [i]) [i]
    (by
      simp only [List.length_append, List.length_singleton]
      omega)
  have hparts := weakDerivative_integrationByParts_H1_univ i _ _ hw V
  have hparts' :
      ‖(U : WkpAmbientOn n k 2 Set.univ)
        (derivIndexOfList (α ++ [i]) (by
          simp only [List.length_append, List.length_singleton]
          omega))‖ ^ 2 =
      -⟪(U : WkpAmbientOn n k 2 Set.univ)
          (derivIndexOfList (α ++ [i, i]) (by simpa using hα)),
        (U : WkpAmbientOn n k 2 Set.univ) (derivIndexOfList α (by omega))⟫_ℝ := by
    simpa [V, wkpBaseCoordinateCLM_apply, derivativeWordCLM_apply,
      List.append_assoc, real_inner_self_eq_norm_sq] using hparts
  rw [real_inner_comm]
  exact neg_eq_iff_eq_neg.mp hparts'.symm

/-- The L² pairing with the weak Laplacian is the negative full
gradient energy, without a boundary or support hypothesis on ℝⁿ. -/
theorem inner_base_laplacian_eq_neg_gradient (U : W^{2,2}(ℝ^n)) :
    ⟪wkpBaseCoordinateCLM U, Δ U⟫_ℝ =
      -∑ i : Fin n, ‖(U : WkpAmbientOn n 2 2 Set.univ)
        (firstDerivIndex n 2 (by omega) i)‖ ^ 2 := by
  rw [laplacian_eq_wkpLaplacianCLM, wkpLaplacianCLM_apply, inner_sum,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [List.nil_append, derivIndexOfList_nil, derivIndexOfList_pair,
    secondDerivIndex_two, derivIndexOfList_singleton, wkpBaseCoordinateCLM_apply] using
    inner_coordinate_second_eq_neg_norm_sq U [] (by simp) i

/-- The weak Laplacian dissipates every Hilbert Sobolev graph norm.
The derivative energy uses the graph's symmetric multiindices. -/
theorem inner_higherOrderLaplacianCLM (h : r + 2 ≤ k) (U : W^{k,2}(ℝ^n)) :
    ⟪lowerOrderCLM (show r ≤ k by omega) U, higherOrderLaplacianCLM h U⟫_ℝ =
      -(∑ a : DerivIndex n r, ∑ i : Fin n,
        ‖(U : WkpAmbientOn n k 2 Set.univ)
          (derivIndexOfList (a.toList ++ [i]) (by
            simp only [List.length_append, List.length_singleton]
            have := a.toList_length_le
            omega))‖ ^ 2) := by
  change inner ℝ (lowerOrderCLM (show r ≤ k by omega) U).val
    (higherOrderLaplacianCLM h U).val = _
  rw [PiLp.inner_apply, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [higherOrderLaplacianCLM_coordinate, inner_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have ha : a.toList.length + 2 ≤ k := by
    have := a.toList_length_le
    omega
  have hbase : a.castOrder (show r ≤ k by omega) =
      derivIndexOfList a.toList (show a.toList.length ≤ k by omega) := by
    exact (derivIndexOfList_toList (a.castOrder (by omega)) _).symm
  have hsecond :
      derivativeWordIndex [i, i] (show [i, i].length + r ≤ k by simpa [Nat.add_comm])
        a = derivIndexOfList (a.toList ++ [i, i]) (by simpa using ha) := by
    apply derivIndexOfList_eq_of_perm
    exact List.perm_append_comm
  rw [lowerOrderCLM_apply, hbase, hsecond]
  exact inner_coordinate_second_eq_neg_norm_sq U a.toList ha i

/-- In H¹, the dissipated energy is the sum of the full gradient and the
ordered Hessian energies, including both orders of each mixed derivative. -/
theorem inner_hOne_laplacian_eq_neg_gradient_hessian (U : W^{3,2}(ℝ^n)) :
    ⟪lowerOrderCLM (show 1 ≤ 3 by omega) U,
      higherOrderLaplacianCLM (show 1 + 2 ≤ 3 by omega) U⟫_ℝ =
      -((∑ i : Fin n, ‖(U : WkpAmbientOn n 3 2 Set.univ)
          (firstDerivIndex n 3 (by omega) i)‖ ^ 2) +
        ∑ i : Fin n, ∑ j : Fin n, ‖(U : WkpAmbientOn n 3 2 Set.univ)
          (secondDerivIndex n 3 (by omega) i j)‖ ^ 2) := by
  simpa only [sum_derivIndex_one, baseIndex_toList, singleDerivIndex_toList,
    List.nil_append, List.cons_append, derivIndexOfList_singleton, derivIndexOfList_pair]
    using inner_higherOrderLaplacianCLM (show 1 + 2 ≤ 3 by omega) U

/-- For diffusivity at most one, the squared L² diffusion term is bounded by
the H¹ dissipation. This uses the ordered Hessian, without identifying it
with the H² graph norm. -/
theorem norm_smul_laplacian_sq_le_hOne_dissipation
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (U : W^{3,2}(ℝ^n)) :
    ‖ε • wkpBaseCoordinateCLM
      (higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) U)‖ ^ 2 ≤
    (n : ℝ) * (-(2 * ε) *
      ⟪lowerOrderCLM (by decide : 1 ≤ 3) U,
        higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) U⟫_ℝ) := by
  let H := ∑ i : Fin n, ∑ j : Fin n, ‖(U : WkpAmbientOn n 3 2 Set.univ)
    (secondDerivIndex n 3 (by decide) i j)‖ ^ 2
  let D := ∑ i : Fin n, ‖(U : WkpAmbientOn n 3 2 Set.univ)
    (firstDerivIndex n 3 (by decide) i)‖ ^ 2
  have hH : 0 ≤ H :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hlap : ‖Δ (lowerOrderCLM (by decide : 2 ≤ 3) U)‖ ^ 2 ≤
      (n : ℝ) * H := by
    exact norm_wkpLaplacianCLM_sq_le_hessian (lowerOrderCLM (by decide : 2 ≤ 3) U)
  rw [higherOrderLaplacianCLM_base, norm_smul, Real.norm_eq_abs, abs_of_nonneg hε,
    mul_pow, inner_hOne_laplacian_eq_neg_gradient_hessian]
  change ε ^ 2 * ‖Δ (lowerOrderCLM (by decide : 2 ≤ 3) U)‖ ^ 2 ≤
    (n : ℝ) * (-(2 * ε) * -(D + H))
  calc
    _ ≤ ε ^ 2 * ((n : ℝ) * H) := mul_le_mul_of_nonneg_left hlap (sq_nonneg ε)
    _ ≤ (2 * ε) * ((n : ℝ) * H) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg (Nat.cast_nonneg n) hH)
    _ ≤ (2 * ε) * ((n : ℝ) * (D + H)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hD) (Nat.cast_nonneg n))
        (mul_nonneg (by norm_num) hε)
    _ = _ := by ring

end SobolevSpace.GraphSpace
