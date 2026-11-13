/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
import PDE.Analysis.Variational.LaxMilgram
import Mathlib.Algebra.Order.Chebyshev

/-!
# Comparison with a homogeneous elliptic solution

On a bounded open set, replace a weak solution by the homogeneous solution for a
second uniformly elliptic coefficient field in the same affine `H¹₀` class.
Testing the correction equation with the correction bounds its gradient by the
flux residual. The bound contains no Poincaré or domain constant.

This is the energy comparison used when freezing coefficients in an interior
Schauder argument. Both fields may be merely measurable; continuity is needed
only when subsequently estimating their difference on small balls.
-/

@[expose] public noncomputable section

open scoped Sobolev InnerProductSpace ENNReal

namespace SobolevSpace.GraphSpace

open PDE.Analysis.Variational

variable {n : ℕ} {Ω : Set ℝ^n}

private theorem sum_norm_sq_le_of_energy
    (q d : Fin n → DerivLp n 2 Ω) {α : ℝ} (hα : 0 < α)
    (henergy : α * ∑ i, ‖d i‖ ^ 2 ≤ ∑ i, ⟪q i, d i⟫_ℝ) :
    α ^ 2 * ∑ i, ‖d i‖ ^ 2 ≤ ∑ i, ‖q i‖ ^ 2 := by
  have hyoung (i : Fin n) :
      2 * α * ⟪q i, d i⟫_ℝ ≤ ‖q i‖ ^ 2 + α ^ 2 * ‖d i‖ ^ 2 := by
    have h : 0 ≤ ⟪q i - α • d i, q i - α • d i⟫_ℝ := real_inner_self_nonneg
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
      Real.norm_eq_abs, abs_of_pos hα] at h
    rw [real_inner_comm (q i) (d i)] at h
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hyoung i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hscaled := mul_le_mul_of_nonneg_left henergy hα.le
  nlinarith

/-- The flux residual is small when each coefficient entry is small in `L∞`.
The dimension factor comes from the Euclidean norm of a matrix with bounded entries. -/
theorem sum_norm_fluxResidual_sq_le
    (c : Fin n → Fin n → DerivLp n ∞ Ω) (F d : Fin n → DerivLp n 2 Ω)
    {ε : ℝ} (hc : ∀ i j, ‖c i j‖ ≤ ε) :
    (∑ i, ‖F i + ∑ j, (c i j • d j : DerivLp n 2 Ω)‖ ^ 2) ≤
      2 * ∑ i, ‖F i‖ ^ 2 + 2 * (n : ℝ) ^ 2 * ε ^ 2 * ∑ j, ‖d j‖ ^ 2 := by
  have hrow (i : Fin n) :
      ‖∑ j, (c i j • d j : DerivLp n 2 Ω)‖ ≤ ε * ∑ j, ‖d j‖ := by
    calc
      _ ≤ ∑ j, ‖(c i j • d j : DerivLp n 2 Ω)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ε * ‖d j‖ := Finset.sum_le_sum fun j _ ↦
        (MeasureTheory.Lp.norm_smul_le _ _).trans
          (mul_le_mul_of_nonneg_right (hc i j) (norm_nonneg _))
      _ = _ := (Finset.mul_sum ..).symm
  have hsum :
      (∑ j, ‖d j‖) ^ 2 ≤ (n : ℝ) * ∑ j, ‖d j‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin n))) (f := fun j ↦ ‖d j‖)
  have hrowSq (i : Fin n) :
      ‖∑ j, (c i j • d j : DerivLp n 2 Ω)‖ ^ 2 ≤
        (n : ℝ) * ε ^ 2 * ∑ j, ‖d j‖ ^ 2 := by
    calc
      _ ≤ (ε * ∑ j, ‖d j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
      _ = ε ^ 2 * (∑ j, ‖d j‖) ^ 2 := mul_pow ..
      _ ≤ ε ^ 2 * ((n : ℝ) * ∑ j, ‖d j‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg ε)
      _ = _ := by ring
  calc
    _ ≤ ∑ i, (2 * ‖F i‖ ^ 2 +
        2 * ((n : ℝ) * ε ^ 2 * ∑ j, ‖d j‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro i _
      let q : DerivLp n 2 Ω := ∑ j, (c i j • d j : DerivLp n 2 Ω)
      have hnonneg := sq_nonneg ‖F i - q‖
      rw [norm_sub_sq_real] at hnonneg
      rw [norm_add_sq_real]
      have hq := hrowSq i
      change ‖q‖ ^ 2 ≤ _ at hq
      nlinarith
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- A homogeneous comparison exists in the same affine `H¹₀` class, and the
gradient of its correction is controlled by the exact flux residual. Only the
comparison coefficients need to be elliptic; neither field needs continuity
or symmetry. The estimate is independent of the size and shape of the domain. -/
theorem exists_homogeneous_comparison
    (hn : 0 < n) (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (a b : Fin n → Fin n → DerivLp n ∞ Ω) {α : ℝ}
    (hb : AEUniformlyElliptic (n := n) (Ω := Ω) b α)
    (u : H¹(Ω)) (F : Fin n → DerivLp n 2 Ω)
    (hu : ∀ v : H¹₀(Ω),
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u v =
        ∑ i, ⟪F i, derivCoordCLM i v⟫_ℝ) :
    ∃ w : H¹₀(Ω),
      IsInteriorWeakDivergenceSolution b 0 (u - (w : H¹(Ω))) ∧
      α ^ 2 * ∑ i, ‖derivCoordCLM i w‖ ^ 2 ≤
        ∑ i, ‖F i + ∑ j, ((b i j - a i j) •
          wkpCoordinateCLM (singleDerivIndex n j) u : DerivLp n 2 Ω)‖ ^ 2 := by
  classical
  let B := variableCoeffForm (n := n) (Ω := Ω) (multiplicationCoefficientOperator b)
  have hB : IsCoercive B := variableCoeffForm_isCoercive hn hbounded _
    (integratedElliptic_multiplication_of_ae b hb)
  let ℓ := interiorVariableCoeffForm (multiplicationCoefficientOperator b) u
  let w : H¹₀(Ω) := solve (V := H¹₀(Ω)) B hB ℓ
  have hw := solve.isWeakSolution (V := H¹₀(Ω)) B hB ℓ
  refine ⟨w, ⟨hopen, ?_⟩, ?_⟩
  · intro v
    change interiorVariableCoeffForm (multiplicationCoefficientOperator b)
      (u - h10SubtypeL w) v = loadFunctional 0 v
    calc
      _ = ℓ v - interiorVariableCoeffForm (multiplicationCoefficientOperator b)
          (h10SubtypeL w) v := congrArg (fun t : H¹₀(Ω) →L[ℝ] ℝ ↦ t v)
        (map_sub (interiorVariableCoeffForm (multiplicationCoefficientOperator b))
          u (h10SubtypeL w))
      _ = ℓ v - B w v := by rw [interiorVariableCoeffForm_h10SubtypeL]
      _ = 0 := sub_eq_zero.mpr (hw v).symm
      _ = _ := by simp
  · apply sum_norm_sq_le_of_energy (n := n) (Ω := Ω)
      (fun i ↦ F i + ∑ j, ((b i j - a i j) •
        wkpCoordinateCLM (singleDerivIndex n j) u : DerivLp n 2 Ω))
      (fun i ↦ derivCoordCLM i w) hb.1
    have hell := (integratedElliptic_multiplication_of_ae b hb).2 w
    rw [dirichletForm_self_eq_sum_norm_sq] at hell
    apply hell.trans_eq
    rw [show variableCoeffForm (multiplicationCoefficientOperator b) w w = ℓ w from hw w]
    have hsub :
        ℓ w - interiorVariableCoeffForm (multiplicationCoefficientOperator a) u w =
          ∑ i, ⟪∑ j, ((b i j - a i j) •
            wkpCoordinateCLM (singleDerivIndex n j) u : DerivLp n 2 Ω),
              derivCoordCLM i w⟫_ℝ := by
      simp only [ℓ, interiorVariableCoeffForm_apply, multiplicationCoefficientOperator_apply,
        sub_eq_add_neg, MeasureTheory.Lp.smul_add, MeasureTheory.Lp.neg_smul,
        sum_inner, inner_add_left, inner_neg_left, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
    rw [hu] at hsub
    simp only [inner_add_left, Finset.sum_add_distrib]
    linarith

end SobolevSpace.GraphSpace
