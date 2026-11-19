/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.Algebra
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WholeSpaceVector

/-!
# Whole-space Sobolev convection in three dimensions

The unprojected transport `(U · ∇)V` is a bounded bilinear map from vector `H³`
to vector `H²`. Each coordinate is assembled from the actual weak derivative
and the whole-space `H²` multiplication operator. The finite Hilbert product
retains the sum of component energies, and the base representative is the
literal coordinate sum defining convection.

This supplies the derivative-loss estimate before pressure elimination.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped BigOperators Sobolev

namespace NavierStokes.SobolevConvection

/-- A nonnegative multiplication constant supplied by the proved `H²` algebra estimate. -/
def productConstant : ℝ :=
  max (exists_product_bound (by norm_num : (3 : ℝ) < 2 * (2 : ℝ))).choose 0

/-- The selected multiplication constant is nonnegative. -/
theorem productConstant_nonneg : 0 ≤ productConstant := le_max_right _ _

/-- The selected constant bounds the actual whole-space Sobolev product. -/
theorem norm_product_le (U V : W^{2,2}(ℝ^3)) :
    ‖multiplication (by norm_num : (3 : ℝ) < 2 * (2 : ℝ)) U V‖ ≤
      productConstant * ‖U‖ * ‖V‖ := by
  have h := (exists_product_bound (by norm_num : (3 : ℝ) < 2 * (2 : ℝ))).choose_spec U V
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg U)) (norm_nonneg V))

/-- One component of the actual weak transport, using the `H²` algebra product. -/
def scalarConvection (j : Fin 3) : VectorH 3 3 →L[ℝ] VectorH 3 3 →L[ℝ] W^{2,2}(ℝ^3) :=
  ∑ i : Fin 3, (multiplication (by norm_num : (3 : ℝ) < 2 * (2 : ℝ))).bilinearComp
    ((lowerOrderCLM (by norm_num : 2 ≤ 3)).comp (PiLp.proj 2 _ i))
    ((partialDerivCLM (k := 2) i).comp (PiLp.proj 2 _ j))

/-- The scalar convection coordinate is the sum of coefficient times weak partial. -/
theorem scalarConvection_apply (j : Fin 3) (U V : VectorH 3 3) :
    scalarConvection j U V = ∑ i : Fin 3,
      multiplication (by norm_num : (3 : ℝ) < 2 * (2 : ℝ))
        (lowerOrderCLM (by norm_num : 2 ≤ 3) (U i)) (partialDerivCLM (k := 2) i (V j)) := by
  simp only [scalarConvection, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply]

/-- The convection base coordinate is the actual product of Sobolev
representatives and weak partial-derivative representatives almost everywhere. -/
theorem scalarConvection_base_ae (j : Fin 3) (U V : VectorH 3 3) :
    baseRepresentative (scalarConvection j U V) =ᵐ[volume]
      fun x ↦ ∑ i : Fin 3, baseRepresentative (U i) x *
        baseRepresentative (partialDerivCLM (k := 2) i (V j)) x := by
  rw [scalarConvection_apply]
  have hs := baseRepresentative_sum_ae (fun i : Fin 3 ↦
    multiplication (by norm_num : (3 : ℝ) < 2 * (2 : ℝ))
      (lowerOrderCLM (by norm_num : 2 ≤ 3) (U i)) (partialDerivCLM (k := 2) i (V j)))
  simp only [domainMeasure, Measure.restrict_univ] at hs
  filter_upwards [hs, ae_all_iff.mpr (fun i : Fin 3 ↦
    multiplication_ae (by norm_num : (3 : ℝ) < 2 * (2 : ℝ))
      (lowerOrderCLM (by norm_num : 2 ≤ 3) (U i)) (partialDerivCLM (k := 2) i (V j)))]
    with x hsum hprod
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hprod i, baseRepresentative_lowerOrderCLM]

/-- The component transport estimate keeps the transported component's norm. -/
theorem norm_scalarConvection_le (j : Fin 3) (U V : VectorH 3 3) :
    ‖scalarConvection j U V‖ ≤
      (3 * productConstant * ‖U‖) * ‖V j‖ := by
  rw [scalarConvection_apply]
  calc
    _ ≤ ∑ i : Fin 3, ‖multiplication (by norm_num : (3 : ℝ) < 2 * (2 : ℝ))
        (lowerOrderCLM (by norm_num : 2 ≤ 3) (U i)) (partialDerivCLM (k := 2) i (V j))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3,
        productConstant * ‖U‖ * ‖V j‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_product_le _ _).trans
        (mul_le_mul
          (mul_le_mul_of_nonneg_left
            ((norm_lowerOrderCLM_apply_le (by norm_num : 2 ≤ 3) (U i)).trans
              (PiLp.norm_apply_le U i)) productConstant_nonneg)
          (norm_partialDeriv_le i (V j)) (norm_nonneg _)
            (mul_nonneg productConstant_nonneg (norm_nonneg U)))
    _ = _ := by simp; ring

/-- The three-component whole-space weak convection operator. -/
def convection : VectorH 3 3 →L[ℝ] VectorH 3 3 →L[ℝ] VectorH 3 2 :=
  let J := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 3 ↦ W^{2,2}(ℝ^3))).symm.toContinuousLinearMap
  ∑ j : Fin 3, (ContinuousLinearMap.compL ℝ (VectorH 3 3) (W^{2,2}(ℝ^3)) (VectorH 3 2)
    (J.comp (ContinuousLinearMap.single ℝ (fun _ : Fin 3 ↦ W^{2,2}(ℝ^3)) j))).comp
      (scalarConvection j)

/-- The vector operator has precisely the scalar convection components. -/
@[simp]
theorem convection_apply (U V : VectorH 3 3) (j : Fin 3) :
    convection U V j = scalarConvection j U V := by
  simp [convection, ContinuousLinearMap.compL_apply]

/-- The actual transport maps `H³ × H³` to `H²`, with a constant determined by
the proved whole-space Sobolev multiplication operator. -/
theorem norm_convection_le (U V : VectorH 3 3) :
    ‖convection U V‖ ≤
      3 * productConstant * ‖U‖ * ‖V‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity [productConstant_nonneg])).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ j : Fin 3,
        ((3 * productConstant * ‖U‖) * ‖V j‖) ^ 2 :=
      Finset.sum_le_sum fun j _ ↦
        (sq_le_sq₀ (norm_nonneg _) (by positivity [productConstant_nonneg])).mpr
          (by simpa only [convection_apply] using norm_scalarConvection_le j U V)
    _ = _ := by
      simp only [mul_pow]
      rw [← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]

/-- The bilinear convection has operator norm at most `3 * productConstant`. -/
theorem opNorm_convection_le : ‖convection‖ ≤ 3 * productConstant :=
  convection.opNorm_le_bound₂ (by positivity [productConstant_nonneg]) norm_convection_le

end NavierStokes.SobolevConvection
