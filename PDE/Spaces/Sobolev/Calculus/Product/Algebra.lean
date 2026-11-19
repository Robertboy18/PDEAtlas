/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.FiniteOperator

/-!
# Multiplication in the Sobolev algebra

When `n < 2k`, the product of two `Hᵏ` functions belongs to `Hᵏ`. We obtain a bound
on the unit ball from the finite-composition estimate, then use bilinearity
to recover the product of the two norms. Mathlib bundles this estimate into a bounded
bilinear map, ready for differentiating nonlinear reaction operators.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped Sobolev
namespace SobolevSpace.GraphSpace
open SobolevSpace.Composition
variable {n k : ℕ} [NeZero n]

/-- Pointwise multiplication of Sobolev functions above the strict embedding threshold. -/
def pointwiseProduct (hk : (n : ℝ) < 2 * (k : ℝ))
    (U V : W^{k,2}(ℝ^n)) : W^{k,2}(ℝ^n) :=
  finiteComposition hk ((contDiff_apply ℝ (fun _ ↦ ℝ) (0 : Fin 2)).mul
    (contDiff_apply ℝ (fun _ ↦ ℝ) 1)) (by simp) ![U, V]

/-- Sobolev multiplication agrees with the product of representatives almost everywhere. -/
theorem pointwiseProduct_ae (hk : (n : ℝ) < 2 * (k : ℝ))
    (U V : W^{k,2}(ℝ^n)) :
    baseRepresentative (pointwiseProduct hk U V) =ᵐ[volume]
      (fun x ↦ baseRepresentative U x * baseRepresentative V x) :=
  finiteComposition_ae hk _ _ _

/-- Multiplication distributes over addition in its first argument. -/
theorem pointwiseProduct_add_left (hk : (n : ℝ) < 2 * (k : ℝ))
    (U V W : W^{k,2}(ℝ^n)) :
    pointwiseProduct hk (U + V) W = pointwiseProduct hk U W + pointwiseProduct hk V W := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  change baseRepresentative (pointwiseProduct hk (U + V) W) =ᵐ[domainMeasure n univ]
    baseRepresentative (pointwiseProduct hk U W + pointwiseProduct hk V W)
  have h1 := baseRepresentative_add_ae U V
  have h2 := baseRepresentative_add_ae (pointwiseProduct hk U W) (pointwiseProduct hk V W)
  simp only [domainMeasure, Measure.restrict_univ] at h1 h2 ⊢
  filter_upwards [pointwiseProduct_ae hk (U + V) W,
    pointwiseProduct_ae hk U W, pointwiseProduct_ae hk V W, h1, h2]
    with x h hU hV ha hb
  simp only [h, hU, hV, ha, hb, add_mul]

/-- Real scalar multiplication commutes with the product in its first argument. -/
theorem pointwiseProduct_smul_left (hk : (n : ℝ) < 2 * (k : ℝ))
    (c : ℝ) (U V : W^{k,2}(ℝ^n)) :
    pointwiseProduct hk (c • U) V = c • pointwiseProduct hk U V := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  change baseRepresentative (pointwiseProduct hk (c • U) V) =ᵐ[domainMeasure n univ]
    baseRepresentative (c • pointwiseProduct hk U V)
  have h1 := baseRepresentative_smul_ae c U
  have h2 := baseRepresentative_smul_ae c (pointwiseProduct hk U V)
  simp only [domainMeasure, Measure.restrict_univ] at h1 h2 ⊢
  filter_upwards [pointwiseProduct_ae hk (c • U) V, pointwiseProduct_ae hk U V, h1, h2]
    with x h hU ha hb
  simp only [h, hU, ha, hb, smul_eq_mul, mul_assoc]

/-- Sobolev multiplication is commutative. -/
theorem pointwiseProduct_comm (hk : (n : ℝ) < 2 * (k : ℝ))
    (U V : W^{k,2}(ℝ^n)) : pointwiseProduct hk U V = pointwiseProduct hk V U := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  change baseRepresentative (pointwiseProduct hk U V) =ᵐ[domainMeasure n univ]
    baseRepresentative (pointwiseProduct hk V U)
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [pointwiseProduct_ae hk U V, pointwiseProduct_ae hk V U]
    with x hU hV
  simpa only [hU, hV] using mul_comm (baseRepresentative U x) (baseRepresentative V x)

/-- Sobolev multiplication as a bilinear map, before applying the norm estimate. -/
def productLinearMap (hk : (n : ℝ) < 2 * (k : ℝ)) :
    W^{k,2}(ℝ^n) →ₗ[ℝ] W^{k,2}(ℝ^n) →ₗ[ℝ] W^{k,2}(ℝ^n) :=
  LinearMap.mk₂ ℝ (pointwiseProduct hk)
    (pointwiseProduct_add_left hk) (pointwiseProduct_smul_left hk)
    (fun U V W ↦ by simpa only [pointwiseProduct_comm hk U] using
      pointwiseProduct_add_left hk V W U)
    (fun c U V ↦ by simpa only [pointwiseProduct_comm hk U] using
      pointwiseProduct_smul_left hk c V U)

/-- The product norm is bounded by a constant times the two input norms. -/
theorem exists_product_bound (hk : (n : ℝ) < 2 * (k : ℝ)) :
    ∃ C : ℝ, ∀ U V : W^{k,2}(ℝ^n),
      ‖productLinearMap hk U V‖ ≤ C * ‖U‖ * ‖V‖ := by
  obtain ⟨C, _, hC⟩ := exists_norm_finiteComposition_bound hk
    ((contDiff_apply ℝ (fun _ ↦ ℝ) (0 : Fin 2)).mul (contDiff_apply ℝ (fun _ ↦ ℝ) 1)) (by simp) 1
  refine ⟨C, fun U V ↦ ?_⟩
  by_cases hU : U = 0
  · simp [hU]
  by_cases hV : V = 0
  · simp [hV]
  have hnU : 0 < ‖U‖ := norm_pos_iff.mpr hU
  have hnV : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hnorm : ‖![‖U‖⁻¹ • U, ‖V‖⁻¹ • V]‖ ≤ (1 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    fin_cases i
    · change ‖‖U‖⁻¹ • U‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hnU.ne']
    · change ‖‖V‖⁻¹ • V‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hnV.ne']
  have hbound := hC ![‖U‖⁻¹ • U, ‖V‖⁻¹ • V] hnorm
  change ‖productLinearMap hk (‖U‖⁻¹ • U) (‖V‖⁻¹ • V)‖ ≤ C at hbound
  have hid : productLinearMap hk U V =
      (‖U‖ * ‖V‖) • productLinearMap hk (‖U‖⁻¹ • U) (‖V‖⁻¹ • V) := by
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    rw [show ‖U‖ * ‖V‖ * (‖V‖⁻¹ * ‖U‖⁻¹) = 1 by
      field_simp, one_smul]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnU.le hnV.le)]
  exact (mul_le_mul_of_nonneg_left hbound (mul_nonneg hnU.le hnV.le)).trans_eq (by ring)

/-- Multiplication is a bounded bilinear map on Hᵏ when the dimension is less than 2k. -/
def multiplication (hk : (n : ℝ) < 2 * (k : ℝ)) :
    W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) :=
  (productLinearMap hk).mkContinuousOfExistsBound₂ (exists_product_bound hk)

/-- The bounded bilinear product is the ordinary product almost everywhere. -/
theorem multiplication_ae (hk : (n : ℝ) < 2 * (k : ℝ))
    (U V : W^{k,2}(ℝ^n)) :
    baseRepresentative (multiplication hk U V) =ᵐ[volume]
      (fun x ↦ baseRepresentative U x * baseRepresentative V x) :=
  pointwiseProduct_ae hk U V
end SobolevSpace.GraphSpace
