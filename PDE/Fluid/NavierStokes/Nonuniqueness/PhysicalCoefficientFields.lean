/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalCoefficients

/-!
# Physical coefficient fields

The transport by a smooth field `X` is covariant under the physical change of variables:
with `a = e^{-τ/2}` and the dilated field `X^a(x) = a X(a x)`,

`P_τ ((X·∇) v + (v·∇) X) = e^τ ((X^a·∇)(P_τ v) + (P_τ v·∇) X^a)`

(`physicalMap_profileConvection`), and the same holds for the `L⁴` convection of two smooth
fields (`physicalMap_lebesgueConvection`). The cutoff field dilates to the physical cutoff
field `-e^{tΔ} w` (`physicalCutoffSobolev`) and the profile to `t^{-1/2} Ũ(x / √t)`
(`physicalProfileWkTop`, `physicalProfileWkFour`), as elements of `W^{k,∞}` and `W^{k,4}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Analysis.Evolution
open NavierStokes.SobolevConvection NavierStokes.Selfsimilar
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-! ### Dilated fields -/

/-- The dilated field `x ↦ a X(a x)`. -/
def dilateField (a : ℝ) (X : ℝ^3 → ℝ^3) : ℝ^3 → ℝ^3 :=
  fun x ↦ a • X (a • x)

variable {X : ℝ^3 → ℝ^3}

theorem contDiff_dilateField (a : ℝ) (hX : ContDiff ℝ (⊤ : ℕ∞) X) :
    ContDiff ℝ (⊤ : ℕ∞) (dilateField a X) :=
  (hX.comp (contDiff_const_smul a)).const_smul a

/-- The derivatives of a dilated field are dilated derivatives. -/
theorem iteratedFDeriv_dilateField (a : ℝ) (hX : ContDiff ℝ (⊤ : ℕ∞) X) (m : ℕ) (x : ℝ^3) :
    iteratedFDeriv ℝ m (dilateField a X) x = a • a ^ m • iteratedFDeriv ℝ m X (a • x) := by
  have h₁ : ContDiffAt ℝ m (fun z ↦ X (a • z)) x :=
    ((hX.comp (contDiff_const_smul a)).of_le (by exact_mod_cast le_top)).contDiffAt
  unfold dilateField
  rw [iteratedFDeriv_const_smul_apply' h₁,
    iteratedFDeriv_comp_const_smul a (hX.of_le (by exact_mod_cast le_top))]

/-- Dilation keeps the derivatives of a smooth field in `Lᵖ`. -/
theorem memLp_iteratedFDeriv_dilateField {a : ℝ} (ha : a ≠ 0) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    {m : ℕ} {p : ℝ≥0∞} (hmem : MemLp (iteratedFDeriv ℝ m X) p volume) :
    MemLp (iteratedFDeriv ℝ m (dilateField a X)) p volume := by
  have h : iteratedFDeriv ℝ m (dilateField a X) =
      fun x ↦ a • a ^ m • iteratedFDeriv ℝ m X (a • x) :=
    funext (iteratedFDeriv_dilateField a hX m)
  rw [h]
  exact ((hmem.comp_smul ha).const_smul (a ^ m)).const_smul a

/-- The derivative of a dilated field: `D(X^a)(x) v = a² DX(a x) v`. -/
theorem fderiv_dilateField_apply (a : ℝ) (hX : ContDiff ℝ (⊤ : ℕ∞) X) (x v : ℝ^3) :
    fderiv ℝ (dilateField a X) x v = (a * a) • fderiv ℝ X (a • x) v := by
  have hd : HasFDerivAt (fun z ↦ X (a • z))
      ((fderiv ℝ X (a • x)).comp (a • ContinuousLinearMap.id ℝ (ℝ^3))) x :=
    ((hX.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x
      ((hasFDerivAt_id x).const_smul a)
  unfold dilateField
  rw [(hd.fun_const_smul a).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul]

/-! ### Covariance of the transport -/

/-- The physical factors at `τ` and `-τ` are inverse. -/
theorem physicalFactor_neg_mul (τ : ℝ) : physicalFactor (-τ) * physicalFactor τ = 1 := by
  rw [physicalFactor, physicalFactor, ← Real.exp_add]
  ring_nf
  exact Real.exp_zero

/-- `e^τ a² = 1` for the physical factor `a = e^{-τ/2}`. -/
theorem exp_mul_physicalFactor_sq (τ : ℝ) :
    Real.exp τ * (physicalFactor τ * physicalFactor τ) = 1 := by
  rw [physicalFactor, ← Real.exp_add, ← Real.exp_add]
  ring_nf
  exact Real.exp_zero

/-- The base representatives of a physical image are dilated base representatives. -/
theorem baseRepresentative_physicalMap_ae {k : ℕ} (τ : ℝ) (v : VectorH 3 k) (j : Fin 3) :
    baseRepresentative (physicalMap k τ v j) =ᵐ[volume]
      fun x ↦ physicalFactor τ * baseRepresentative (v j) (physicalFactor τ • x) := by
  rw [physicalMap_apply, PiLp.smul_apply, vectorDilation_apply]
  have h₁ := baseRepresentative_smul_ae (physicalFactor τ)
    (dilationWkpCLM (by norm_num) (physicalFactor τ) (physicalFactor_pos τ).ne' (v j))
  have h₂ := dilationWkpCLM_base_ae (by norm_num) (physicalFactor τ) (physicalFactor_pos τ).ne'
    (v j)
  simp only [domainMeasure, Measure.restrict_univ] at h₁ h₂
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  rw [hx₁, hx₂, smul_eq_mul]

/-- The base representatives of the partial derivatives of a physical image. -/
theorem baseRepresentative_partialDerivCLM_physicalMap_ae {k : ℕ} (τ : ℝ) (v : VectorH 3 (k + 1))
    (i j : Fin 3) :
    baseRepresentative (partialDerivCLM (k := k) i (physicalMap (k + 1) τ v j)) =ᵐ[volume]
      fun x ↦ physicalFactor τ * (physicalFactor τ *
        baseRepresentative (partialDerivCLM (k := k) i (v j)) (physicalFactor τ • x)) := by
  rw [physicalMap_apply, PiLp.smul_apply, vectorDilation_apply, map_smul,
    partialDerivCLM_dilationWkpCLM, smul_smul]
  have h₁ := baseRepresentative_smul_ae (physicalFactor τ * physicalFactor τ)
    (dilationWkpCLM (by norm_num) (physicalFactor τ) (physicalFactor_pos τ).ne'
      (partialDerivCLM (k := k) i (v j)))
  have h₂ := dilationWkpCLM_base_ae (by norm_num) (physicalFactor τ) (physicalFactor_pos τ).ne'
    (partialDerivCLM (k := k) i (v j))
  simp only [domainMeasure, Measure.restrict_univ] at h₁ h₂
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  rw [hx₁, hx₂, smul_eq_mul, mul_assoc]

/-- **Covariance of the transport by a smooth field.** With `a = e^{-τ/2}`,
`P_τ ((X·∇) v + (v·∇) X) = e^τ ((X^a·∇)(P_τ v) + (P_τ v·∇) X^a)`, written for `v = P_{-τ} w`. -/
theorem physicalMap_profileConvection (k : ℕ) (τ : ℝ) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hmem : ∀ m ≤ k + 1, MemLp (iteratedFDeriv ℝ m X) ⊤ volume) (w : VectorH 3 (k + 1)) :
    physicalMap k τ (profileConvection k (vectorWkpOfContDiff X hX hmem)
        (physicalMap (k + 1) (-τ) w)) =
      Real.exp τ • profileConvection k (vectorWkpOfContDiff (dilateField (physicalFactor τ) X)
        (contDiff_dilateField _ hX) fun m hm ↦
          memLp_iteratedFDeriv_dilateField (physicalFactor_pos τ).ne' hX (hmem m hm)) w := by
  set a := physicalFactor τ with ha
  set b := physicalFactor (-τ) with hb
  have hba : b * a = 1 := physicalFactor_neg_mul τ
  have hea : Real.exp τ * (a * a) = 1 := exp_mul_physicalFactor_sq τ
  have ha0 : a ≠ 0 := (physicalFactor_pos τ).ne'
  refine PiLp.ext fun j ↦ WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  change baseRepresentative _ =ᵐ[domainMeasure 3 univ] baseRepresentative _
  simp only [domainMeasure, Measure.restrict_univ]
  have hqmp := Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^3)) ha0
  -- the left side
  have hL := baseRepresentative_physicalMap_ae τ (profileConvection k
    (vectorWkpOfContDiff X hX hmem) (physicalMap (k + 1) (-τ) w)) j
  have hC := hqmp.ae_eq_comp (profileConvection_vectorWkpOfContDiff_base_ae k X hX hmem
    (physicalMap (k + 1) (-τ) w) j)
  have hv : ∀ i : Fin 3, (fun x ↦ baseRepresentative (physicalMap (k + 1) (-τ) w i) (a • x))
      =ᵐ[volume] fun x ↦ b * baseRepresentative (w i) x := fun i ↦ by
    have h := hqmp.ae_eq_comp (baseRepresentative_physicalMap_ae (-τ) w i)
    filter_upwards [h] with x hx
    simp only [Function.comp_apply] at hx
    rw [hx, smul_smul, hba, one_smul]
  have hdv : ∀ i : Fin 3, (fun x ↦ baseRepresentative (partialDerivCLM (k := k) i
      (physicalMap (k + 1) (-τ) w j)) (a • x)) =ᵐ[volume]
      fun x ↦ b * (b * baseRepresentative (partialDerivCLM (k := k) i (w j)) x) := fun i ↦ by
    have h := hqmp.ae_eq_comp (baseRepresentative_partialDerivCLM_physicalMap_ae (-τ) w i j)
    filter_upwards [h] with x hx
    simp only [Function.comp_apply] at hx
    rw [hx, smul_smul, hba, one_smul]
  -- the right side
  have hR₁ := baseRepresentative_smul_ae (Real.exp τ) (profileConvection k
    (vectorWkpOfContDiff (dilateField a X) (contDiff_dilateField _ hX) fun m hm ↦
      memLp_iteratedFDeriv_dilateField (physicalFactor_pos τ).ne' hX (hmem m hm)) w j)
  simp only [domainMeasure, Measure.restrict_univ] at hR₁
  have hR₂ := profileConvection_vectorWkpOfContDiff_base_ae k (dilateField a X)
    (contDiff_dilateField _ hX) (fun m hm ↦
      memLp_iteratedFDeriv_dilateField (physicalFactor_pos τ).ne' hX (hmem m hm)) w j
  rw [PiLp.smul_apply]
  filter_upwards [hL, hC, ae_all_iff.mpr hv, ae_all_iff.mpr hdv, hR₁, hR₂]
    with x h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₅, h₆]
  simp only [Function.comp_apply] at h₂
  rw [h₂, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [h₃ i, h₄ i, fderiv_dilateField_apply a hX]
  simp only [dilateField, PiLp.smul_apply, smul_eq_mul]
  have hb' : b = a⁻¹ := eq_inv_of_mul_eq_one_left hba
  have he' : Real.exp τ = (a * a)⁻¹ := eq_inv_of_mul_eq_one_left hea
  rw [hb', he']
  field_simp
  ring

/-- **Covariance of the `L⁴` convection of smooth fields.** With `a = e^{-τ/2}`,
`P_τ ((A·∇) V) = e^τ ((A^a·∇) V^a)`. -/
theorem physicalMap_lebesgueConvection (k : ℕ) (τ : ℝ) {A V : ℝ^3 → ℝ^3}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (hAmem : ∀ m ≤ k, MemLp (iteratedFDeriv ℝ m A) 4 volume)
    (hVmem : ∀ m ≤ k + 1, MemLp (iteratedFDeriv ℝ m V) 4 volume) :
    physicalMap k τ (lebesgueConvection k (vectorWkpOfContDiff A hA hAmem)
        (vectorWkpOfContDiff V hV hVmem)) =
      Real.exp τ • lebesgueConvection k
        (vectorWkpOfContDiff (dilateField (physicalFactor τ) A) (contDiff_dilateField _ hA)
          fun m hm ↦ memLp_iteratedFDeriv_dilateField (physicalFactor_pos τ).ne' hA (hAmem m hm))
        (vectorWkpOfContDiff (dilateField (physicalFactor τ) V) (contDiff_dilateField _ hV)
          fun m hm ↦ memLp_iteratedFDeriv_dilateField (physicalFactor_pos τ).ne' hV
            (hVmem m hm)) := by
  set a := physicalFactor τ with ha
  have hea : Real.exp τ * (a * a) = 1 := exp_mul_physicalFactor_sq τ
  have ha0 : a ≠ 0 := (physicalFactor_pos τ).ne'
  refine PiLp.ext fun j ↦ WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  change baseRepresentative _ =ᵐ[domainMeasure 3 univ] baseRepresentative _
  simp only [domainMeasure, Measure.restrict_univ]
  have hqmp := Measure.quasiMeasurePreserving_smul (volume : Measure (ℝ^3)) ha0
  have hL := baseRepresentative_physicalMap_ae τ (lebesgueConvection k
    (vectorWkpOfContDiff A hA hAmem) (vectorWkpOfContDiff V hV hVmem)) j
  have hC := hqmp.ae_eq_comp (lebesgueConvection_vectorWkpOfContDiff_base_ae k A V hA hV
    hAmem hVmem j)
  have hR₁ := baseRepresentative_smul_ae (Real.exp τ) (lebesgueConvection k
    (vectorWkpOfContDiff (dilateField a A) (contDiff_dilateField _ hA)
      fun m hm ↦ memLp_iteratedFDeriv_dilateField (physicalFactor_pos τ).ne' hA (hAmem m hm))
    (vectorWkpOfContDiff (dilateField a V) (contDiff_dilateField _ hV)
      fun m hm ↦ memLp_iteratedFDeriv_dilateField (physicalFactor_pos τ).ne' hV (hVmem m hm)) j)
  simp only [domainMeasure, Measure.restrict_univ] at hR₁
  have hR₂ := lebesgueConvection_vectorWkpOfContDiff_base_ae k (dilateField a A)
    (dilateField a V) (contDiff_dilateField _ hA) (contDiff_dilateField _ hV)
    (fun m hm ↦ memLp_iteratedFDeriv_dilateField (physicalFactor_pos τ).ne' hA (hAmem m hm))
    (fun m hm ↦ memLp_iteratedFDeriv_dilateField (physicalFactor_pos τ).ne' hV (hVmem m hm)) j
  rw [PiLp.smul_apply]
  filter_upwards [hL, hC, hR₁, hR₂] with x h₁ h₂ h₅ h₆
  rw [h₁, h₅, h₆]
  simp only [Function.comp_apply] at h₂
  rw [h₂, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_dilateField_apply a hV]
  simp only [dilateField, PiLp.smul_apply, smul_eq_mul]
  have he' : Real.exp τ = (a * a)⁻¹ := eq_inv_of_mul_eq_one_left hea
  rw [he', ← ha]
  field_simp

/-! ### The physical coefficient fields -/

/-- The transport of the linearization at the profile is the unprojected profile convection of
the profile in `W^{k+1,∞}`. -/
theorem UnstableProfile.transport_eq_profileConvection (D : UnstableProfile) (k : ℕ) :
    (D.profileCoefficientBounds k).transport = profileConvection k (D.velocityWkTop (k + 1)) := by
  have hmem : ∀ m ≤ k + 1, MemLp (iteratedFDeriv ℝ m D.U) ⊤ volume :=
    fun m _ ↦ D.memLp_top_iteratedFDeriv m
  refine (Selfsimilar.ProfileCoefficientBounds.transport_eq_linearTransport
    (D.profileCoefficientBounds k)
    (B := fun i ↦ lowerOrderCLM (Nat.le_succ k) (D.velocityWkTop (k + 1) i))
    (C := fun j i ↦ partialDerivCLM i (D.velocityWkTop (k + 1) j)) (fun i ↦ ?_)
    (fun j i ↦ ?_)).trans rfl
  · rw [wkpBaseCoordinateCLM_lowerOrderCLM]
    refine Lp.ext ?_
    have h : baseRepresentative (D.velocityWkTop (k + 1) i) =ᵐ[volume] _ :=
      (baseRepresentative_vectorWkpOfContDiff D.U D.contDiff_U hmem i).trans
        (D.transportCoefficients_ae i).symm
    simpa only [domainMeasure, Measure.restrict_univ, baseRepresentative,
      wkpBaseCoordinateCLM_apply] using h
  · refine Lp.ext ?_
    have h : baseRepresentative (partialDerivCLM i (D.velocityWkTop (k + 1) j)) =ᵐ[volume] _ :=
      (baseRepresentative_partialDerivCLM_vectorWkpOfContDiff (k := k) D.U D.contDiff_U
        hmem j i).trans (D.stretchingCoefficients_ae j i).symm
    simpa only [domainMeasure, Measure.restrict_univ, baseRepresentative,
      wkpBaseCoordinateCLM_apply] using h

variable (D : UnstableProfile) (R : ℝ)

/-- The smooth cutoff field at similarity time `τ`, the base function of `cutoffSobolev`. -/
def cutoffFieldFn (τ : ℝ) : ℝ^3 → ℝ^3 :=
  gaussianFlow 1 fun x ↦ Real.exp (τ / 2) •
    (-localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) (Real.exp (τ / 2) • x)

theorem contDiff_cutoffFieldFn (τ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoffFieldFn D R τ) :=
  contDiff_gaussianFlow_one_dilate (D.memLp_four_localizationRemainder R).neg (by norm_num) τ

theorem memLp_iteratedFDeriv_cutoffFieldFn {r : ℝ≥0∞} (hr : 4 ≤ r) (τ : ℝ) (m : ℕ) :
    MemLp (iteratedFDeriv ℝ m (cutoffFieldFn D R τ)) r volume :=
  memLp_iteratedFDeriv_gaussianFlow_one_dilate (D.memLp_four_localizationRemainder R).neg
    (by norm_num) hr τ m

/-- The physical cutoff field `-e^{tΔ} w` in `W^{k,r}(ℝ³)`, `4 ≤ r`, at time `t`. -/
def physicalCutoffSobolev (k : ℕ) {r : ℝ≥0∞} (hr : 4 ≤ r) (t : ℝ) : Fin 3 → W^{k,r}(ℝ^3) :=
  vectorWkpOfContDiff (dilateField (physicalFactor (Real.log t)) (cutoffFieldFn D R (Real.log t)))
    (contDiff_dilateField _ (contDiff_cutoffFieldFn D R _)) fun m _ ↦
      memLp_iteratedFDeriv_dilateField (physicalFactor_pos _).ne' (contDiff_cutoffFieldFn D R _)
        (memLp_iteratedFDeriv_cutoffFieldFn D R hr _ m)

/-- The physical profile `t^{-1/2} Ũ(x / √t)` in `W^{k,∞}(ℝ³)` at time `t`. -/
def physicalProfileWkTop (k : ℕ) (t : ℝ) : Fin 3 → W^{k,∞}(ℝ^3) :=
  vectorWkpOfContDiff (dilateField (physicalFactor (Real.log t)) D.U)
    (contDiff_dilateField _ D.contDiff_U) fun m _ ↦
      memLp_iteratedFDeriv_dilateField (physicalFactor_pos _).ne' D.contDiff_U
        (D.memLp_top_iteratedFDeriv m)

/-- The physical profile `t^{-1/2} Ũ(x / √t)` in `W^{k,4}(ℝ³)` at time `t`. -/
def physicalProfileWkFour (k : ℕ) (t : ℝ) : Fin 3 → W^{k,4}(ℝ^3) :=
  vectorWkpOfContDiff (dilateField (physicalFactor (Real.log t)) D.U)
    (contDiff_dilateField _ D.contDiff_U) fun m _ ↦
      memLp_iteratedFDeriv_dilateField (physicalFactor_pos _).ne' D.contDiff_U
        (D.derivatives_memLp_four m)

end NavierStokes.Nonuniqueness
