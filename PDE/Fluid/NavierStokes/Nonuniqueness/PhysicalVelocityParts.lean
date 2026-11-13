/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalCutoffSmoothness

/-!
# The three parts of the physical velocity

At a positive time `t` the slice of the physical velocity is the sum
`v = ũ + u_cut + u_cor` (`velocitySlice_physicalVelocity_eq_add`) of the dilated profile
`ũ = a Ũ(a ·)`, `a = t^{-1/2}` (`physicalProfileField`), the heat flow `u_cut = -e^{tΔ} w` of
the localization remainder (`physicalCutoffField`) and the correction
`u_cor = a U_cor(log t, a ·)` (`physicalCorrectionField`). For `0 < t ≤ 1` all three are smooth
with square-integrable derivative (the profile has `DŨ ∈ L²`, the remainder has symbol decay
of order `-1`, and the correction lies in every `Hᵐ`), and all three are divergence free, so the
slice is smooth, divergence free and has square-integrable derivative
(`contDiff_velocitySlice_physicalVelocity`, `divergence_velocitySlice_physicalVelocity`,
`memLp_fderiv_velocitySlice_physicalVelocity`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Common
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable (D : UnstableProfile) (R s : ℝ)

/-- The profile part `t^{-1/2} Ũ(x / √t)` of the physical velocity at time `t`. -/
def physicalProfileField (t : ℝ) : ℝ^3 → ℝ^3 :=
  dilateField (physicalFactor (Real.log t)) D.U

/-- The cutoff part `-e^{tΔ} w` of the physical velocity at time `t > 0`. -/
def physicalCutoffField (t : ℝ) : ℝ^3 → ℝ^3 :=
  dilateField (physicalFactor (Real.log t)) (cutoffFieldFn D R (Real.log t))

/-- The correction part `t^{-1/2} U_cor(log t, x / √t)` of the physical velocity at time `t`. -/
def physicalCorrectionField (t : ℝ) (x : ℝ^3) : ℝ^3 :=
  (Real.sqrt t)⁻¹ • correctionField D R s (Real.log t) ((Real.sqrt t)⁻¹ • x)

variable {D R s}

/-- At a positive time the cutoff part is the heat flow `-e^{tΔ} w` of the remainder. -/
theorem physicalCutoffField_eq {t : ℝ} (ht : 0 < t) :
    physicalCutoffField D R t = -gaussianFlow t (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) :=
  funext fun x ↦ D.dilateField_cutoffFieldFn ht x

/-- At a positive time the slice of the physical velocity is the sum of its three parts. -/
theorem velocitySlice_physicalVelocity_eq_add {t : ℝ} (ht : 0 < t) :
    velocitySlice (physicalVelocity D R s) t = physicalProfileField D t +
      physicalCutoffField D R t + physicalCorrectionField D R s t := by
  funext x
  rw [velocitySlice, physicalVelocity_timeSpaceCons_eq D R s ht x, Pi.add_apply, Pi.add_apply,
    physicalCutoffField, D.dilateField_cutoffFieldFn ht x, physicalProfileField, dilateField,
    physicalFactor_log ht, physicalCorrectionField, sub_eq_add_neg]

/-- The profile part of the physical velocity is smooth. -/
theorem contDiff_physicalProfileField (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalProfileField D t) :=
  contDiff_dilateField _ D.contDiff_U

/-- The cutoff part of the physical velocity is smooth. -/
theorem contDiff_physicalCutoffField (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (physicalCutoffField D R t) :=
  contDiff_dilateField _ (contDiff_cutoffFieldFn D R _)

/-- For `0 < t ≤ 1` the slice of the physical velocity is smooth. -/
theorem contDiff_velocitySlice_physicalVelocity (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ContDiff ℝ (⊤ : ℕ∞) (velocitySlice (physicalVelocity D R s) t) := by
  rw [velocitySlice_physicalVelocity_eq_add ht]
  exact ((contDiff_physicalProfileField t).add (contDiff_physicalCutoffField t)).add
    (contDiff_physicalCorrectionField hR hs ht ht1)

/-- The components of the physical correction in vector `Hᵐ⁺¹` are the correction part of the
physical velocity almost everywhere. -/
theorem baseRepresentative_physicalCorrection_ae (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : (3 : ℝ) < 2 * m) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (j : Fin 3) :
    baseRepresentative (physicalCorrection D R s m hm t j) =ᵐ[volume]
      fun x ↦ physicalCorrectionField D R s t x j := by
  have h := classicalRepresentativeCLM_ae (three_lt_two_mul_succ_sub_one hm)
    (physicalCorrection D R s m hm t j)
  rw [classicalRepresentativeCLM_physicalCorrection hR hs hm ht ht1 j] at h
  exact h.symm

/-- The weak derivatives of the physical correction are the classical derivatives of the
correction part of the physical velocity almost everywhere. -/
theorem baseRepresentative_partialDerivCLM_physicalCorrection_ae (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : (3 : ℝ) < 2 * m) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (i j : Fin 3) :
    baseRepresentative (partialDerivCLM (k := m + 1) i
        (physicalCorrection D R s (m + 1) (three_lt_two_mul_succ hm) t j)) =ᵐ[volume]
      fun x ↦ fderiv ℝ (physicalCorrectionField D R s t) x (EuclideanSpace.single i 1) j := by
  have hm' := three_lt_two_mul_succ hm
  have hk := three_lt_two_mul_succ_sub_one hm'
  have hlow := three_lt_two_mul_succ_sub_one hm
  have h := classicalRepresentativeCLM_ae hlow
    (partialDerivCLM i (physicalCorrection D R s (m + 1) hm' t j))
  rw [← PDE.Hyperbolic.NonlinearWave.Cauchy.partialDeriv_classicalRepresentative hk hlow i,
    classicalRepresentativeCLM_physicalCorrection hR hs hm' ht ht1 j] at h
  refine h.symm.trans (Eventually.of_forall fun x ↦ ?_)
  have hd : DifferentiableAt ℝ (physicalCorrectionField D R s t) x :=
    ((contDiff_physicalCorrectionField hR hs ht ht1).differentiable (by simp)) x
  exact (PDE.partialDeriv_apply i j hd).symm

/-! ### Square-integrable derivatives -/

/-- The derivative of the profile part of the physical velocity is square integrable. -/
theorem memLp_fderiv_physicalProfileField (t : ℝ) :
    MemLp (fderiv ℝ (physicalProfileField D t)) 2 volume :=
  PDE.memLp_fderiv_of_memLp_iteratedFDeriv_one ((contDiff_physicalProfileField t).of_le (by simp))
    (memLp_iteratedFDeriv_dilateField (physicalFactor_pos _).ne' D.contDiff_U
      (D.derivatives_memLp_two 1 le_rfl))

/-- The partial derivatives of the localization remainder are square integrable. -/
theorem memLp_partialDeriv_localizationRemainder (hR : 0 < R) (i : Fin 3) :
    MemLp (∂[i] (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R)) 2 volume := by
  have hW := D.contDiff_remainder hR
  have h1 := (D.hasSymbolDecay_localizationRemainder hR).memLp_iteratedFDeriv (μ := volume) hW 1
    (p := 2) (by
      simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat, Int.cast_neg,
        Int.cast_one, ENNReal.toReal_ofNat]
      norm_num)
  refine (PDE.memLp_fderiv_of_memLp_iteratedFDeriv_one (hW.of_le (by simp)) h1).of_le
    (PDE.contDiff_top_partialDeriv (i := i) hW).continuous.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  refine ((fderiv ℝ (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) x).le_opNorm _).trans ?_
  simp

/-- At positive times the partial derivatives of the cutoff part are the heat flows of the
partial derivatives of the remainder: `∂ᵢ(-e^{tΔ} w) = -e^{tΔ} ∂ᵢw`. -/
theorem partialDeriv_physicalCutoffField (hR : 0 < R) {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    ∂[i] (physicalCutoffField D R t) =
      -gaussianFlow t (∂[i] (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R)) := by
  rw [physicalCutoffField_eq ht]
  funext x
  rw [PDE.partialDeriv_neg, Pi.neg_apply]
  exact congrArg Neg.neg (congrFun (partialDeriv_gaussianFlow_eq ht (D.contDiff_remainder hR)
    (D.exists_bound_iteratedFDeriv_remainder hR) i) x)

/-- The derivative of the cutoff part of the physical velocity is square integrable. -/
theorem memLp_fderiv_physicalCutoffField (hR : 0 < R) {t : ℝ} (ht : 0 < t) :
    MemLp (fderiv ℝ (physicalCutoffField D R t)) 2 volume := by
  refine PDE.memLp_fderiv_of_memLp_partialDeriv ((contDiff_physicalCutoffField t).of_le (by simp))
    fun i ↦ ?_
  rw [partialDeriv_physicalCutoffField hR ht]
  exact (memLp_gaussianFlow ht one_le_two le_rfl
    (memLp_partialDeriv_localizationRemainder (D := D) hR i)).neg

/-- For `0 < t ≤ 1` the derivative of the correction part of the physical velocity is square
integrable. -/
theorem memLp_fderiv_physicalCorrectionField (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    MemLp (fderiv ℝ (physicalCorrectionField D R s t)) 2 volume := by
  have hm : (3 : ℝ) < 2 * ((2 : ℕ) : ℝ) := by norm_num
  refine PDE.memLp_fderiv_of_memLp_partialDeriv
    ((contDiff_physicalCorrectionField hR hs ht ht1).of_le (by simp)) fun i ↦ ?_
  refine MemLp.of_eval_piLp fun j ↦ ?_
  have h := baseRepresentative_partialDerivCLM_physicalCorrection_ae hR hs hm ht ht1 i j
  have hb := Lp.memLp (wkpBaseCoordinateCLM (partialDerivCLM (k := 2 + 1) i
    (physicalCorrection D R s (2 + 1) (three_lt_two_mul_succ hm) t j)))
  simp only [domainMeasure, Measure.restrict_univ] at hb
  exact hb.ae_eq h

/-- For `0 < t ≤ 1` the derivative of the slice of the physical velocity is the sum of the
derivatives of its three parts. -/
theorem fderiv_velocitySlice_physicalVelocity (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    fderiv ℝ (velocitySlice (physicalVelocity D R s) t) =
      fderiv ℝ (physicalProfileField D t) + fderiv ℝ (physicalCutoffField D R t) +
        fderiv ℝ (physicalCorrectionField D R s t) := by
  have hP := (contDiff_physicalProfileField (D := D) t).differentiable (by simp)
  have hC := (contDiff_physicalCutoffField (D := D) (R := R) t).differentiable (by simp)
  have hK : Differentiable ℝ (physicalCorrectionField D R s t) :=
    (contDiff_physicalCorrectionField hR hs ht ht1).differentiable (by simp)
  funext x
  rw [velocitySlice_physicalVelocity_eq_add ht, fderiv_add ((hP x).add (hC x)) (hK x),
    fderiv_add (hP x) (hC x)]
  rfl

/-- For `0 < t ≤ 1` the derivative of the slice of the physical velocity is square
integrable. -/
theorem memLp_fderiv_velocitySlice_physicalVelocity (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    MemLp (fderiv ℝ (velocitySlice (physicalVelocity D R s) t)) 2 volume := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  rw [fderiv_velocitySlice_physicalVelocity hR hs ht ht1]
  exact ((memLp_fderiv_physicalProfileField t).add (memLp_fderiv_physicalCutoffField hR0 ht)).add
    (memLp_fderiv_physicalCorrectionField hR hs ht ht1)

/-! ### Divergence-freeness -/

/-- The profile part of the physical velocity is divergence free. -/
theorem divergence_physicalProfileField (t : ℝ) (x : ℝ^3) :
    PDE.divergence (physicalProfileField D t) x = 0 := by
  set a := physicalFactor (Real.log t)
  have hd := (contDiff_physicalProfileField (D := D) t).differentiable (by simp)
  have hU := D.contDiff_U.differentiable (by simp)
  have h (i : Fin 3) : ∂[i] (fun y ↦ physicalProfileField D t y i) x =
      (a * a) * ∂[i] (fun y ↦ D.U y i) (a • x) := by
    rw [← PDE.partialDeriv_apply i i (hd x), physicalProfileField,
      partialDeriv_dilateField D.contDiff_U, PiLp.smul_apply, smul_eq_mul,
      PDE.partialDeriv_apply i i (hU _)]
  unfold PDE.divergence
  simp_rw [h, ← Finset.mul_sum]
  have h0 := D.divergence_eq_zero (a • x)
  unfold PDE.divergence at h0
  rw [h0, mul_zero]

/-- At positive times the cutoff part of the physical velocity is divergence free. -/
theorem divergence_physicalCutoffField (hR : 0 < R) {t : ℝ} (ht : 0 < t) (x : ℝ^3) :
    PDE.divergence (physicalCutoffField D R t) x = 0 := by
  set W := localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R with hWdef
  have hW := D.contDiff_remainder hR
  have hW4 := D.memLp_four_localizationRemainder R
  have hWi (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ W y i) :=
    (EuclideanSpace.proj i : ℝ^3 →L[ℝ] ℝ).contDiff.comp hW
  have hbi (i : Fin 3) : ∀ m : ℕ, ∃ M, ∀ x, ‖iteratedFDeriv ℝ m (fun y ↦ W y i) x‖ ≤ M :=
    fun m ↦ by
      obtain ⟨M, hM⟩ := D.exists_bound_iteratedFDeriv_remainder hR m
      exact ⟨M, fun x ↦ (PDE.norm_iteratedFDeriv_component_le hW i m x).trans (hM x)⟩
  have hcomp (i : Fin 3) : (fun y ↦ physicalCutoffField D R t y i) =
      fun y ↦ -gaussianFlow t (fun z ↦ W z i) y := by
    funext y
    rw [physicalCutoffField_eq ht, Pi.neg_apply, PiLp.neg_apply,
      gaussianFlow_component t (by norm_num) hW4 y i]
  have hterm (i : Fin 3) : ∂[i] (fun y ↦ physicalCutoffField D R t y i) x =
      -gaussianFlow t (∂[i] (fun z ↦ W z i)) x := by
    rw [hcomp i, show (fun y ↦ -gaussianFlow t (fun z ↦ W z i) y) =
      -gaussianFlow t (fun z ↦ W z i) from rfl, PDE.partialDeriv_neg]
    exact congrArg Neg.neg (congrFun (partialDeriv_gaussianFlow_eq ht (hWi i) (hbi i) i) x)
  have hdc (i : Fin 3) : Continuous (∂[i] (fun z ↦ W z i)) :=
    (PDE.contDiff_top_partialDeriv (i := i) (hWi i)).continuous
  have hdb (i : Fin 3) : ∃ M, ∀ y, ‖(∂[i] (fun z ↦ W z i)) y‖ ≤ M := by
    obtain ⟨M, hM⟩ := hbi i 1
    refine ⟨M, fun y ↦ ((fderiv ℝ (fun z ↦ W z i) y).le_opNorm _).trans ?_⟩
    simpa [norm_iteratedFDeriv_one] using hM y
  have hdivW : (fun y ↦ ∑ i : Fin 3, (∂[i] (fun z ↦ W z i)) y) = fun _ ↦ 0 := by
    funext y
    exact divergence_localizationRemainder hR (fun x c hc ↦ D.farField_smul x hc)
      (fun x hx ↦ D.contDiffAt_farField hx) D.datum_divergenceFree y
  unfold PDE.divergence
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib, ← gaussianFlow_finsetSum ht Finset.univ hdc hdb x, hdivW,
    gaussianFlow_apply ht]
  simp

/-- For `0 < t ≤ 1` the correction part of the physical velocity is divergence free. -/
theorem divergence_physicalCorrectionField (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : ℝ^3) :
    PDE.divergence (physicalCorrectionField D R s t) x = 0 := by
  have hm : (3 : ℝ) < 2 * ((2 : ℕ) : ℝ) := by norm_num
  set V := physicalCorrection D R s 2 hm t
  have hrow : lerayProjection 3 (l2SobolevRow (baseIndex 3 (2 + 1)) V) =
      l2SobolevRow (baseIndex 3 (2 + 1)) V := by
    rw [← l2SobolevRow_leraySobolev, leraySobolev_physicalCorrection hR hs hm ht ht1]
  have hsol : l2SobolevRow (baseIndex 3 (2 + 1)) V ∈ l2Solenoidal 3 :=
    hrow ▸ lerayProjection_mem 3 _
  have hdd := (mem_l2Solenoidal_iff_distributionallyDivergenceFree _).mp hsol
  have hae : (fun y ↦ l2SobolevRow (baseIndex 3 (2 + 1)) V y) =ᵐ[volume]
      physicalCorrectionField D R s t := by
    have h := Lp.euclideanTuple_apply_ae (fun j ↦ wkpCoordinateCLM (baseIndex 3 (2 + 1)) (V j))
    simp only [domainMeasure, Measure.restrict_univ] at h
    filter_upwards [h, ae_all_iff.mpr fun j ↦
      baseRepresentative_physicalCorrection_ae hR hs hm ht ht1 j] with y hy hb
    refine PiLp.ext fun j ↦ ?_
    rw [← hb j, l2SobolevRow_apply, hy j, wkpCoordinateCLM_apply]
    rfl
  exact (hdd.congr_ae hae).divergence_eq_zero_of_contDiffOn (n := 2) isOpen_univ
    ((contDiff_physicalCorrectionField hR hs ht ht1).of_le (by simp)).contDiffOn (mem_univ x)

/-- For `0 < t ≤ 1` the slice of the physical velocity is divergence free. -/
theorem divergence_velocitySlice_physicalVelocity (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : ℝ^3) :
    PDE.divergence (velocitySlice (physicalVelocity D R s) t) x = 0 := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  have hP := (contDiff_physicalProfileField (D := D) t).differentiable (by simp)
  have hC := (contDiff_physicalCutoffField (D := D) (R := R) t).differentiable (by simp)
  have hK : Differentiable ℝ (physicalCorrectionField D R s t) :=
    (contDiff_physicalCorrectionField hR hs ht ht1).differentiable (by simp)
  have e₁ := PDE.divergence_add_of_differentiableAt
    (F := physicalProfileField D t + physicalCutoffField D R t)
    (G := physicalCorrectionField D R s t) ((hP x).add (hC x)) (hK x)
  have e₂ := PDE.divergence_add_of_differentiableAt (F := physicalProfileField D t)
    (G := physicalCutoffField D R t) (hP x) (hC x)
  rw [velocitySlice_physicalVelocity_eq_add ht]
  refine e₁.trans ?_
  rw [show physicalProfileField D t + physicalCutoffField D R t =
    fun y ↦ physicalProfileField D t y + physicalCutoffField D R t y from rfl, e₂]
  rw [divergence_physicalProfileField, divergence_physicalCutoffField hR0 ht,
    divergence_physicalCorrectionField hR hs ht ht1]
  norm_num

end NavierStokes.Nonuniqueness
