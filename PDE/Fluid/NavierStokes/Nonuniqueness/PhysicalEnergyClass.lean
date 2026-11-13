/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.PhysicalMomentum
public import PDE.Fluid.NavierStokes.ClassicalEnergy.EnergyClass

/-!
# Gradient bounds of the physical velocity

Let `u` be the physical velocity of an unstable profile `D`, with `R ≥ D.ancientThreshold` and
`s ∈ [0, 1]`. There are constants `A`, `B` with `‖Du(t)‖_{L²} ≤ A t^{-1/4} + B` for `t ∈ (0, 1]`, so
`t ↦ ‖Du(t)‖²_{L²}` is integrable on `(0, 1]`.

## Main results

* `toReal_eLpNorm_fderiv_dilateField`: for `a > 0`, `‖D(a X(a ·))‖_{L²} = a^{1/2} ‖DX‖_{L²}` on
  `ℝ³`.
* `exists_toReal_eLpNorm_fderiv_correctionField_le`: the derivative of the correction field is
  bounded in `L²` uniformly in `τ ≤ 0`.
* `exists_toReal_eLpNorm_fderiv_physicalCutoffField_le`: the derivative of the cutoff part is
  bounded in `L²` uniformly in `t > 0`.
* `exists_toReal_eLpNorm_fderiv_velocitySlice_le`: `‖Du(t)‖_{L²} ≤ A t^{-1/4} + B` on `(0, 1]`.
* `integrableOn_sq_eLpNorm_fderiv_velocitySlice_physicalVelocity`: `t ↦ ‖Du(t)‖²_{L²}` is integrable
  on `(0, 1]`.

## How it works

The derivative of the slice at time `t` is the sum of the derivatives of its three parts. The
profile and correction parts are dilations `a X(a ·)` with `a = t^{-1/2}`, so the `L²` norms of
their derivatives are `t^{-1/4} ‖DX‖_{L²}` (`toReal_eLpNorm_fderiv_dilateField`,
`physicalFactor_log_rpow_half`). For the correction, `‖DX‖_{L²}` is bounded by the `H³` norm of the
ancient correction, which is bounded for `τ ≤ 0`. The cutoff part is `-e^{tΔ} w` with `w` the
localization remainder, and its derivative `-e^{tΔ} Dw` is bounded in `L²` by a constant times
`‖Dw‖_{L²}`. Squaring the bound gives `‖Du(t)‖²_{L²} ≤ 2 A² t^{-1/2} + 2 B²`, which is integrable on
`(0, 1]`, and the joint smoothness of `u` makes the squared norm measurable in time.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Common PDE.Analysis.Evolution
open scoped NNReal ENNReal Sobolev

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable {D : UnstableProfile} {R s : ℝ}

/-! ### Derivatives of dilations -/

/-- The derivative of a dilated field: `D(a X(a ·))(x) = a² DX(a x)`. -/
theorem fderiv_dilateField {X : ℝ^3 → ℝ^3} (hX : ContDiff ℝ (⊤ : ℕ∞) X) (a : ℝ) :
    fderiv ℝ (dilateField a X) = fun x ↦ (a * a) • fderiv ℝ X (a • x) :=
  funext fun x ↦ ContinuousLinearMap.ext fun v ↦ fderiv_dilateField_apply a hX x v

/-- **The `L²` norm of the derivative of a dilation.** For `a > 0`,
`‖D(a X(a ·))‖_{L²} = a^{1/2} ‖DX‖_{L²}` on `ℝ³`. -/
theorem toReal_eLpNorm_fderiv_dilateField {X : ℝ^3 → ℝ^3} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    {a : ℝ} (ha : 0 < a) :
    (eLpNorm (fderiv ℝ (dilateField a X)) 2 volume).toReal =
      a ^ (1 / 2 : ℝ) * (eLpNorm (fderiv ℝ X) 2 volume).toReal := by
  have hm : AEStronglyMeasurable (fderiv ℝ X) volume :=
    (hX.continuous_fderiv (by simp)).aestronglyMeasurable
  have hm' : AEStronglyMeasurable (fun y ↦ ‖fderiv ℝ X y‖) volume := hm.norm
  have hnorm : (fun x ↦ ‖(a * a) • fderiv ℝ X (a • x)‖) =
      (a * a) • fun x ↦ ‖fderiv ℝ X (a • x)‖ := by
    funext x
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    rfl
  rw [fderiv_dilateField hX a, ← eLpNorm_norm, hnorm, eLpNorm_const_smul,
    eLpNorm_comp_smul (f := fun y ↦ ‖fderiv ℝ X y‖) hm' ha.ne', eLpNorm_norm,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_assoc]
  rotate_left
  · exact hm
  · exact (((hX.continuous_fderiv (by simp)).comp (continuous_const_smul a)).const_smul
      (a * a)).aestronglyMeasurable
  congr 1
  rw [dilationFactor, finrank_euclideanSpace_fin, Real.enorm_eq_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (by positivity)]
  have h2 : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
  rw [h2, ← Real.rpow_natCast, ← Real.rpow_neg ha.le, ← Real.rpow_mul ha.le]
  rw [show a * a = a ^ (2 : ℝ) by rw [Real.rpow_two, sq], ← Real.rpow_add ha]
  norm_num

/-- **The derivative of the correction field is bounded in `L²`.** Above the threshold radius
and for `s ∈ [0, 1]` there is `M` with `‖DU_cor(τ)‖_{L²} ≤ M` for every `τ ≤ 0`. -/
theorem exists_toReal_eLpNorm_fderiv_correctionField_le (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ M : ℝ, ∀ τ ≤ 0, MemLp (fderiv ℝ (correctionField D R s τ)) 2 volume ∧
      (eLpNorm (fderiv ℝ (correctionField D R s τ)) 2 volume).toReal ≤ M := by
  have hm2 : (3 : ℝ) < 2 * ((2 : ℕ) : ℝ) := by norm_num
  have hk := three_lt_two_mul_succ_sub_one hm2
  set L : W^{2 + 1,2}(ℝ^3) →L[ℝ] WholeSpaceL2 3 :=
    (wkpGradientCLM (n := 3) (p := 2) (Ω := univ)).comp
      (lowerOrderCLM (n := 3) (p := 2) (Ω := univ) (by norm_num : 1 ≤ 2 + 1))
  refine ⟨3 * (3 * (‖L‖ * D.ancientRadius)), fun τ hτ ↦ ?_⟩
  set W := ancientLift D.dichotomy.η (ancientCorrection D R s) τ
  have hW : ‖W‖ ≤ D.ancientRadius := (norm_ancientLift_ancientCorrection_le hR hs τ).trans
    (mul_le_of_le_one_right D.ancientRadius_pos.le
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos D.dichotomy.η_pos.le hτ)))
  have hK := correctionField_eq_classicalRepresentative (isCorrectionLift_two hR hs hm2) hτ
  have hKs := contDiff_correctionField hR hs hτ
  set f : Fin 3 → ℝ^3 → ℝ := fun j ↦ classicalRepresentativeCLM hk (W j)
  have hf (j : Fin 3) : ContDiff ℝ 1 (f j) :=
    contDiff_classicalRepresentativeCLM hk (by norm_num) (W j)
  have hG (j : Fin 3) : ∀ᵐ x ∂volume, ∀ i : Fin 3, (L (W j) x) i = PDE.partialDeriv i (f j) x := by
    refine wkpGradientCLM_ae_eq_partialDeriv _ (hf j) ?_
    change f j =ᵐ[volume] baseRepresentative (lowerOrderCLM (n := 3) (p := 2) (Ω := univ)
      (by norm_num : 1 ≤ 2 + 1) (W j))
    rw [baseRepresentative_lowerOrderCLM]
    exact classicalRepresentativeCLM_ae hk (W j)
  -- each partial derivative is a Euclidean tuple of gradient coordinates
  have hpart (i : Fin 3) : (∂[i] (correctionField D R s τ)) =ᵐ[volume]
      Lp.euclideanTuple (fun j ↦ l2Coordinate i (L (W j))) := by
    have h₁ := Lp.euclideanTuple_apply_ae (fun j ↦ l2Coordinate i (L (W j)))
    have h₂ := ae_all_iff.mpr fun j ↦ l2Coordinate_ae i (L (W j))
    simp only [domainMeasure, Measure.restrict_univ] at h₁ h₂
    filter_upwards [h₁, h₂, ae_all_iff.mpr hG] with x e₁ e₂ e₃
    refine PiLp.ext fun j ↦ ?_
    rw [e₁ j, e₂ j, e₃ j i, PDE.partialDeriv_apply i j ((hKs.differentiable (by simp)) x), hK]
  have hnorm (i : Fin 3) : (eLpNorm (∂[i] (correctionField D R s τ)) 2 volume).toReal ≤
      3 * (‖L‖ * D.ancientRadius) := by
    rw [eLpNorm_congr_ae (hpart i)]
    have h := (Lp.norm_euclideanTuple_le (fun j ↦ l2Coordinate i (L (W j))))
    rw [Lp.norm_def] at h
    simp only [domainMeasure, Measure.restrict_univ] at h
    refine h.trans ?_
    calc ∑ j : Fin 3, ‖l2Coordinate i (L (W j))‖ ≤ ∑ _j : Fin 3, ‖L‖ * D.ancientRadius :=
          Finset.sum_le_sum fun j _ ↦ (norm_l2Coordinate_le i _).trans ((L.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le W j).trans hW) L.opNorm_nonneg))
      _ = 3 * (‖L‖ * D.ancientRadius) := by simp
  have hmem (i : Fin 3) : MemLp (∂[i] (correctionField D R s τ)) 2 volume := by
    have h := Lp.memLp (Lp.euclideanTuple (fun j ↦ l2Coordinate i (L (W j))))
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h.ae_eq (hpart i).symm
  have hC1 : ContDiff ℝ 1 (correctionField D R s τ) := hKs.of_le (by simp)
  refine ⟨PDE.memLp_fderiv_of_memLp_partialDeriv hC1 hmem, ?_⟩
  refine (PDE.toReal_eLpNorm_fderiv_le_sum hC1 one_le_two hmem).trans ?_
  calc ∑ i : Fin 3, (eLpNorm (∂[i] (correctionField D R s τ)) 2 volume).toReal
      ≤ ∑ _i : Fin 3, 3 * (‖L‖ * D.ancientRadius) := Finset.sum_le_sum fun i _ ↦ hnorm i
    _ = 3 * (3 * (‖L‖ * D.ancientRadius)) := by simp

/-- **The derivative of the cutoff part is bounded in `L²`** uniformly in `t > 0`. -/
theorem exists_toReal_eLpNorm_fderiv_physicalCutoffField_le (hR : 0 < R) :
    ∃ B : ℝ, ∀ t > 0, (eLpNorm (fderiv ℝ (physicalCutoffField D R t)) 2 volume).toReal ≤ B := by
  set W := localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R
  obtain ⟨C, hCtop, hC⟩ := eLpNorm_iteratedFDeriv_gaussianFlow_le (n := 3) (E := ℝ^3) 0
    (p := 2) one_le_two le_rfl
  refine ⟨∑ i : Fin 3, C.toReal * (eLpNorm (∂[i] W) 2 volume).toReal, fun t ht ↦ ?_⟩
  have hW (i : Fin 3) := memLp_partialDeriv_localizationRemainder (D := D) hR i
  have hmem (i : Fin 3) : MemLp (∂[i] (physicalCutoffField D R t)) 2 volume := by
    rw [partialDeriv_physicalCutoffField hR ht]
    exact (memLp_gaussianFlow ht one_le_two le_rfl (hW i)).neg
  refine (PDE.toReal_eLpNorm_fderiv_le_sum ((contDiff_physicalCutoffField t).of_le (by simp))
    one_le_two hmem).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  have hG := memLp_gaussianFlow ht one_le_two le_rfl (hW i)
  have h₀ : eLpNorm (gaussianFlow t (∂[i] W)) 2 volume =
      eLpNorm (iteratedFDeriv ℝ 0 (gaussianFlow t (∂[i] W))) 2 volume := by
    refine eLpNorm_congr_norm_ae hG.aestronglyMeasurable ?_
      (Eventually.of_forall fun x ↦ by rw [norm_iteratedFDeriv_zero])
    exact (memLp_iteratedFDeriv_gaussianFlow ht one_le_two le_rfl (hW i) 0).aestronglyMeasurable
  have hb := hC ht (hW i)
  rw [← h₀] at hb
  simp only [CharP.cast_eq_zero, zero_div, neg_zero, sub_self, mul_zero,
    Real.rpow_zero, ENNReal.ofReal_one, mul_one] at hb
  rw [partialDeriv_physicalCutoffField hR ht, eLpNorm_neg]
  calc (eLpNorm (gaussianFlow t (∂[i] W)) 2 volume).toReal
      ≤ (C * eLpNorm (∂[i] W) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hCtop (hW i).eLpNorm_ne_top) hb
    _ = C.toReal * (eLpNorm (∂[i] W) 2 volume).toReal := ENNReal.toReal_mul

/-- `(t^{-1/2})^{1/2} = t^{-1/4}` for the physical factor at `log t`. -/
theorem physicalFactor_log_rpow_half {t : ℝ} (ht : 0 < t) :
    physicalFactor (Real.log t) ^ (1 / 2 : ℝ) = t ^ (-(1 / 4) : ℝ) := by
  rw [physicalFactor, ← Real.exp_mul, Real.rpow_def_of_pos ht]
  ring_nf

/-- The correction part of the physical velocity is the dilation of the correction field. -/
theorem physicalCorrectionField_eq_dilateField {t : ℝ} (ht : 0 < t) :
    physicalCorrectionField D R s t =
      dilateField (physicalFactor (Real.log t)) (correctionField D R s (Real.log t)) := by
  funext x
  rw [physicalCorrectionField, dilateField, physicalFactor_log ht]

/-- **The `L²` bound of the derivative of the velocity slices.** Above the threshold radius and
for `s ∈ [0, 1]` there are constants `A`, `B` with `‖Du(t)‖_{L²} ≤ A t^{-1/4} + B` on `(0, 1]`. -/
theorem exists_toReal_eLpNorm_fderiv_velocitySlice_le (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ A B : ℝ, ∀ t ∈ Ioc (0 : ℝ) 1,
      (eLpNorm (fderiv ℝ (velocitySlice (physicalVelocity D R s) t)) 2 volume).toReal ≤
        A * t ^ (-(1 / 4) : ℝ) + B := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (D.one_le_ancientThreshold.trans hR)
  obtain ⟨M, hM⟩ := exists_toReal_eLpNorm_fderiv_correctionField_le hR hs
  obtain ⟨B, hB⟩ := exists_toReal_eLpNorm_fderiv_physicalCutoffField_le (D := D) hR0
  refine ⟨(eLpNorm (fderiv ℝ D.U) 2 volume).toReal + M, B, fun t ht ↦ ?_⟩
  have hτ : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2
  have ha : 0 < physicalFactor (Real.log t) := physicalFactor_pos _
  have hP := memLp_fderiv_physicalProfileField (D := D) t
  have hC := memLp_fderiv_physicalCutoffField (D := D) hR0 ht.1
  have hK := memLp_fderiv_physicalCorrectionField hR hs ht.1 ht.2
  have hmeas : AEStronglyMeasurable (fderiv ℝ (velocitySlice (physicalVelocity D R s) t)) volume :=
    ((contDiff_velocitySlice_physicalVelocity hR hs ht.1 ht.2).continuous_fderiv
      (by simp)).aestronglyMeasurable
  have hsplit := fderiv_velocitySlice_physicalVelocity hR hs ht.1 ht.2
  have h₁ : eLpNorm (fderiv ℝ (velocitySlice (physicalVelocity D R s) t)) 2 volume ≤
      eLpNorm (fun x ↦ (‖fderiv ℝ (physicalProfileField D t) x‖ +
        ‖fderiv ℝ (physicalCutoffField D R t) x‖) +
          ‖fderiv ℝ (physicalCorrectionField D R s t) x‖) 2 volume := by
    refine eLpNorm_mono_real hmeas fun x ↦ ?_
    rw [hsplit, Pi.add_apply, Pi.add_apply]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have h₂ : eLpNorm (fun x ↦ (‖fderiv ℝ (physicalProfileField D t) x‖ +
        ‖fderiv ℝ (physicalCutoffField D R t) x‖) +
          ‖fderiv ℝ (physicalCorrectionField D R s t) x‖) 2 volume ≤
      (eLpNorm (fun x ↦ ‖fderiv ℝ (physicalProfileField D t) x‖) 2 volume +
        eLpNorm (fun x ↦ ‖fderiv ℝ (physicalCutoffField D R t) x‖) 2 volume) +
          eLpNorm (fun x ↦ ‖fderiv ℝ (physicalCorrectionField D R s t) x‖) 2 volume :=
    (eLpNorm_add_le (μ := volume) (p := 2) one_le_two).trans
      (add_le_add (eLpNorm_add_le (μ := volume) (p := 2) one_le_two) le_rfl)
  rw [eLpNorm_norm _ hP.aestronglyMeasurable, eLpNorm_norm _ hC.aestronglyMeasurable,
    eLpNorm_norm _ hK.aestronglyMeasurable] at h₂
  have hfin := ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hP.eLpNorm_ne_top,
    hC.eLpNorm_ne_top⟩, hK.eLpNorm_ne_top⟩
  refine (ENNReal.toReal_mono hfin (h₁.trans h₂)).trans ?_
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hP.eLpNorm_ne_top, hC.eLpNorm_ne_top⟩)
    hK.eLpNorm_ne_top, ENNReal.toReal_add hP.eLpNorm_ne_top hC.eLpNorm_ne_top]
  have eP : (eLpNorm (fderiv ℝ (physicalProfileField D t)) 2 volume).toReal =
      t ^ (-(1 / 4) : ℝ) * (eLpNorm (fderiv ℝ D.U) 2 volume).toReal := by
    rw [physicalProfileField, toReal_eLpNorm_fderiv_dilateField D.contDiff_U ha,
      physicalFactor_log_rpow_half ht.1]
  have eK : (eLpNorm (fderiv ℝ (physicalCorrectionField D R s t)) 2 volume).toReal ≤
      t ^ (-(1 / 4) : ℝ) * M := by
    rw [physicalCorrectionField_eq_dilateField ht.1,
      toReal_eLpNorm_fderiv_dilateField (contDiff_correctionField hR hs hτ) ha,
      physicalFactor_log_rpow_half ht.1]
    exact mul_le_mul_of_nonneg_left (hM _ hτ).2 (Real.rpow_nonneg ht.1.le _)
  rw [eP]
  have hCt := hB t ht.1
  nlinarith [eK, hCt]

/-- The squared `L²` norm of the derivative of the velocity slices is integrable on `(0, 1]`. -/
theorem integrableOn_sq_eLpNorm_fderiv_velocitySlice_physicalVelocity (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (fun t ↦ (eLpNorm (fderiv ℝ (velocitySlice (physicalVelocity D R s) t)) 2
      volume).toReal ^ 2) (Ioc 0 1) := by
  obtain ⟨A, B, hAB⟩ := exists_toReal_eLpNorm_fderiv_velocitySlice_le hR hs
  have hmeas := aestronglyMeasurable_sq_eLpNorm_fderiv_velocitySlice (T := 1)
    (u := physicalVelocity D R s) fun z hz ↦
      ((physical_time_regularity D R s hR hs).2 z hz).of_le (by simp)
  have hint : IntegrableOn (fun t : ℝ ↦ 2 * A ^ 2 * t ^ (-(1 / 2) : ℝ) + 2 * B ^ 2) (Ioc 0 1) := by
    refine Integrable.add (Integrable.const_mul ?_ _) (integrableOn_const (by simp))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  refine Integrable.mono' hint hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := hAB t ht
  have h0 : 0 ≤ (eLpNorm (fderiv ℝ (velocitySlice (physicalVelocity D R s) t)) 2 volume).toReal :=
    ENNReal.toReal_nonneg
  have hq : (t ^ (-(1 / 4) : ℝ)) ^ 2 = t ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
    norm_num
  calc (eLpNorm (fderiv ℝ (velocitySlice (physicalVelocity D R s) t)) 2 volume).toReal ^ 2
      ≤ (A * t ^ (-(1 / 4) : ℝ) + B) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ ≤ 2 * A ^ 2 * t ^ (-(1 / 2) : ℝ) + 2 * B ^ 2 := by
        rw [← hq]
        nlinarith [sq_nonneg (A * t ^ (-(1 / 4) : ℝ) - B)]

end NavierStokes.Nonuniqueness
