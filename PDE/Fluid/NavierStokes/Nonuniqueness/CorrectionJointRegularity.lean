/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.CorrectionTimeRegularity
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.JointHigherRegularity

/-!
# Joint regularity of the correction field in physical variables

At every time `0 < t ≤ 1` the classical representative of the physical correction in vector
`Hᵐ⁺¹` is the correction part `t^{-1/2} U_cor(log t, x / √t)` of the physical velocity
(`classicalRepresentativeCLM_physicalCorrection`). Since the physical correction is a `C¹` path
on `(0, 1)` in vector `H⁴`, and `H⁴(ℝ³)` controls one derivative more than its classical
threshold, the correction part of the physical velocity is jointly `C¹` in `(t, x)` on
`(0, 1) × ℝ³` (`contDiffOn_one_physicalCorrectionField`), and at every point its time derivative
is its spatial Laplacian plus the continuous representative of the projected physical forcing,
`∂ₜ u_cor(t, x) = Δₓ u_cor(t, x) + (Π g(t))(x)` (`hasDerivAt_physicalCorrectionField`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology SobolevSpace SobolevSpace.GraphSpace
open HeatEquation.WholeSpace IncompressibleFlow PDE.Analysis.Evolution
open scoped NNReal ENNReal Sobolev Laplacian

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable {D : UnstableProfile} {R s : ℝ}

/-- At a time `0 < t ≤ 1` the classical representative of the physical correction is the
correction part `t^{-1/2} U_cor(log t, x / √t)` of the physical velocity. -/
theorem classicalRepresentativeCLM_physicalCorrection (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {m : ℕ} (hm : (3 : ℝ) < 2 * m) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (j : Fin 3) :
    (classicalRepresentativeCLM (three_lt_two_mul_succ_sub_one hm)
        (physicalCorrection D R s m hm t j) : ℝ^3 → ℝ) =
      fun x ↦ ((Real.sqrt t)⁻¹ • correctionField D R s (Real.log t) ((Real.sqrt t)⁻¹ • x)) j := by
  have hτ : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have hV := isCorrectionLift_correctionLift hR hs m hm
  have hf := physicalFactor_log ht
  symm
  refine eq_classicalRepresentativeCLM_of_ae_eq _ _ ?_ ?_
  · exact (PiLp.continuous_apply 2 _ j).comp
      (contDiff_physicalCorrectionField hR hs ht ht1).continuous
  · -- the base representative of the correction lift is the correction field
    have hbase : baseRepresentative (correctionLift D R s m hm (Real.log t) j) =ᵐ[volume]
        fun y ↦ correctionField D R s (Real.log t) y j := by
      have h := classicalRepresentativeCLM_ae (three_lt_two_mul_succ_sub_one hm)
        (correctionLift D R s m hm (Real.log t) j)
      rw [correctionField_eq_classicalRepresentative hV hτ]
      exact h.symm
    have hcomp := (Measure.quasiMeasurePreserving_smul volume
      (physicalFactor_pos (Real.log t)).ne').ae_eq_comp hbase
    have hdil := dilationWkpCLM_base_ae (by norm_num) (physicalFactor (Real.log t))
      (physicalFactor_pos (Real.log t)).ne' (correctionLift D R s m hm (Real.log t) j)
    have hsmul := baseRepresentative_smul_ae (physicalFactor (Real.log t))
      (dilationWkpCLM (by norm_num) (physicalFactor (Real.log t))
        (physicalFactor_pos (Real.log t)).ne' (correctionLift D R s m hm (Real.log t) j))
    simp only [domainMeasure, Measure.restrict_univ] at hsmul hdil
    change _ =ᵐ[volume] baseRepresentative (physicalFactor (Real.log t) •
      dilationWkpCLM (by norm_num) (physicalFactor (Real.log t))
        (physicalFactor_pos (Real.log t)).ne' (correctionLift D R s m hm (Real.log t) j))
    filter_upwards [hsmul, hdil, hcomp] with x h₁ h₂ h₃
    rw [h₁, h₂]
    simp only [Function.comp_apply] at h₃
    rw [h₃, ← hf, PiLp.smul_apply, smul_eq_mul]

/-- **Joint `C¹` regularity of the correction field.** Above the threshold radius and for
`s ∈ [0, 1]`, the correction part `t^{-1/2} U_cor(log t, x / √t)` of the physical velocity is
jointly continuously differentiable in `(t, x)` on `(0, 1) × ℝ³`. -/
theorem contDiffOn_one_physicalCorrectionField (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ^3 ↦
      (Real.sqrt p.1)⁻¹ • correctionField D R s (Real.log p.1) ((Real.sqrt p.1)⁻¹ • p.2))
      (Ioo 0 1 ×ˢ univ) := by
  have hm : (3 : ℝ) < 2 * ((3 : ℕ) : ℝ) := by norm_num
  have hk : ((3 : ℕ) : ℝ) < 2 * (((3 + 1 : ℕ) : ℝ) - 1) := three_lt_two_mul_succ_sub_one hm
  have hr : ((3 : ℕ) : ℝ) < 2 * (((3 + 1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) - 1) := by norm_num
  refine contDiffOn_piLp' 2 fun j ↦ ?_
  have hu : ContDiffOn ℝ (1 : ℕ) (fun t ↦ physicalCorrection D R s 3 hm t j) (Ioo 0 1) :=
    (contDiffOn_piLp 2).mp (by exact_mod_cast contDiffOn_one_physicalCorrection hR hs 3 hm) j
  have h := PDE.Hyperbolic.NonlinearWave.Cauchy.contDiffOn_joint_classicalRepresentative
    isOpen_Ioo hk hr hu
  refine (h.congr fun p hp ↦ ?_)
  have hp1 := hp.1
  have heq := congrFun (classicalRepresentativeCLM_physicalCorrection hR hs hm hp1.1 hp1.2.le j)
    p.2
  exact heq.symm

/-- **The pointwise equation of the correction field.** Above the threshold radius and for
`s ∈ [0, 1]`, at every `t ∈ (0, 1)` and `x ∈ ℝ³` each component of the correction part
`u_cor(t, x) = t^{-1/2} U_cor(log t, x / √t)` of the physical velocity has the time derivative
`Δₓ u_cor(t, x) + (Π g(t))(x)`, with the continuous representative of the projected physical
forcing in vector `H⁴`. -/
theorem hasDerivAt_physicalCorrectionField (hR : D.ancientThreshold ≤ R)
    (hs : s ∈ Icc (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : ℝ^3) (j : Fin 3) :
    HasDerivAt (fun t' ↦
        ((Real.sqrt t')⁻¹ • correctionField D R s (Real.log t') ((Real.sqrt t')⁻¹ • x)) j)
      (Δ (fun y ↦ ((Real.sqrt t)⁻¹ • correctionField D R s (Real.log t)
          ((Real.sqrt t)⁻¹ • y)) j) x +
        classicalRepresentativeCLM (three_lt_two_mul_succ_sub_one (by norm_num : (3 : ℝ) <
          2 * ((3 : ℕ) : ℝ))) (leraySobolev 3 (3 + 1) (physicalForcing D R s 3
            (by norm_num) t) j) x) t := by
  have hm : (3 : ℝ) < 2 * ((3 : ℕ) : ℝ) := by norm_num
  have hm₂ := three_lt_two_mul_succ (three_lt_two_mul_succ hm)
  have hk := three_lt_two_mul_succ_sub_one hm
  have hk₂ := three_lt_two_mul_succ_sub_one hm₂
  -- the evaluation of the `j`-th classical representative at `x`
  let E : VectorH 3 (3 + 1) →L[ℝ] ℝ := (BoundedContinuousFunction.evalCLM ℝ x).comp
    ((classicalRepresentativeCLM hk).comp (PiLp.proj 2 (𝕜 := ℝ) _ j))
  have hd := E.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_physicalCorrection hR hs hm ht)
  have heq : (fun t' ↦ ((Real.sqrt t')⁻¹ • correctionField D R s (Real.log t')
      ((Real.sqrt t')⁻¹ • x)) j) =ᶠ[𝓝 t] fun t' ↦ E (physicalCorrection D R s 3 hm t') := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t' ht'
    simp only [E, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
      BoundedContinuousFunction.evalCLM_apply]
    rw [classicalRepresentativeCLM_physicalCorrection hR hs hm ht'.1 ht'.2.le j]
  refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [E, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    BoundedContinuousFunction.evalCLM_apply, map_add, vectorLaplacian_apply]
  congr 1
  rw [← PDE.Hyperbolic.NonlinearWave.Cauchy.laplacian_classicalRepresentative hk₂ hk,
    classicalRepresentativeCLM_physicalCorrection hR hs hm₂ ht.1 ht.2.le j]

end NavierStokes.Nonuniqueness
