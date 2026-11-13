/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Construction.RegularizedEvolution
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Bochner bounds for the regularized heat equation

The H¹ trajectory and its smoothed H² state have separate bounds. The L²
velocity estimate follows from the equation and the bounded weak
Laplacian H² → L². All bounds are independent of the smoothing scale.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal InnerProductSpace Sobolev

variable {n : ℕ} {ε δ a b : ℝ}
  {F : ℝ → DerivLp n 2 univ} {q : W^{1,2}(ℝ^n)}

/-- The unmollified H¹ state has a uniform Bochner energy bound. -/
theorem regularized_heat_integral_norm_sq_le
    (hε : 0 < ε) (hδ : 0 < δ) (hab : a ≤ b)
    (hf : MemLp F 2 (volume.restrict (Ioc a b)))
    (U : AffineCaratheodorySolutionOn (fun _ ↦ ε • regularizedLaplacianCLM 1 hδ)
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t)) a b q) :
    (∫ t in a..b, ‖U.trajectory t‖ ^ 2) ≤
      (b - a) * Real.exp (b - a) *
        (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) := by
  let K := ‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2
  have hK : 0 ≤ K := by
    have hi : 0 ≤ ∫ s in a..b, ‖F s‖ ^ 2 :=
      intervalIntegral.integral_nonneg hab fun _ _ ↦ sq_nonneg _
    positivity
  have hU : ContinuousOn U.trajectory (Icc a b) := by
    simpa only [uIcc_of_le hab] using U.absolutely_continuous.continuousOn
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) :
      ‖U.trajectory t‖ ^ 2 ≤ K * Real.exp (b - a) :=
    (regularized_heat_norm_sq_le hε hδ hab hf U t ht).trans
      (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (sub_le_sub_right ht.2 a)) hK)
  have hi := intervalIntegral.integral_mono_on hab
    ((hU.norm.pow 2).intervalIntegrable_of_Icc hab)
    (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ ↦ K * Real.exp (b - a)) volume a b) hpoint
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  change _ ≤ (b - a) * Real.exp (b - a) * K
  calc
    _ ≤ (b - a) * (K * Real.exp (b - a)) := hi
    _ = _ := by ring

/-- Diffusion controls the smoothed H² state in Bochner L². The
unordered native H² norm is bounded using the ordered Hessian comparison. -/
theorem regularized_heat_integral_smoothing_sq_le
    (hε : 0 < ε) (hδ : 0 < δ) (hab : a ≤ b)
    (hf : MemLp F 2 (volume.restrict (Ioc a b)))
    (U : AffineCaratheodorySolutionOn (fun _ ↦ ε • regularizedLaplacianCLM 1 hδ)
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t)) a b q) :
    ε * (∫ t in a..b,
      ‖mollifierSmoothingCLM 2 (standardMollifier n) hδ
        (wkpBaseCoordinateCLM (U.trajectory t))‖ ^ 2) ≤
      (1 + (1 + ε) * (b - a) * Real.exp (b - a)) *
        (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2) := by
  have hU : ContinuousOn U.trajectory (Icc a b) := by
    simpa only [uIcc_of_le hab] using U.absolutely_continuous.continuousOn
  have he : IntervalIntegrable (fun t ↦ ‖U.trajectory t‖ ^ 2) volume a b :=
    (hU.norm.pow 2).intervalIntegrable_of_Icc hab
  have hd : IntervalIntegrable (fun t ↦
      ⟪U.trajectory t, regularizedLaplacianCLM 1 hδ (U.trajectory t)⟫_ℝ) volume a b :=
    (hU.inner (𝕜 := ℝ) ((regularizedLaplacianCLM 1 hδ).continuous.comp_continuousOn hU))
      |>.intervalIntegrable_of_Icc hab
  have hv : IntervalIntegrable (fun t ↦
      ‖mollifierSmoothingCLM 2 (standardMollifier n) hδ
        (wkpBaseCoordinateCLM (U.trajectory t))‖ ^ 2) volume a b :=
    (((mollifierSmoothingCLM 2 (standardMollifier n) hδ).continuous.comp_continuousOn
      (wkpBaseCoordinateCLM.continuous.comp_continuousOn hU)).norm.pow 2)
        |>.intervalIntegrable_of_Icc hab
  have hi := intervalIntegral.integral_mono_on hab hv (he.sub hd)
    (fun t _ ↦ norm_mollifierSmoothingCLM_two_sq_le hδ (U.trajectory t))
  rw [intervalIntegral.integral_sub he hd] at hi
  have hu := regularized_heat_integral_norm_sq_le hε hδ hab hf U
  have hdis := regularized_heat_integral_dissipation_le hε hδ hab hf U
  rw [intervalIntegral.integral_neg] at hdis
  nlinarith [mul_le_mul_of_nonneg_left hi hε.le, mul_le_mul_of_nonneg_left hu hε.le]

/-- The projected velocity is bounded by the smoothed H² state and
the original L² forcing, with no derivative of the forcing. -/
theorem norm_base_regularized_heat_sq_le (hε : 0 < ε) (hδ : 0 < δ)
    (U : W^{1,2}(ℝ^n)) (F : DerivLp n 2 univ) :
    ‖wkpBaseCoordinateCLM (ε • regularizedLaplacianCLM 1 hδ U +
      mollifierSmoothingCLM 1 (standardMollifier n) hδ F)‖ ^ 2 ≤
      2 * ε ^ 2 * ‖(wkpLaplacianCLM :
        W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)‖ ^ 2 *
        ‖mollifierSmoothingCLM 2 (standardMollifier n) hδ
          (wkpBaseCoordinateCLM U)‖ ^ 2 + 2 * ‖F‖ ^ 2 := by
  let V := mollifierSmoothingCLM 2 (standardMollifier n) hδ (wkpBaseCoordinateCLM U)
  let L : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpLaplacianCLM
  have hn :
      ‖wkpBaseCoordinateCLM (ε • regularizedLaplacianCLM 1 hδ U +
        mollifierSmoothingCLM 1 (standardMollifier n) hδ F)‖ ≤
      ε * ‖L‖ * ‖V‖ + ‖F‖ := by
    rw [map_add, map_smul, regularizedLaplacianCLM_base, mollifierSmoothingCLM_base]
    apply (norm_add_le _ _).trans
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    exact add_le_add
      ((mul_le_mul_of_nonneg_left
        ((norm_mollifierRowCLM_apply_le _ _ _).trans (L.le_opNorm V)) hε.le).trans_eq
          (mul_assoc ε ‖L‖ ‖V‖).symm)
      (norm_mollifierRowCLM_apply_le _ _ _)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  change _ ≤ 2 * ε ^ 2 * ‖L‖ ^ 2 * ‖V‖ ^ 2 + 2 * ‖F‖ ^ 2
  nlinarith [sq_nonneg (ε * ‖L‖ * ‖V‖ - ‖F‖)]

/-- The time integral of the L² velocity is bounded uniformly in the
auxiliary smoothing scale. The physical diffusivity may be any positive number. -/
theorem regularized_heat_integral_velocity_sq_le
    (hε : 0 < ε) (hδ : 0 < δ) (hab : a ≤ b)
    (hf : MemLp F 2 (volume.restrict (Ioc a b)))
    (U : AffineCaratheodorySolutionOn (fun _ ↦ ε • regularizedLaplacianCLM 1 hδ)
      (fun t ↦ mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t)) a b q) :
    (∫ t in a..b,
      ‖wkpBaseCoordinateCLM (ε • regularizedLaplacianCLM 1 hδ (U.trajectory t) +
        mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t))‖ ^ 2) ≤
      2 * ε * ‖(wkpLaplacianCLM :
        W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)‖ ^ 2 *
        ((1 + (1 + ε) * (b - a) * Real.exp (b - a)) *
          (‖q‖ ^ 2 + (1 + (n : ℝ) / ε) * ∫ s in a..b, ‖F s‖ ^ 2)) +
        2 * ∫ s in a..b, ‖F s‖ ^ 2 := by
  have hU : ContinuousOn U.trajectory (Icc a b) := by
    simpa only [uIcc_of_le hab] using U.absolutely_continuous.continuousOn
  have hu := hU.memLp_of_subset_isCompact isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self
    (p := 2) (μ := volume)
  have hv := (mollifierSmoothingCLM 2 (standardMollifier n) hδ).comp_memLp'
    (wkpBaseCoordinateCLM.comp_memLp' hu)
  have hg := wkpBaseCoordinateCLM.comp_memLp'
    (((ε • regularizedLaplacianCLM 1 hδ).comp_memLp' hu).add
      ((mollifierSmoothingCLM 1 (standardMollifier n) hδ).comp_memLp' hf))
  have hfsq : IntervalIntegrable (fun t ↦ ‖F t‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hf.integrable_norm_pow (by norm_num)
  have hvsq : IntervalIntegrable (fun t ↦
      ‖mollifierSmoothingCLM 2 (standardMollifier n) hδ
        (wkpBaseCoordinateCLM (U.trajectory t))‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hv.integrable_norm_pow (by norm_num)
  have hgsq : IntervalIntegrable (fun t ↦
      ‖wkpBaseCoordinateCLM (ε • regularizedLaplacianCLM 1 hδ (U.trajectory t) +
        mollifierSmoothingCLM 1 (standardMollifier n) hδ (F t))‖ ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact hg.integrable_norm_pow (by norm_num)
  let C := 2 * ε ^ 2 * ‖(wkpLaplacianCLM :
    W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)‖ ^ 2
  have hi := intervalIntegral.integral_mono_on hab hgsq
    ((hvsq.const_mul C).add (hfsq.const_mul 2))
    (fun t _ ↦ norm_base_regularized_heat_sq_le hε hδ (U.trajectory t) (F t))
  rw [intervalIntegral.integral_add (hvsq.const_mul C) (hfsq.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have hb := regularized_heat_integral_smoothing_sq_le hε hδ hab hf U
  have hm := mul_le_mul_of_nonneg_left hb (show
    0 ≤ 2 * ε * ‖(wkpLaplacianCLM :
      W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)‖ ^ 2 by positivity)
  dsimp only [C] at hi
  nlinarith

end PDE.Parabolic.Heat
