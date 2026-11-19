/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Regularity
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Differentiating scaled convolution

The derivative in scale and position falls on the smooth real kernel, even when the
normed-space-valued input is only locally Bochner integrable. Compact support is uniform
on a neighborhood of the scale.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Convolution Topology

namespace SobolevSpace.Approximation

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- At a fixed positive scale, the joint kernel derivative has compact spatial support. -/
theorem hasCompactSupport_fderiv_scaled_joint (μ : Mollifier n) {t : ℝ} (ht : 0 < t) :
    HasCompactSupport
      (fun y : ℝ^n ↦ fderiv ℝ (fun q : ℝ × ℝ^n ↦ scaled μ q.1 q.2) (t, y)) := by
  obtain ⟨k, hk, hks⟩ := exists_compact_scaled_support μ (t + 1)
  apply exists_compact_iff_hasCompactSupport.mp
  refine ⟨k, hk, fun y hy ↦ ?_⟩
  apply (hasFDerivAt_zero_of_eventually_const 0 ?_).fderiv
  have hs : Ioo 0 (t + 1) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨ht, lt_add_one _⟩
  have hy' : kᶜ ∈ 𝓝 y := hk.isClosed.isOpen_compl.mem_nhds hy
  rw [nhds_prod_eq]
  filter_upwards [prod_mem_prod hs hy'] with q hq
  exact hks q.1 q.2 hq.1 hq.2

/-- The joint derivative of mollification is the convolution with the joint kernel
derivative. Neither the scale nor the spatial derivative falls on the input. -/
theorem fderiv_mollifyVector_scale_apply (μ : Mollifier n) {g : ℝ^n → F}
    (hg : LocallyIntegrable g volume) {t : ℝ} (ht : 0 < t) (x : ℝ^n)
    (v : ℝ × ℝ^n) :
    fderiv ℝ (fun q : ℝ × ℝ^n ↦ mollifyVector μ q.1 g q.2) (t, x) v =
      ∫ y, fderiv ℝ (fun q : ℝ × ℝ^n ↦ scaled μ q.1 q.2) (t, y) v • g (x - y) := by
  obtain ⟨k, hk, hks⟩ := exists_compact_scaled_support μ (t + 1)
  have hdiff := hasFDerivAt_convolution_right_with_param
    (ContinuousLinearMap.lsmul ℝ ℝ).flip (μ := (volume : Measure (ℝ^n)))
    isOpen_Ioo hk hks hg
    (((contDiffOn_scaled μ).mono (prod_mono Ioo_subset_Ioi_self Subset.rfl)).of_le
      (by simp)) (t, x) ⟨ht, lt_add_one _⟩
  have heq : (fun q : ℝ × ℝ^n ↦
      (g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume] scaled μ q.1) q.2) =
      (fun q : ℝ × ℝ^n ↦ mollifyVector μ q.1 g q.2) := by
    funext q
    rw [convolution_flip]
    rfl
  rw [heq] at hdiff
  rw [hdiff.fderiv]
  have hc : Continuous
      (fun y : ℝ^n ↦ fderiv ℝ (fun q : ℝ × ℝ^n ↦ scaled μ q.1 q.2) (t, y)) :=
    ((contDiffOn_scaled μ).continuousOn_fderiv_of_isOpen
      (isOpen_Ioi.prod isOpen_univ) (by simp)).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ ↦ ⟨ht, mem_univ _⟩)
  change ((g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip.precompR (ℝ × ℝ^n), volume]
    (fun y ↦ fderiv ℝ (fun q : ℝ × ℝ^n ↦ scaled μ q.1 q.2) (t, y))) x) v = _
  rw [convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ).flip hg
    (hasCompactSupport_fderiv_scaled_joint μ ht) hc, convolution_flip]
  rfl

/-- Dilation cancels the kernel normalization in a convolution integral, leaving the
single inverse scale contributed by a derivative. -/
theorem integral_scaled_profile_smul (ψ : ℝ^n → ℝ) (g : ℝ^n → F) {t : ℝ} (ht : 0 < t)
    (x : ℝ^n) :
    (∫ y, ((t⁻¹)^n * t⁻¹ * ψ (t⁻¹ • y)) • g (x - y)) =
      t⁻¹ • ∫ z, ψ z • g (x - t • z) := by
  let f : ℝ^n → F := fun z ↦ ψ z • g (x - t • z)
  have heq (y : ℝ^n) :
      ((t⁻¹)^n * t⁻¹ * ψ (t⁻¹ • y)) • g (x - y) =
        ((t⁻¹)^n * t⁻¹) • f (t⁻¹ • y) := by
    simp only [f, smul_inv_smul₀ ht.ne']
    rw [mul_smul]
  simp_rw [heq]
  rw [integral_smul]
  have hfinrank : Module.finrank ℝ (ℝ^n) = n := by simp
  have hscale : (∫ y, f (t⁻¹ • y)) = t^n • ∫ z, f z := by
    simpa only [hfinrank] using
      (Measure.integral_comp_inv_smul_of_nonneg
        (μ := (volume : Measure (ℝ^n))) (f := f) ht.le)
  rw [hscale]
  calc
    (t⁻¹ ^ n * t⁻¹) • (t ^ n • ∫ z, f z) =
        (t⁻¹ ^ n * t ^ n) • (t⁻¹ • ∫ z, f z) := by
      simp only [smul_smul]
      congr 1
      ac_rfl
    _ = t⁻¹ • ∫ z, f z := by
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero n ht.ne'), one_smul]

end SobolevSpace.Approximation
