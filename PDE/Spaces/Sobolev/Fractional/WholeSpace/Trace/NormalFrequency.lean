/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.NormalKernel
public import PDE.Common.Euclidean
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Isometric normal-frequency lifting

The tangential Bessel scale is `sqrt (1 + ‖ξ‖²)`. Multiplying a boundary Fourier
coordinate by the normalized normal kernel embeds its `L²` space isometrically
into the product-frequency `L²` space. Fubini's theorem and the Cauchy density
normalization prove the norm equality.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace SobolevSpace.Fractional.Trace

variable {n : ℕ}

/-- The positive tangential scale in the Bessel weight. -/
def tangentialScale (ξ : ℝ^n) : ℝ≥0 :=
  ⟨Real.sqrt (1 + ‖ξ‖ ^ 2), Real.sqrt_nonneg _⟩

/-- The inhomogeneous Bessel scale never vanishes. -/
theorem tangentialScale_ne_zero (ξ : ℝ^n) : tangentialScale ξ ≠ 0 := by
  have h : 0 < Real.sqrt (1 + ‖ξ‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  exact ne_of_gt h

/-- Joint measurability of the frequency kernel. -/
theorem measurable_normalKernel_tangentialScale :
    Measurable (fun z : ℝ^n × ℝ ↦ normalKernel (tangentialScale z.1) z.2) := by
  unfold normalKernel ProbabilityTheory.cauchyPDFReal tangentialScale
  fun_prop

/-- The pointwise normal-frequency lift of a boundary coordinate. -/
def normalLiftFun (v : Lp ℂ 2 (volume : Measure ℝ^n)) (z : ℝ^n × ℝ) : ℂ :=
  normalKernel (tangentialScale z.1) z.2 • v z.1

private theorem normalLiftFun_norm_sq (v : Lp ℂ 2 (volume : Measure ℝ^n))
    (z : ℝ^n × ℝ) :
    ‖normalLiftFun v z‖ ^ 2 = normalKernel (tangentialScale z.1) z.2 ^ 2 * ‖v z.1‖ ^ 2 := by
  rw [normalLiftFun, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (normalKernel_nonneg _ _), mul_pow]

private theorem integrable_normalLiftFun_norm_sq_slice
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) (ξ : ℝ^n) :
    Integrable (fun t : ℝ ↦ ‖normalLiftFun v (ξ, t)‖ ^ 2) := by
  simp_rw [normalLiftFun_norm_sq]
  exact (memLp_normalKernel (tangentialScale ξ)).integrable_sq.mul_const _

private theorem integral_normalLiftFun_norm_sq_slice
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) (ξ : ℝ^n) :
    ∫ t : ℝ, ‖normalLiftFun v (ξ, t)‖ ^ 2 = ‖v ξ‖ ^ 2 := by
  simp_rw [normalLiftFun_norm_sq]
  rw [integral_mul_const, integral_normalKernel_sq _ (tangentialScale_ne_zero ξ), one_mul]

private theorem aestronglyMeasurable_normalLiftFun
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    AEStronglyMeasurable (normalLiftFun v) (volume.prod volume) :=
  measurable_normalKernel_tangentialScale.aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable v).comp_fst

private theorem integrable_normalLiftFun_norm_sq
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    Integrable (fun z ↦ ‖normalLiftFun v z‖ ^ 2) (volume.prod volume) := by
  apply (integrable_prod_iff ((aestronglyMeasurable_normalLiftFun v).norm.pow 2)).2
  constructor
  · exact Filter.Eventually.of_forall (integrable_normalLiftFun_norm_sq_slice v)
  · change Integrable (fun ξ : ℝ^n ↦ ∫ t : ℝ, ‖‖normalLiftFun v (ξ, t)‖ ^ 2‖) volume
    simp_rw [norm_pow, norm_norm,
      integral_normalLiftFun_norm_sq_slice]
    exact (Lp.memLp v).norm.integrable_sq

/-- The normal-frequency lift is square integrable. -/
theorem memLp_normalLiftFun (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    MemLp (normalLiftFun v) 2 volume := by
  rw [Measure.volume_eq_prod]
  exact (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_normalLiftFun v)).2
    (integrable_normalLiftFun_norm_sq v)

/-- The normal-frequency lift as an element of `L²`. -/
def normalLift (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    Lp ℂ 2 (volume : Measure (ℝ^n × ℝ)) :=
  (memLp_normalLiftFun v).toLp (normalLiftFun v)

/-- The `L²` lifting agrees almost everywhere with multiplication by the kernel. -/
theorem normalLift_apply_ae (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    normalLift v =ᵐ[volume] normalLiftFun v :=
  (memLp_normalLiftFun v).coeFn_toLp

/-- Normal-frequency lifting preserves the norm, with constant exactly one. -/
theorem norm_normalLift (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    ‖normalLift v‖ = ‖v‖ := by
  have hs : ‖normalLift v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq, Lp.norm_sq_eq_integral_norm_sq]
    calc
      _ = ∫ z, ‖normalLiftFun v z‖ ^ 2 :=
        integral_congr_ae ((normalLift_apply_ae v).fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))
      _ = ∫ ξ, ∫ t, ‖normalLiftFun v (ξ, t)‖ ^ 2 := by
        rw [Measure.volume_eq_prod]
        exact integral_prod _ (integrable_normalLiftFun_norm_sq v)
      _ = _ := by simp_rw [integral_normalLiftFun_norm_sq_slice]
  nlinarith [norm_nonneg (normalLift v), norm_nonneg v]

/-- Normal-frequency lifting is complex linear and isometric. -/
def normalLiftLI (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ^n) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n × ℝ)) where
  toFun := normalLift
  map_add' v w := by
    apply Lp.ext
    have ha := (Lp.coeFn_add v w).comp_tendsto
      (Measure.quasiMeasurePreserving_fst (μ := volume)
        (ν := (volume : Measure ℝ))).tendsto_ae
    rw [← Measure.volume_eq_prod] at ha
    filter_upwards [normalLift_apply_ae (v + w), normalLift_apply_ae v, normalLift_apply_ae w,
      Lp.coeFn_add (normalLift v) (normalLift w), ha] with z h1 h2 h3 h4 h5
    simp only [Function.comp_apply, Pi.add_apply] at h4 h5
    rw [h1, h4, h2, h3]
    simp only [normalLiftFun, h5, smul_add]
  map_smul' c v := by
    apply Lp.ext
    have ha := (Lp.coeFn_smul c v).comp_tendsto
      (Measure.quasiMeasurePreserving_fst (μ := volume)
        (ν := (volume : Measure ℝ))).tendsto_ae
    rw [← Measure.volume_eq_prod] at ha
    filter_upwards [normalLift_apply_ae (c • v), normalLift_apply_ae v,
      Lp.coeFn_smul c (normalLift v), ha] with z h1 h2 h3 h4
    change normalLift (c • v) z = (c • normalLift v) z
    simp only [Function.comp_apply, Pi.smul_apply] at h3 h4
    rw [h1, h3, h2]
    simp only [normalLiftFun, h4]
    exact smul_comm _ _ _
  norm_map' := norm_normalLift

end SobolevSpace.Fractional.Trace
