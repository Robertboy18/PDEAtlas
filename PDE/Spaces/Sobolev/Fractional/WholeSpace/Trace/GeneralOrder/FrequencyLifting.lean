/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.NormalIntegral
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.NormalFrequency
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# General-order lifting in product-frequency coordinates

The normal kernel at scale `sqrt (1 + ‖ξ‖²)` embeds boundary `L²` isometrically
into product-frequency `L²`. Fubini and the unit normal integral establish
this norm identity in every boundary dimension, including dimension zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace SobolevSpace.Fractional.Trace.GeneralOrder

variable {n : ℕ} {s : ℝ}

/-- The general-order kernel at the tangential Bessel scale. -/
def frequencyKernel (s : ℝ) (ξ : ℝ^n) (t : ℝ) : ℝ :=
  normalKernel s (tangentialScale ξ) t

theorem frequencyKernel_nonneg (s : ℝ) (ξ : ℝ^n) (t : ℝ) :
    0 ≤ frequencyKernel s ξ t := normalKernel_nonneg s _ t

theorem frequencyKernel_neg (s : ℝ) (ξ : ℝ^n) (t : ℝ) :
    frequencyKernel s (-ξ) (-t) = frequencyKernel s ξ t := by
  simp only [frequencyKernel, normalKernel, tangentialScale, norm_neg, neg_sq]

theorem measurable_frequencyKernel (s : ℝ) :
    Measurable (fun z : ℝ^n × ℝ ↦ frequencyKernel s z.1 z.2) := by
  unfold frequencyKernel normalKernel tangentialScale
  fun_prop

theorem memLp_frequencyKernel (hs : 1 / 2 < s) (ξ : ℝ^n) :
    MemLp (frequencyKernel s ξ) 2 volume :=
  memLp_normalKernel hs _ (tangentialScale_ne_zero ξ)

theorem integral_frequencyKernel_sq (hs : 1 / 2 < s) (ξ : ℝ^n) :
    ∫ t : ℝ, frequencyKernel s ξ t ^ 2 = 1 :=
  integral_normalKernel_sq hs _ (tangentialScale_ne_zero ξ)

theorem integrable_frequencyKernel_smul (hs : 1 / 2 < s)
    (ξ : ℝ^n) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun t ↦ frequencyKernel s ξ t • f t) :=
  integrable_normalKernel_smul hs _ (tangentialScale_ne_zero ξ) hf

theorem norm_integral_frequencyKernel_smul_sq_le (hs : 1 / 2 < s)
    (ξ : ℝ^n) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖∫ t, frequencyKernel s ξ t • f t‖ ^ 2 ≤ ∫ t, ‖f t‖ ^ 2 :=
  norm_integral_normalKernel_smul_sq_le hs _ (tangentialScale_ne_zero ξ) hf

/-- Multiplication by the normalized kernel along each normal-frequency line. -/
def frequencyLiftFun (s : ℝ) (v : Lp ℂ 2 (volume : Measure ℝ^n))
    (z : ℝ^n × ℝ) : ℂ :=
  frequencyKernel s z.1 z.2 • v z.1

private theorem frequencyLiftFun_norm_sq (v : Lp ℂ 2 (volume : Measure ℝ^n))
    (z : ℝ^n × ℝ) :
    ‖frequencyLiftFun s v z‖ ^ 2 = frequencyKernel s z.1 z.2 ^ 2 * ‖v z.1‖ ^ 2 := by
  rw [frequencyLiftFun, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (frequencyKernel_nonneg _ _ _), mul_pow]

private theorem integrable_frequencyLiftFun_norm_sq_slice (hs : 1 / 2 < s)
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) (ξ : ℝ^n) :
    Integrable (fun t : ℝ ↦ ‖frequencyLiftFun s v (ξ, t)‖ ^ 2) := by
  simp_rw [frequencyLiftFun_norm_sq]
  exact (memLp_frequencyKernel hs ξ).integrable_sq.mul_const _

private theorem integral_frequencyLiftFun_norm_sq_slice (hs : 1 / 2 < s)
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) (ξ : ℝ^n) :
    ∫ t : ℝ, ‖frequencyLiftFun s v (ξ, t)‖ ^ 2 = ‖v ξ‖ ^ 2 := by
  simp_rw [frequencyLiftFun_norm_sq]
  rw [integral_mul_const, integral_frequencyKernel_sq hs, one_mul]

private theorem aestronglyMeasurable_frequencyLiftFun
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    AEStronglyMeasurable (frequencyLiftFun s v) (volume.prod volume) :=
  (measurable_frequencyKernel s).aestronglyMeasurable.smul
    (Lp.aestronglyMeasurable v).comp_fst

private theorem integrable_frequencyLiftFun_norm_sq (hs : 1 / 2 < s)
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    Integrable (fun z ↦ ‖frequencyLiftFun s v z‖ ^ 2) (volume.prod volume) := by
  apply (integrable_prod_iff ((aestronglyMeasurable_frequencyLiftFun v).norm.pow 2)).2
  constructor
  · exact Filter.Eventually.of_forall (integrable_frequencyLiftFun_norm_sq_slice hs v)
  · change Integrable (fun ξ : ℝ^n ↦ ∫ t : ℝ, ‖‖frequencyLiftFun s v (ξ, t)‖ ^ 2‖) volume
    simp_rw [norm_pow, norm_norm, integral_frequencyLiftFun_norm_sq_slice hs]
    exact (Lp.memLp v).norm.integrable_sq

theorem memLp_frequencyLiftFun (hs : 1 / 2 < s)
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) : MemLp (frequencyLiftFun s v) 2 volume := by
  rw [Measure.volume_eq_prod]
  exact (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_frequencyLiftFun v)).2
    (integrable_frequencyLiftFun_norm_sq hs v)

/-- The normalized lifting as a product-frequency `L²` element. -/
def frequencyLift (hs : 1 / 2 < s) (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    Lp ℂ 2 (volume : Measure (ℝ^n × ℝ)) :=
  (memLp_frequencyLiftFun hs v).toLp (frequencyLiftFun s v)

theorem frequencyLift_apply_ae (hs : 1 / 2 < s)
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    frequencyLift hs v =ᵐ[volume] frequencyLiftFun s v :=
  (memLp_frequencyLiftFun hs v).coeFn_toLp

theorem norm_frequencyLift (hs : 1 / 2 < s) (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    ‖frequencyLift hs v‖ = ‖v‖ := by
  have hsq : ‖frequencyLift hs v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq, Lp.norm_sq_eq_integral_norm_sq]
    calc
      _ = ∫ z, ‖frequencyLiftFun s v z‖ ^ 2 :=
        integral_congr_ae ((frequencyLift_apply_ae hs v).fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))
      _ = ∫ ξ, ∫ t, ‖frequencyLiftFun s v (ξ, t)‖ ^ 2 := by
        rw [Measure.volume_eq_prod]
        exact integral_prod _ (integrable_frequencyLiftFun_norm_sq hs v)
      _ = _ := by simp_rw [integral_frequencyLiftFun_norm_sq_slice hs]
  nlinarith [norm_nonneg (frequencyLift hs v), norm_nonneg v]

/-- The kernel lifting is a complex linear isometry. -/
def frequencyLiftLI (n : ℕ) (hs : 1 / 2 < s) :
    Lp ℂ 2 (volume : Measure ℝ^n) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n × ℝ)) where
  toFun := frequencyLift hs
  map_add' v w := by
    apply Lp.ext
    have ha := (Lp.coeFn_add v w).comp_tendsto
      (Measure.quasiMeasurePreserving_fst (μ := volume)
        (ν := (volume : Measure ℝ))).tendsto_ae
    rw [← Measure.volume_eq_prod] at ha
    filter_upwards [frequencyLift_apply_ae hs (v + w), frequencyLift_apply_ae hs v,
      frequencyLift_apply_ae hs w, Lp.coeFn_add (frequencyLift hs v) (frequencyLift hs w),
      ha] with z h1 h2 h3 h4 h5
    simp only [Function.comp_apply, Pi.add_apply] at h4 h5
    rw [h1, h4, h2, h3]
    simp only [frequencyLiftFun, h5, smul_add]
  map_smul' c v := by
    apply Lp.ext
    have ha := (Lp.coeFn_smul c v).comp_tendsto
      (Measure.quasiMeasurePreserving_fst (μ := volume)
        (ν := (volume : Measure ℝ))).tendsto_ae
    rw [← Measure.volume_eq_prod] at ha
    filter_upwards [frequencyLift_apply_ae hs (c • v), frequencyLift_apply_ae hs v,
      Lp.coeFn_smul c (frequencyLift hs v), ha] with z h1 h2 h3 h4
    change frequencyLift hs (c • v) z = (c • frequencyLift hs v) z
    simp only [Function.comp_apply, Pi.smul_apply] at h3 h4
    rw [h1, h3, h2]
    simp only [frequencyLiftFun, h4]
    exact smul_comm _ _ _
  norm_map' := norm_frequencyLift hs

end SobolevSpace.Fractional.Trace.GeneralOrder
