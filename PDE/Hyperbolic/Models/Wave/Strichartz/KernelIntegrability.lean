/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.KernelBilinear
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

/-!
# Absolute integrability of the spacetime kernel pairing

Finite dual mixed norms imply absolute integrability on the full product of two
time and two spatial variables. The proof uses the positive pairing bound and Tonelli.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace WaveEquation.Strichartz

/-- The exterior Newtonian kernel is jointly measurable in radius and position. -/
theorem measurable_exteriorNewtonKernel_uncurry :
    Measurable (fun z : ℝ × ℝ^3 ↦ exteriorNewtonKernel z.1 z.2) := by
  simp only [exteriorNewtonKernel, indicator_apply, mem_ofPred_eq]
  apply Measurable.ite (measurableSet_lt measurable_fst measurable_snd.norm)
  · exact measurable_snd.norm.inv
  · exact measurable_const

private theorem measurable_spacetime_exteriorNewtonKernel_mul
    {F G : ℝ × ℝ^3 → ℝ} (hF : Measurable F) (hG : Measurable G) :
    Measurable (fun z : ℝ × ℝ × ℝ^3 × ℝ^3 ↦ exteriorNewtonKernel |z.1 - z.2.1| (z.2.2.1 - z.2.2.2) *
      F (z.2.1, z.2.2.2) * G (z.1, z.2.2.1)) := by
  have hK : Measurable (fun z : ℝ × ℝ × ℝ^3 × ℝ^3 ↦
      exteriorNewtonKernel |z.1 - z.2.1| (z.2.2.1 - z.2.2.2)) := by
    simp only [exteriorNewtonKernel, indicator_apply, mem_ofPred_eq]
    apply Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
    · fun_prop
    · fun_prop
  have hm : Measurable (fun z : ℝ × ℝ × ℝ^3 × ℝ^3 ↦
      exteriorNewtonKernel |z.1 - z.2.1| (z.2.2.1 - z.2.2.2) *
        F (z.2.1, z.2.2.2) * G (z.1, z.2.2.1)) := by
    apply (hK.mul (hF.comp (by fun_prop))).mul (hG.comp (by fun_prop))
  exact hm

private theorem lintegral_prod_four {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] {μ : Measure α} {ν : Measure β} {ρ : Measure γ}
    {σ : Measure δ} [SFinite ν] [SFinite ρ] [SFinite σ] {f : α × β × γ × δ → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ z, f z ∂μ.prod (ν.prod (ρ.prod σ))) =
      ∫⁻ a, ∫⁻ b, ∫⁻ c, ∫⁻ d, f (a, b, c, d) ∂σ ∂ρ ∂ν ∂μ := by
  rw [lintegral_prod _ hf.aemeasurable]
  refine lintegral_congr fun a ↦ ?_
  have ha : Measurable (fun z : β × γ × δ ↦ f (a, z)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ ha.aemeasurable]
  refine lintegral_congr fun b ↦ ?_
  exact lintegral_prod _ (ha.comp (measurable_const.prodMk measurable_id)).aemeasurable

private theorem lintegral_enorm_spacetime_exteriorNewtonKernel_mul
    {F G : ℝ × ℝ^3 → ℝ} (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ z : ℝ × ℝ × ℝ^3 × ℝ^3,
      ‖exteriorNewtonKernel |z.1 - z.2.1| (z.2.2.1 - z.2.2.2) *
        F (z.2.1, z.2.2.2) * G (z.1, z.2.2.1)‖ₑ
      ∂volume.prod (volume.prod (volume.prod volume))) =
    ∫⁻ t : ℝ, ∫⁻ s : ℝ, ∫⁻ x : ℝ^3,
      (∫⁻ y : ℝ^3, ‖exteriorNewtonKernel |t - s| (x - y)‖ₑ * ‖F (s, y)‖ₑ) *
        ‖G (t, x)‖ₑ := by
  have hm := measurable_spacetime_exteriorNewtonKernel_mul hF hG
  rw [lintegral_prod_four hm.enorm]
  refine lintegral_congr fun t ↦ ?_
  refine lintegral_congr fun s ↦ ?_
  refine lintegral_congr fun x ↦ ?_
  simp only [enorm_mul]
  exact lintegral_mul_const _ (((measurable_exteriorNewtonKernel |t - s|).comp
      (measurable_const.sub measurable_id)).enorm.mul (hF.comp measurable_prodMk_left).enorm)

/-- Finite mixed-norm data make the full spacetime kernel pairing absolutely integrable. -/
theorem integrable_spacetime_exteriorNewtonKernel_mul
    {F G : ℝ × ℝ^3 → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFfin : MemLp (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume)
    (hGfin : MemLp (fun t ↦ eLpNorm (fun x ↦ G (t, x)) (12 / 11) volume) (4 / 3) volume) :
    Integrable (fun z : ℝ × ℝ × ℝ^3 × ℝ^3 ↦ exteriorNewtonKernel |z.1 - z.2.1| (z.2.2.1 - z.2.2.2) *
      F (z.2.1, z.2.2.2) * G (z.1, z.2.2.1)) (volume.prod (volume.prod (volume.prod volume))) := by
  have hm := measurable_spacetime_exteriorNewtonKernel_mul hF hG
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_enorm_spacetime_exteriorNewtonKernel_mul hF hG]
  have hbound := lintegral_spacetime_exteriorNewtonKernel_mul_le hF.enorm hG.enorm
  have hFnorm (s : ℝ) : eLpNorm (fun y ↦ ‖F (s, y)‖ₑ) (12 / 11) volume =
      eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume :=
    eLpNorm_enorm _ (hF.comp measurable_prodMk_left).aestronglyMeasurable
  have hGnorm (t : ℝ) : eLpNorm (fun x ↦ ‖G (t, x)‖ₑ) (12 / 11) volume =
      eLpNorm (fun x ↦ G (t, x)) (12 / 11) volume :=
    eLpNorm_enorm _ (hG.comp measurable_prodMk_left).aestronglyMeasurable
  simp_rw [hFnorm, hGnorm] at hbound
  apply hbound.trans_lt
  apply ENNReal.mul_lt_top _ hGfin
  apply ENNReal.mul_lt_top _ hFfin
  apply ENNReal.mul_lt_top
  · apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  · apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      finiteness
    · finiteness

end WaveEquation.Strichartz
