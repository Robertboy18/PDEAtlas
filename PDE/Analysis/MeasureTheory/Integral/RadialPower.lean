/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.RadialPower
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Radial weights on balls

Translation and Haar scaling reduce every radial-power ball integral to the unit
ball. Combining this identity with Hölder's inequality gives weighted estimates
with their radius dependence explicit. The dimensional integrability condition
allows singular weights without imposing pointwise bounds on the function.
-/

@[expose] public section

open Metric Set
open scoped ENNReal Pointwise

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Radial powers have the expected scaling on a ball for every real exponent.
Finiteness of the integral is supplied separately by the dimensional criterion. -/
theorem integral_norm_rpow_ball (μ : Measure E) [μ.IsAddHaarMeasure]
    (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x in ball (0 : E) r, ‖x‖ ^ a ∂μ) =
      r ^ ((Module.finrank ℝ E : ℝ) + a) * ∫ x in ball (0 : E) 1, ‖x‖ ^ a ∂μ := by
  have h := μ.setIntegral_comp_smul_of_pos (fun x : E ↦ ‖x‖ ^ a)
    (ball (0 : E) 1) hr
  rw [_root_.smul_ball hr.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hr, mul_one,
    smul_eq_mul] at h
  have hscale (x : E) : ‖r • x‖ ^ a = r ^ a * ‖x‖ ^ a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      Real.mul_rpow hr.le (norm_nonneg x)]
  simp_rw [hscale] at h
  rw [integral_const_mul] at h
  rw [Real.rpow_add hr, Real.rpow_natCast]
  have hpow : r ^ Module.finrank ℝ E ≠ 0 := pow_ne_zero _ hr.ne'
  calc
    _ = r ^ Module.finrank ℝ E *
        ((r ^ Module.finrank ℝ E)⁻¹ * ∫ x in ball (0 : E) r, ‖x‖ ^ a ∂μ) := by
      rw [← mul_assoc, mul_inv_cancel₀ hpow, one_mul]
    _ = _ := by rw [← h]; ring

/-- Translation leaves the radial-power ball integral unchanged; dilation supplies
its entire radius dependence. -/
theorem integral_norm_sub_rpow_ball (μ : Measure E) [μ.IsAddHaarMeasure]
    (c : E) (a : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x in ball c r, ‖x - c‖ ^ a ∂μ) =
      r ^ ((Module.finrank ℝ E : ℝ) + a) * ∫ x in ball (0 : E) 1, ‖x‖ ^ a ∂μ := by
  have h := (measurePreserving_add_left μ c).setIntegral_preimage_emb
    (Homeomorph.addLeft c).measurableEmbedding (fun x : E ↦ ‖x - c‖ ^ a) (ball c r)
  have hpre : (fun x : E ↦ c + x) ⁻¹' ball c r = ball (0 : E) r := by
    ext x
    simp [mem_ball, dist_eq_norm]
  rw [hpre] at h
  simp only [add_sub_cancel_left] at h
  rw [← h]
  exact integral_norm_rpow_ball μ a hr

/-- Hölder controls a radial weighted integral, including its dependence on the
ball radius. The dimensional condition proves the weight's Lᑫ membership. In dimension zero the
weight vanishes, since `a > 0` there. -/
theorem integral_norm_mul_norm_sub_rpow_le
    {p q a r : ℝ} (hpq : p.HolderConjugate q)
    (ha : -a * q < (Module.finrank ℝ E : ℝ)) (hr : 0 < r) (c : E)
    {f : E → ℝ} (hf : MemLp f (ENNReal.ofReal p) (μ.restrict (ball c r))) :
    (∫ x in ball c r, |f x| * ‖x - c‖ ^ a ∂μ) ≤
      (∫ x in ball c r, |f x| ^ p ∂μ) ^ (1 / p) *
        ((∫ x in ball (0 : E) 1, ‖x‖ ^ (a * q) ∂μ) ^ (1 / q) *
          r ^ ((Module.finrank ℝ E : ℝ) / q + a)) := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hd0 | hd
  · have : Subsingleton E := Module.finrank_zero_iff.mp hd0
    have ha0 : 0 < a := by
      have hq := hpq.symm.pos
      rw [hd0, Nat.cast_zero] at ha
      nlinarith
    have hzero : (∫ x in ball c r, |f x| * ‖x - c‖ ^ a ∂μ) = 0 :=
      integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x ↦ by
        simp [Subsingleton.elim x c, Real.zero_rpow ha0.ne'])
    rw [hzero]
    exact mul_nonneg (Real.rpow_nonneg (integral_nonneg fun x ↦
        Real.rpow_nonneg (abs_nonneg _) _) _)
      (mul_nonneg (Real.rpow_nonneg (integral_nonneg fun x ↦
        Real.rpow_nonneg (norm_nonneg x) _) _) (Real.rpow_nonneg hr.le _))
  have hg : MemLp (fun x : E ↦ ‖x - c‖ ^ a) (ENNReal.ofReal q)
      (μ.restrict (ball c r)) :=
    memLp_norm_sub_rpow_of_isBounded hd (by simpa using hpq.symm.pos)
      ENNReal.ofReal_ne_top (by simpa only [ENNReal.toReal_ofReal hpq.symm.nonneg] using ha)
      c isBounded_ball
  have h := integral_mul_norm_le_Lp_mul_Lq hpq hf hg
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _)] at h
  rw [integral_norm_sub_rpow_ball μ c (a * q) hr] at h
  rw [Real.mul_rpow (Real.rpow_nonneg hr.le _) (integral_nonneg fun x ↦
    Real.rpow_nonneg (norm_nonneg x) _), ← Real.rpow_mul hr.le] at h
  have hexp : ((Module.finrank ℝ E : ℝ) + a * q) * (1 / q) =
      (Module.finrank ℝ E : ℝ) / q + a := by
    field_simp [hpq.symm.ne_zero]
  rw [hexp, mul_comm (r ^ ((Module.finrank ℝ E : ℝ) / q + a))] at h
  exact h

end MeasureTheory
