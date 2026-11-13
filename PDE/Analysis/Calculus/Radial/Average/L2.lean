/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Radial.Average.Basic
public import PDE.Analysis.Operator.IntegralKernelOperator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Square-integrable radial averages

The radial Poisson equation replaces division by the radius with an average
along the segment from the axis. For `n > 0`, the average has a triangular
integral kernel with row mass `1/(n+1)` and column mass `1/n`. Schur's estimate
therefore controls the average on the physical radial measure `dr`, without a
vanishing trace or an assumed square-integrable quotient.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Calculus

private def radialAverageKernel (n : ℕ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 ∧ p.2 < p.1 then p.2 ^ n / p.1 ^ (n + 1) else 0

private theorem radialAverageKernel_nonneg (n : ℕ) (r s : ℝ) :
    0 ≤ radialAverageKernel n (r, s) := by
  unfold radialAverageKernel
  split_ifs with h
  · exact div_nonneg (pow_nonneg h.1.le _) (pow_nonneg (h.1.trans h.2).le _)
  · exact le_rfl

private theorem measurable_radialAverageKernel (n : ℕ) :
    Measurable (radialAverageKernel n) := by
  unfold radialAverageKernel
  apply Measurable.ite
  · exact (isOpen_lt continuous_const continuous_snd).measurableSet.inter
      (isOpen_lt continuous_snd continuous_fst).measurableSet
  · fun_prop
  · fun_prop

private theorem radialAverageKernel_row (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun s ↦ radialAverageKernel n (r, s)) (volume.restrict (Ioi 0)) ∧
      (∫ s in Ioi 0, radialAverageKernel n (r, s)) = 1 / ((n : ℝ) + 1) := by
  have heq : (fun s ↦ radialAverageKernel n (r, s)) =
      (Ioo 0 r).indicator (fun s ↦ s ^ n / r ^ (n + 1)) := by
    funext s
    simp only [radialAverageKernel, mem_Ioo, indicator_apply]
  rw [heq]
  have hi : IntegrableOn (fun s : ℝ ↦ s ^ n / r ^ (n + 1)) (Ioo 0 r) :=
    ((show Continuous (fun s : ℝ ↦ s ^ n / r ^ (n + 1)) by
      fun_prop).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hfull : Integrable ((Ioo 0 r).indicator (fun s : ℝ ↦ s ^ n / r ^ (n + 1))) :=
    (integrable_indicator_iff measurableSet_Ioo).mpr hi
  refine ⟨hfull.restrict, ?_⟩
  rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo]
  have hset : Ioo (0 : ℝ) r ∩ Ioi 0 = Ioo 0 r := by ext s; simp; tauto
  rw [hset, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hr.le, intervalIntegral.integral_div,
    integral_pow]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hrn : r ^ (n + 1) ≠ 0 := pow_ne_zero _ hr.ne'
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero]
  field_simp

private theorem radialAverageKernel_column (n : ℕ) (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    Integrable (fun r ↦ radialAverageKernel n (r, s)) (volume.restrict (Ioi 0)) ∧
      (∫ r in Ioi 0, radialAverageKernel n (r, s)) = 1 / (n : ℝ) := by
  have hexp : -(n + 1 : ℝ) < -1 := by exact_mod_cast (show -(n + 1 : ℤ) < -1 by omega)
  have hpow (r : ℝ) : r ^ (-(n + 1 : ℝ)) = (r ^ (n + 1))⁻¹ := by
    rw [Real.rpow_neg_eq_inv_rpow,
      show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by simp,
      Real.rpow_natCast, inv_pow]
  have heq : (fun r ↦ radialAverageKernel n (r, s)) =
      (Ioi s).indicator (fun r ↦ s ^ n / r ^ (n + 1)) := by
    funext r
    simp only [radialAverageKernel, hs, true_and, mem_Ioi, indicator_apply]
  rw [heq]
  have hi : IntegrableOn (fun r : ℝ ↦ s ^ n / r ^ (n + 1)) (Ioi s) := by
    apply ((integrableOn_Ioi_rpow_of_lt hexp hs).const_mul (s ^ n)).congr
    filter_upwards [] with r
    rw [hpow, div_eq_mul_inv]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hi).restrict, ?_⟩
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi s ∩ Ioi 0 = Ioi s := by ext r; simp; grind
  rw [hset]
  have heq' : (fun r : ℝ ↦ s ^ n / r ^ (n + 1)) =
      (fun r ↦ s ^ n * r ^ (-(n + 1 : ℝ))) := by
    funext r
    rw [hpow, div_eq_mul_inv]
  rw [heq', integral_const_mul, integral_Ioi_rpow_of_lt hexp hs]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hs' : s ^ n ≠ 0 := pow_ne_zero _ hs.ne'
  have he : (-(n + 1 : ℝ) + 1) = -(n : ℝ) := by ring
  rw [he, Real.rpow_neg hs.le, Real.rpow_natCast]
  field_simp

/-- The triangular kernel is the radial average after the substitution `s = tr`.
This change of variables is valid for the totalized integral as well. -/
private theorem radialAverageKernel_integral (n : ℕ) (f : ℝ → ℝ) {r : ℝ}
    (hr : 0 < r) :
    (∫ s in Ioi 0, radialAverageKernel n (r, s) * f s) =
      weightedRadialAverage f n r := by
  have heq : (fun s ↦ radialAverageKernel n (r, s) * f s) =
      (Ioo 0 r).indicator (fun s ↦ s ^ n / r ^ (n + 1) * f s) := by
    funext s
    simp only [radialAverageKernel, mem_Ioo, indicator_apply, ite_mul, zero_mul]
  rw [heq, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  have hset : Ioo (0 : ℝ) r ∩ Ioi 0 = Ioo 0 r := by ext s; simp; tauto
  rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
  have hfactor : (fun s : ℝ ↦ s ^ n / r ^ (n + 1) * f s) =
      (fun s ↦ (r ^ (n + 1))⁻¹ * (s ^ n * f s)) := by
    funext s
    ring
  rw [hfactor, intervalIntegral.integral_const_mul]
  have hscale : (∫ s in (0 : ℝ)..r, s ^ n * f s) =
      r ^ (n + 1) * weightedRadialAverage f n r := by
    have hsub := intervalIntegral.smul_integral_comp_mul_right
      (fun s : ℝ ↦ s ^ n * f s) (a := 0) (b := 1) r
    simp only [zero_mul, one_mul, smul_eq_mul] at hsub
    rw [← hsub]
    have hinner : (fun t : ℝ ↦ (t * r) ^ n * f (t * r)) =
        (fun t ↦ r ^ n * (t ^ n * f (t * r))) := by
      funext t
      rw [mul_pow]
      ring
    rw [hinner, intervalIntegral.integral_const_mul, pow_succ]
    unfold weightedRadialAverage
    ring
  rw [hscale, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]

/-- A power-weighted radial average is a bounded operator on `L²(dr)` for
every positive integer power. Its norm is at most `sqrt(1/(n(n+1)))`.
The operator represents the actual segment average on all L² inputs. -/
theorem exists_weightedRadialAverageL2 (n : ℕ) (hn : 0 < n) :
    ∃ T : Lp ℝ 2 (volume.restrict (Ioi (0 : ℝ))) →L[ℝ]
        Lp ℝ 2 (volume.restrict (Ioi (0 : ℝ))),
      ‖T‖ ≤ √(1 / (((n : ℝ) + 1) * n)) ∧
      ∀ (f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Ioi 0))),
        (T (hf.toLp f) : ℝ → ℝ) =ᵐ[volume.restrict (Ioi 0)]
          weightedRadialAverage f n := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  have hK : AEStronglyMeasurable (radialAverageKernel n) (ν.prod ν) :=
    (measurable_radialAverageKernel n).aestronglyMeasurable
  have hrow : ∀ᵐ r ∂ν,
      (∫⁻ s, ENNReal.ofReal ‖radialAverageKernel n (r, s)‖ ∂ν) ≤
        ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    obtain ⟨hi, heq⟩ := radialAverageKernel_row n hr
    simp only [Real.norm_eq_abs, abs_of_nonneg (radialAverageKernel_nonneg n r _)]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (radialAverageKernel_nonneg n r)), heq]
  have hcolumn : ∀ᵐ s ∂ν,
      (∫⁻ r, ENNReal.ofReal ‖radialAverageKernel n (r, s)‖ ∂ν) ≤
        ENNReal.ofReal (1 / (n : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    obtain ⟨hi, heq⟩ := radialAverageKernel_column n hn hs
    simp only [Real.norm_eq_abs, abs_of_nonneg (radialAverageKernel_nonneg n _ s)]
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun r ↦ radialAverageKernel_nonneg n r s), heq]
  have hA : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hB : 0 ≤ 1 / (n : ℝ) := by positivity
  let T := integralKernelL2OfSchur (E := ℝ) hK hA hB hrow hcolumn
  refine ⟨T, ?_, ?_⟩
  · calc
      ‖T‖ ≤ √((1 / ((n : ℝ) + 1)) * (1 / (n : ℝ))) :=
        norm_integralKernelL2OfSchur_le (E := ℝ) hK hA hB hrow hcolumn
      _ = √(1 / (((n : ℝ) + 1) * n)) := by
        rw [div_mul_div_comm, one_mul]
  · intro f hf
    have hrep := integralKernelL2OfSchur_toLp_ae (E := ℝ) hK hA hB hrow hcolumn hf
    filter_upwards [hrep, ae_restrict_mem measurableSet_Ioi] with r hr hrpos
    exact hr.trans (by simpa only [smul_eq_mul] using radialAverageKernel_integral n f hrpos)

/-- The actual radial average is square integrable, with the Schur norm bound.
This form can be applied to each axial slice of a physical profile. -/
theorem weightedRadialAverage_memLp_and_lpNorm_le (n : ℕ) (hn : 0 < n)
    {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    MemLp (weightedRadialAverage f n) 2 (volume.restrict (Ioi (0 : ℝ))) ∧
      lpNorm (weightedRadialAverage f n) 2 (volume.restrict (Ioi (0 : ℝ))) ≤
        √(1 / (((n : ℝ) + 1) * n)) *
          lpNorm f 2 (volume.restrict (Ioi (0 : ℝ))) := by
  obtain ⟨T, hT, hactual⟩ := exists_weightedRadialAverageL2 n hn
  have ha := hactual f hf
  have hg := MemLp.ae_eq ha (Lp.memLp (T (hf.toLp f)))
  refine ⟨hg, ?_⟩
  calc
    _ = ‖T (hf.toLp f)‖ := by
      rw [← toReal_eLpNorm, Lp.norm_def, eLpNorm_congr_ae ha]
    _ ≤ √(1 / (((n : ℝ) + 1) * n)) * ‖hf.toLp f‖ :=
      T.le_of_opNorm_le hT _
    _ = _ := by rw [Lp.norm_toLp, toReal_eLpNorm]

/-- Integrating the square of a radial average costs at most `1/(n(n+1))`.
Both square integrability and the estimate follow from the input L² condition. -/
theorem weightedRadialAverage_integrable_sq_and_integral_le (n : ℕ) (hn : 0 < n)
    {f : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (fun r ↦ weightedRadialAverage f n r ^ 2)
        (volume.restrict (Ioi (0 : ℝ))) ∧
      (∫ r in Ioi (0 : ℝ), weightedRadialAverage f n r ^ 2) ≤
        (1 / (((n : ℝ) + 1) * n)) * (∫ r in Ioi (0 : ℝ), f r ^ 2) := by
  obtain ⟨hg, hnorm⟩ := weightedRadialAverage_memLp_and_lpNorm_le n hn hf
  refine ⟨hg.integrable_sq, ?_⟩
  rw [hg.integral_sq_eq_lpNorm_sq, hf.integral_sq_eq_lpNorm_sq]
  have hC : 0 ≤ 1 / (((n : ℝ) + 1) * n) := by positivity
  calc
    _ ≤ (√(1 / (((n : ℝ) + 1) * n)) *
        lpNorm f 2 (volume.restrict (Ioi (0 : ℝ)))) ^ 2 :=
      (sq_le_sq₀ lpNorm_nonneg (mul_nonneg (Real.sqrt_nonneg _) lpNorm_nonneg)).2
        hnorm
    _ = _ := by rw [mul_pow, Real.sq_sqrt hC]

/-- Radial averaging has the same L² bound after integration in the axial
variable. Fubini supplies almost every input slice and derives integrability
of the averaged profile from the one-dimensional estimate. -/
theorem weightedRadialAverage_prod_memLp_and_lpNorm_le (n : ℕ) (hn : 0 < n)
    {f : ℝ × ℝ → ℝ} (hcont : Continuous f)
    (hf : MemLp f 2 ((volume.restrict (Ioi (0 : ℝ))).prod volume)) :
    MemLp (fun p : ℝ × ℝ ↦ weightedRadialAverage (fun r ↦ f (r, p.2)) n p.1)
        2 ((volume.restrict (Ioi (0 : ℝ))).prod volume) ∧
      lpNorm (fun p : ℝ × ℝ ↦ weightedRadialAverage (fun r ↦ f (r, p.2)) n p.1)
        2 ((volume.restrict (Ioi (0 : ℝ))).prod volume) ≤
        √(1 / (((n : ℝ) + 1) * n)) *
          lpNorm f 2 ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let C : ℝ := 1 / (((n : ℝ) + 1) * n)
  let g (p : ℝ × ℝ) := weightedRadialAverage (fun r ↦ f (r, p.2)) n p.1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgm : AEStronglyMeasurable g (ν.prod volume) := by
    have hc : Continuous (fun q : (ℝ × ℝ) × ℝ ↦
        q.2 ^ n * f (q.2 * q.1.1, q.1.2)) := by fun_prop
    have hm : AEStronglyMeasurable
        (fun q : (ℝ × ℝ) × ℝ ↦ q.2 ^ n * f (q.2 * q.1.1, q.1.2))
        ((ν.prod volume).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
      hc.aestronglyMeasurable
    simpa only [g, weightedRadialAverage, intervalIntegral.integral_of_le zero_le_one]
      using hm.integral_prod_right'
  have hslices : ∀ᵐ z ∂(volume : Measure ℝ),
      Integrable (fun r ↦ g (r, z) ^ 2) ν ∧
        (∫ r, g (r, z) ^ 2 ∂ν) ≤ C * (∫ r, f (r, z) ^ 2 ∂ν) := by
    filter_upwards [hf.integrable_sq.prod_left_ae] with z hz
    have hzmeas : AEStronglyMeasurable (fun r ↦ f (r, z)) ν :=
      (hcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    exact weightedRadialAverage_integrable_sq_and_integral_le n hn
      ((memLp_two_iff_integrable_sq hzmeas).2 hz)
  have houter : Integrable (fun z ↦ ∫ r, g (r, z) ^ 2 ∂ν) :=
    (hf.integrable_sq.integral_prod_right.const_mul C).mono_nonneg
      (hgm.pow 2).prod_swap.integral_prod_right'
      (Filter.Eventually.of_forall fun z ↦ integral_nonneg fun r ↦ sq_nonneg (g (r, z)))
      (hslices.mono fun _ h ↦ h.2)
  have hgi : Integrable (fun p ↦ g p ^ 2) (ν.prod volume) := by
    apply (integrable_prod_iff' (hgm.pow 2)).2
    refine ⟨hslices.mono fun _ h ↦ h.1, ?_⟩
    simpa only [Real.norm_eq_abs, Pi.pow_apply, abs_pow, sq_abs] using houter
  have hg : MemLp g 2 (ν.prod volume) := (memLp_two_iff_integrable_sq hgm).2 hgi
  have hint : (∫ p, g p ^ 2 ∂ν.prod volume) ≤ C * (∫ p, f p ^ 2 ∂ν.prod volume) := by
    calc
      _ = ∫ z, ∫ r, g (r, z) ^ 2 ∂ν := integral_prod_symm _ hgi
      _ ≤ ∫ z, C * (∫ r, f (r, z) ^ 2 ∂ν) :=
        integral_mono_ae houter (hf.integrable_sq.integral_prod_right.const_mul C)
          (hslices.mono fun _ h ↦ h.2)
      _ = _ := by rw [integral_const_mul, ← integral_prod_symm _ hf.integrable_sq]
  refine ⟨hg, ?_⟩
  apply (sq_le_sq₀ lpNorm_nonneg (mul_nonneg (Real.sqrt_nonneg C) lpNorm_nonneg)).1
  rw [mul_pow, Real.sq_sqrt hC, ← hg.integral_sq_eq_lpNorm_sq,
    ← hf.integral_sq_eq_lpNorm_sq]
  exact hint

end PDE.Calculus
