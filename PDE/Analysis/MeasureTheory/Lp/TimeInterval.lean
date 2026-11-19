/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Analysis.MeasureTheory.Lp.IntegralPower
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Fourth-power norms on time intervals

Continuity of prefix integrals gives continuity of the L4 prefix norm. Mathlib’s
improper-integral criterion then upgrades bounded prefix norms to membership on
the whole half-open time interval.
-/

@[expose] public section

open Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

/-- Local fourth-power integrability makes the L4 prefix norm continuous. -/
theorem continuousOn_lpNorm_restrict_Icc_four {f : ℝ → ℝ} {s t : ℝ}
    (hf : Measurable f) (hlocal : MemLp f 4 (volume.restrict (Icc s t))) :
    ContinuousOn (fun r ↦ lpNorm f 4 (volume.restrict (Icc s r))) (Icc s t) := by
  have hp := hlocal.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hc := (intervalIntegral.continuousOn_primitive_Icc hp).rpow_const
    (fun _ _ ↦ Or.inr (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹))
  convert hc using 1
  ext r
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num


/-- Uniform bounds on preterminal L4 prefix norms imply L4 membership on the
half-open interval. No regularity or integrability at the terminal time is assumed. -/
theorem memLp_four_Ico_of_prefix_bound {f : ℝ → ℝ} {s T B : ℝ}
    (hsT : s < T) (hf : Measurable f)
    (hlocal : ∀ t ∈ Ico s T, MemLp f 4 (volume.restrict (Icc s t)))
    (hbound : ∀ t ∈ Ico s T, lpNorm f 4 (volume.restrict (Icc s t)) ≤ B) :
    MemLp f 4 (volume.restrict (Ico s T)) := by
  obtain ⟨a, -, ha, hlim⟩ := exists_seq_strictMono_tendsto' hsT
  have hp : IntegrableOn (fun t ↦ ‖f t‖ ^ 4) (Ioc s T) := by
    apply integrableOn_Ioc_of_intervalIntegral_norm_bounded_right (I := B ^ 4)
      (b := a) (l := atTop)
    · intro n
      exact IntegrableOn.mono_set
        ((hlocal (a n) ⟨(ha n).1.le, (ha n).2⟩).integrable_norm_pow
          (by norm_num : (4 : ℕ) ≠ 0)) Ioc_subset_Icc_self
    · exact hlim
    · apply Filter.Eventually.of_forall
      intro n
      rw [← integral_Icc_eq_integral_Ioc]
      simp only [norm_pow, norm_norm]
      rw [integral_norm_pow_eq_lpNorm_pow hf.aestronglyMeasurable (by norm_num : 0 < (4 : ℕ))]
      exact pow_le_pow_left₀ lpNorm_nonneg (hbound (a n) ⟨(ha n).1.le, (ha n).2⟩) 4
  have hp' : IntegrableOn (fun t ↦ ‖f t‖ ^ 4) (Ico s T) :=
    (integrableOn_Icc_iff_integrableOn_Ico).mp
      ((integrableOn_Icc_iff_integrableOn_Ioc).mpr hp)
  have he := (memLp_norm_rpow_iff (μ := volume.restrict (Ico s T)) (p := (4 : ℝ≥0∞)) (q := 4)
    hf.aestronglyMeasurable (by norm_num) (by norm_num)).mp
  apply he
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, ENNReal.div_self (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ∞)] using memLp_one_iff_integrable.mpr hp'

end MeasureTheory
