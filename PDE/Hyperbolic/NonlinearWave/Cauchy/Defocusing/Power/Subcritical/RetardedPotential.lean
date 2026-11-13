/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import PDE.Spaces.Sobolev.Inequalities.Hardy.Ball
import CAS.ExactTactic

/-!
# The subcritical retarded-potential estimate

For the three-dimensional power wave, the retarded source is integrated against inverse distance on
a ball. Hardy controls the first L² factor, and the L⁶ norm controls the cubic factor. An amplitude
bound contributes only the power `max (p - 4) 0`, which is sublinear precisely when `p < 5`. These
are (19)-(21) and the two cases of step 3 in the proof of Theorem 3 of Evans, §12.3.3, with Hardy's
inequality as Theorem 7 of §5.8.4.

The estimates apply to arbitrary H¹ ball functions, with no trace condition. The L⁶ hypothesis is
explicit, and the source is proved integrable.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.4, Theorem 7; §12.3.3, proof of Theorem 3,
  equations (19)-(21) and step 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The cubic factor absorbs every power up to four. Higher powers cost only
an amplitude factor with exponent `p - 4`. -/
theorem rpow_sub_one_le_amplitude_mul_cubic {p A a : ℝ}
    (hp : 1 ≤ p) (hA : 1 ≤ A) (ha : 0 ≤ a) (haA : a ≤ A) :
    a ^ (p - 1) ≤ A ^ max (p - 4) 0 * (1 + a ^ 3) := by
  have hq : 0 ≤ max (p - 4) 0 := le_max_right _ _
  have hAp : 1 ≤ A ^ max (p - 4) 0 := Real.one_le_rpow hA hq
  rcases le_or_gt a 1 with ha1 | ha1
  · have hsmall := Real.rpow_le_one ha ha1 (sub_nonneg.mpr hp)
    have hc : 1 ≤ 1 + a ^ 3 := le_add_of_nonneg_right (by positivity)
    exact hsmall.trans (one_le_mul_of_one_le_of_one_le hAp hc)
  · have hexp : p - 1 ≤ max (p - 4) 0 + 3 := by
      have := le_max_left (p - 4) 0
      linarith
    calc
      a ^ (p - 1) ≤ a ^ (max (p - 4) 0 + 3) := Real.rpow_le_rpow_of_exponent_le ha1.le hexp
      _ = a ^ max (p - 4) 0 * a ^ 3 := by
        cas using (zero_lt_one.trans ha1)
      _ ≤ A ^ max (p - 4) 0 * (1 + a ^ 3) :=
        mul_le_mul (Real.rpow_le_rpow ha haA hq) (by linarith)
          (by positivity) (Real.rpow_nonneg (zero_le_one.trans hA) _)

/-- An inverse-distance power potential is integrable and bounded by its two
L² factors. This applies to every real power at least one. -/
theorem integrable_power_potential_and_bound {r p A : ℝ} (hp : 1 ≤ p) (hA : 1 ≤ A) {f : ℝ^3 → ℝ}
    (hH : MemLp (fun x ↦ f x / ‖x‖) 2 (volume.restrict (ball 0 r)))
    (h6 : MemLp f 6 (volume.restrict (ball 0 r)))
    (hbound : ∀ᵐ x ∂volume.restrict (ball 0 r), |f x| ≤ A) :
    IntegrableOn (fun x ↦ |f x| ^ p / ‖x‖) (ball (0 : ℝ^3) r) ∧
      (∫ x in ball (0 : ℝ^3) r, |f x| ^ p / ‖x‖) ≤
        A ^ max (p - 4) 0 *
          √(∫ x in ball (0 : ℝ^3) r, f x ^ 2 / ‖x‖ ^ 2) *
          (√(volume.real (ball (0 : ℝ^3) r)) +
            √(∫ x in ball (0 : ℝ^3) r, |f x| ^ 6)) := by
  let μ := volume.restrict (ball (0 : ℝ^3) r)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let H : ℝ^3 → ℝ := fun x ↦ |f x| / ‖x‖
  let G : ℝ^3 → ℝ := fun x ↦ |f x| ^ 3
  have hH' : MemLp H 2 μ := by
    simpa only [H, μ, norm_div, Real.norm_eq_abs, abs_norm] using hH.norm
  have hG : MemLp G 2 μ := by
    simpa only [G, μ, ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs,
      show (6 : ℝ≥0∞) / 3 = 2 by
        change ((6 : NNReal) : ℝ≥0∞) / ((3 : NNReal) : ℝ≥0∞) = ((2 : NNReal) : ℝ≥0∞)
        rw [← ENNReal.coe_div (by norm_num)]
        norm_num] using h6.norm_rpow_div 3
  have h1 : MemLp (fun _ : ℝ^3 ↦ (1 : ℝ)) 2 μ := memLp_const 1
  have hHi : Integrable H μ := hH'.integrable (by norm_num)
  have hHG : Integrable (fun x ↦ H x * G x) μ := hH'.integrable_mul hG
  have hdom : ∀ᵐ x ∂μ, |f x| ^ p / ‖x‖ ≤
      A ^ max (p - 4) 0 * (H x + H x * G x) := by
    filter_upwards [hbound] with x hx
    have h := mul_le_mul_of_nonneg_left
      (rpow_sub_one_le_amplitude_mul_cubic hp hA (abs_nonneg _) hx)
      (div_nonneg (abs_nonneg (f x)) (norm_nonneg x))
    have heq : |f x| ^ p = |f x| * |f x| ^ (p - 1) := by
      have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
      simpa only [show (1 : ℝ) + (p - 1) = p by cas] using (Real.rpow_one_add' (abs_nonneg (f x))
          (y := p - 1) (by simpa only [add_sub_cancel] using hp0))
    rw [heq]
    dsimp only [H, G] at h ⊢
    convert h using 1 <;> ring
  have hint : Integrable (fun x ↦ |f x| ^ p / ‖x‖) μ := by
    apply ((hHi.add hHG).const_mul (A ^ max (p - 4) 0)).mono'
      ((h6.aestronglyMeasurable.norm.aemeasurable.pow_const p).div
        continuous_norm.measurable.aemeasurable).aestronglyMeasurable
    filter_upwards [hdom] with x hx
    simpa only [Pi.div_apply, Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (norm_nonneg _))] using hx
  have hcs1 : (∫ x, H x ∂μ) ≤
      √(∫ x, f x ^ 2 / ‖x‖ ^ 2 ∂μ) * √(volume.real (ball (0 : ℝ^3) r)) := by
    have h := integral_abs_mul_le_sqrt_integral_sq hH' h1
    simpa only [H, mul_one, abs_div, abs_abs, abs_norm, div_pow, sq_abs,
      one_pow, integral_const, smul_eq_mul, mul_one, μ, Measure.real,
      Measure.restrict_apply_univ] using h
  have hcsG : (∫ x, H x * G x ∂μ) ≤
      √(∫ x, f x ^ 2 / ‖x‖ ^ 2 ∂μ) * √(∫ x, |f x| ^ 6 ∂μ) := by
    have h := integral_abs_mul_le_sqrt_integral_sq hH' hG
    simpa only [H, G, abs_mul, abs_div, abs_abs, abs_norm, abs_pow,
      div_pow, sq_abs, ← pow_mul] using h
  refine ⟨hint, ?_⟩
  calc
    _ ≤ ∫ x, A ^ max (p - 4) 0 * (H x + H x * G x) ∂μ :=
      integral_mono_ae hint ((hHi.add hHG).const_mul _) hdom
    _ = A ^ max (p - 4) 0 * ((∫ x, H x ∂μ) + ∫ x, H x * G x ∂μ) := by
      rw [integral_const_mul, integral_add hHi hHG]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (add_le_add hcs1 hcsG)
        (Real.rpow_nonneg (zero_le_one.trans hA) (max (p - 4) 0))
      convert h using 1
      ring

/-- Hardy supplies the singular factor for arbitrary H¹ data. Only the L⁶
membership and amplitude bound remain as inputs to this estimate. -/
theorem h1_power_potential_bound {r p A : ℝ} (hr : 0 < r) (hp : 1 ≤ p) (hA : 1 ≤ A)
    (U : H¹(ball (0 : ℝ^3) r)) (h6 : MemLp (baseRepresentative U) 6 (domainMeasure 3 (ball 0 r)))
    (hbound : ∀ᵐ x ∂domainMeasure 3 (ball 0 r), |baseRepresentative U x| ≤ A) :
    IntegrableOn (fun x ↦ |baseRepresentative U x| ^ p / ‖x‖) (ball (0 : ℝ^3) r) ∧
      (∫ x in ball (0 : ℝ^3) r, |baseRepresentative U x| ^ p / ‖x‖) ≤
        A ^ max (p - 4) 0 *
          √(4 * ‖∇ U‖ ^ 2 + 6 / r ^ 2 * ‖wkpBaseCoordinateCLM U‖ ^ 2) *
          (√(volume.real (ball (0 : ℝ^3) r)) +
            √(∫ x in ball (0 : ℝ^3) r, |baseRepresentative U x| ^ 6)) := by
  obtain ⟨hi, hb⟩ := integrable_power_potential_and_bound hp hA
    (Hardy.memLp_div_norm_h1_ball (by decide) hr U) h6 hbound
  refine ⟨hi, hb.trans ?_⟩
  have hH := (Hardy.integrable_hardy_ball_and_bound (by decide) hr U).2
  norm_num only [Nat.cast_ofNat, mul_one, show (2 : ℝ) * 3 = 6 by norm_num] at hH
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH)
      (Real.rpow_nonneg (zero_le_one.trans hA) _)) (by positivity)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
