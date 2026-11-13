/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Translation estimates for derivative p-energy

For a compactly supported C¹ function into a real Banach space, defined on a
finite-dimensional real normed space, translation by `h` has p-energy at most
`‖h‖ ^ p` times the derivative p-energy.
The derivative is measured in operator norm. The measure can be any additive Haar
measure, with no normalization factor. Real exponents `p ≥ 1` include the endpoint one.

The proof uses the Bochner fundamental theorem of calculus along each unit-parameter
segment, bounds the integral by the integral of the norm, and applies scalar Jensen.
Fubini and translation invariance then integrate the resulting bound.
-/

@[expose] public section

open MeasureTheory Set

namespace SobolevSpace
namespace Translation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The fundamental theorem of calculus on the segment from `x` to `x + h`. -/
theorem sub_eq_intervalIntegral_fderiv {f : E → F} (hf : ContDiff ℝ 1 f) (x h : E) :
    f (x + h) - f x = ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • h) h := by
  have hpath (t : ℝ) : HasDerivAt (fun t : ℝ ↦ x + t • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hcomp (t : ℝ) :
      HasDerivAt (fun t : ℝ ↦ f (x + t • h)) (fderiv ℝ f (x + t • h) h) t :=
    (hf.differentiable (by simp) (x + t • h)).hasFDerivAt.comp_hasDerivAt t (hpath t)
  have hc : Continuous fun t : ℝ ↦ fderiv ℝ f (x + t • h) h :=
    ((hf.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  simpa using (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hcomp t) (hc.intervalIntegrable 0 1)).symm

omit [CompleteSpace F] in
/-- Jensen's inequality on a Lebesgue interval of length one. -/
theorem norm_intervalIntegral_rpow_le {g : ℝ → F} (hg : Continuous g)
    {p : ℝ} (hp : 1 ≤ p) :
    ‖∫ t in (0 : ℝ)..1, g t‖ ^ p ≤ ∫ t in (0 : ℝ)..1, ‖g t‖ ^ p := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hc : Continuous fun t ↦ ‖g t‖ ^ p := hg.norm.rpow_const (fun _ ↦ Or.inr hp0)
  have hj := (convexOn_rpow hp).map_set_average_le
    (μ := (volume : Measure ℝ)) (t := Ioc (0 : ℝ) 1) (f := fun t ↦ ‖g t‖)
    (continuousOn_id.rpow_const (fun _ _ ↦ Or.inr hp0)) isClosed_Ici
    (by simp) (by simp) (Filter.Eventually.of_forall fun t ↦ norm_nonneg (g t))
    (hg.norm.intervalIntegrable 0 1).1 (hc.intervalIntegrable 0 1).1
  rw [setAverage_eq, setAverage_eq,
    Real.volume_real_Ioc_of_le zero_le_one] at hj
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := g) zero_le_one
  calc
    ‖∫ t in (0 : ℝ)..1, g t‖ ^ p ≤ (∫ t in (0 : ℝ)..1, ‖g t‖) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) hn hp0
    _ ≤ ∫ t in (0 : ℝ)..1, ‖g t‖ ^ p := by
      simpa [intervalIntegral.integral_of_le zero_le_one, Function.comp_def] using hj

/-- The p-th power of an increment is controlled by the derivative energy along its segment. -/
theorem norm_sub_rpow_le_intervalIntegral_fderiv {f : E → F} (hf : ContDiff ℝ 1 f)
    {p : ℝ} (hp : 1 ≤ p) (x h : E) :
    ‖f (x + h) - f x‖ ^ p ≤
      ‖h‖ ^ p * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ f (x + t • h)‖ ^ p := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hc : Continuous fun t : ℝ ↦ fderiv ℝ f (x + t • h) :=
    (hf.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hdir : Continuous fun t : ℝ ↦ ‖fderiv ℝ f (x + t • h) h‖ ^ p :=
    (hc.clm_apply continuous_const).norm.rpow_const (fun _ ↦ Or.inr hp0)
  have hen : Continuous fun t : ℝ ↦ ‖fderiv ℝ f (x + t • h)‖ ^ p :=
    hc.norm.rpow_const (fun _ ↦ Or.inr hp0)
  calc
    ‖f (x + h) - f x‖ ^ p ≤
        ∫ t in (0 : ℝ)..1, ‖fderiv ℝ f (x + t • h) h‖ ^ p := by
      rw [sub_eq_intervalIntegral_fderiv hf x h]
      exact norm_intervalIntegral_rpow_le (hc.clm_apply continuous_const) hp
    _ ≤ ∫ t in (0 : ℝ)..1, ‖h‖ ^ p * ‖fderiv ℝ f (x + t • h)‖ ^ p := by
      apply intervalIntegral.integral_mono_on zero_le_one
        (hdir.intervalIntegrable 0 1) ((hen.const_mul _).intervalIntegrable 0 1)
      intro t _
      calc
        ‖fderiv ℝ f (x + t • h) h‖ ^ p ≤ (‖fderiv ℝ f (x + t • h)‖ * ‖h‖) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) ((fderiv ℝ f (x + t • h)).le_opNorm h) hp0
        _ = ‖h‖ ^ p * ‖fderiv ℝ f (x + t • h)‖ ^ p := by
          rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_comm]
    _ = ‖h‖ ^ p * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ f (x + t • h)‖ ^ p :=
      intervalIntegral.integral_const_mul _ _

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Positive powers of the derivative norm of a compactly supported C¹ function are integrable. -/
theorem integrable_norm_fderiv_rpow {f : E → F} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x ↦ ‖fderiv ℝ f x‖ ^ p) μ := by
  have hc : Continuous fun x ↦ ‖fderiv ℝ f x‖ ^ p :=
    (hf.continuous_fderiv (by simp)).norm.rpow_const (fun _ ↦ Or.inr hp.le)
  exact hc.integrable_of_hasCompactSupport ((hfc.fderiv (𝕜 := ℝ)).norm.rpow_const hp.ne')

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Positive powers of a translated increment of a compactly supported continuous function
are integrable. -/
theorem integrable_norm_sub_rpow {f : E → F} (hf : Continuous f)
    (hfc : HasCompactSupport f) {p : ℝ} (hp : 0 < p) (h : E) :
    Integrable (fun x ↦ ‖f (x + h) - f x‖ ^ p) μ := by
  have hc : Continuous fun x ↦ ‖f (x + h) - f x‖ ^ p :=
    ((hf.comp (continuous_id.add continuous_const)).sub hf).norm.rpow_const
      (fun _ ↦ Or.inr hp.le)
  exact hc.integrable_of_hasCompactSupport
    (((hfc.comp_homeomorph (Homeomorph.addRight h)).sub hfc).norm.rpow_const hp.ne')

omit [NormedSpace ℝ F] [CompleteSpace F] in
/-- An integrable continuous function remains jointly integrable when translated along
a segment with parameter in the unit interval. -/
theorem integrable_add_smul {g : E → F} (hg : Continuous g) (hgi : Integrable g μ) (h : E) :
    Integrable (fun z : ℝ × E ↦ g (z.2 + z.1 • h))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod μ) := by
  have hc : Continuous fun z : ℝ × E ↦ g (z.2 + z.1 • h) :=
    hg.comp (continuous_snd.add (continuous_fst.smul continuous_const))
  refine (integrable_prod_iff hc.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun t ↦ hgi.comp_add_right (t • h)
  · simp_rw [integral_add_right_eq_self (fun x ↦ ‖g x‖)]
    exact integrableOn_const (by simp)

/-- Averaging translates over the unit interval preserves the total integral. -/
theorem integral_intervalIntegral_add_smul {g : E → F} (hg : Continuous g)
    (hgi : Integrable g μ) (h : E) :
    (∫ x, (∫ t in (0 : ℝ)..1, g (x + t • h)) ∂μ) = ∫ x, g x ∂μ := by
  rw [← intervalIntegral_integral_swap (integrable_add_smul μ hg hgi h)]
  simp_rw [integral_add_right_eq_self g]
  simp

/-- The p-energy of translation is bounded by the p-energy of the Fréchet derivative,
with constant `‖h‖ ^ p`. The derivative norm is the operator norm. -/
theorem integral_norm_sub_rpow_le {f : E → F} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {p : ℝ} (hp : 1 ≤ p) (h : E) :
    (∫ x, ‖f (x + h) - f x‖ ^ p ∂μ) ≤
      ‖h‖ ^ p * ∫ x, ‖fderiv ℝ f x‖ ^ p ∂μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hc : Continuous fun x ↦ ‖fderiv ℝ f x‖ ^ p :=
    (hf.continuous_fderiv (by simp)).norm.rpow_const (fun _ ↦ Or.inr hp0.le)
  have hi := integrable_norm_fderiv_rpow μ hf hfc hp0
  have hs := (integrable_add_smul μ hc hi h).swap.integral_prod_left
  have hmean : Integrable (fun x ↦ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ f (x + t • h)‖ ^ p) μ := by
    simpa [intervalIntegral.integral_of_le zero_le_one, uIoc_of_le zero_le_one] using hs
  calc
    (∫ x, ‖f (x + h) - f x‖ ^ p ∂μ) ≤
        ∫ x, ‖h‖ ^ p * (∫ t in (0 : ℝ)..1, ‖fderiv ℝ f (x + t • h)‖ ^ p) ∂μ :=
      integral_mono (integrable_norm_sub_rpow μ hf.continuous hfc hp0 h)
        (hmean.const_mul _) (fun x ↦ norm_sub_rpow_le_intervalIntegral_fderiv hf hp x h)
    _ = ‖h‖ ^ p * ∫ x, ‖fderiv ℝ f x‖ ^ p ∂μ := by
      rw [integral_const_mul, integral_intervalIntegral_add_smul μ hc hi h]

/-- The translation estimate for nonnegative integrals, for subsequent Tonelli arguments. -/
theorem lintegral_norm_sub_rpow_le {f : E → F} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) {p : ℝ} (hp : 1 ≤ p) (h : E) :
    (∫⁻ x, ENNReal.ofReal (‖f (x + h) - f x‖ ^ p) ∂μ) ≤
      ENNReal.ofReal (‖h‖ ^ p) * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ p) ∂μ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_norm_sub_rpow μ hf.continuous hfc hp0 h)
    (Filter.Eventually.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_norm_fderiv_rpow μ hf hfc hp0)
    (Filter.Eventually.of_forall fun x ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg h) p)]
  exact ENNReal.ofReal_le_ofReal (integral_norm_sub_rpow_le μ hf hfc hp h)

end Translation
end SobolevSpace
