/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Localization.Pointwise
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The nonlocal tail across an artificial chart edge

A positive gap between the active support and the new part of the domain
removes the singularity in the cross term of zero extension. The remaining
tail is dominated by an integrable shifted radial power. This does not
justify zero extension across a physical boundary without a support gap.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.Fractional.Localization

variable {n : ℕ} {s δ : ℝ} {p : ℝ≥0∞}

/-- The integrable radial tail used beyond an artificial chart edge. -/
def edgeKernel (n : ℕ) (s : ℝ) (h : ℝ^n) (p : ℝ≥0∞ := 2) : ℝ :=
  (1 + ‖h‖) ^ (-((n : ℝ) + p.toReal * s))

/-- The shifted radial power is nonnegative at every point. -/
theorem edgeKernel_nonneg (h : ℝ^n) (p : ℝ≥0∞ := 2) :
    0 ≤ edgeKernel n s h (p := p) :=
  Real.rpow_nonneg (by positivity) _

/-- The tail kernel is measurable, so it can be integrated over any measurable region. -/
theorem measurable_edgeKernel (p : ℝ≥0∞ := 2) :
    Measurable (edgeKernel n s (p := p)) := by
  unfold edgeKernel
  fun_prop

/-- Positive order gives decay strictly faster than the dimension, making the tail integrable. -/
theorem integrable_edgeKernel (hs : 0 < s) (p : ℝ≥0∞ := 2)
    (hp : 0 < p.toReal := by norm_num) :
    Integrable (edgeKernel n s (p := p)) volume :=
  integrable_one_add_norm (by
    rw [finrank_euclideanSpace_fin]
    linarith [mul_pos hp hs])

/-- The radial kernel is unchanged when we reverse a displacement. -/
theorem edgeKernel_neg (h : ℝ^n) (p : ℝ≥0∞ := 2) :
    edgeKernel n s (-h) (p := p) = edgeKernel n s h (p := p) := by
  simp only [edgeKernel, norm_neg]

/-- The exact finite radial mass appearing in the artificial-edge estimate. -/
def edgeMass (n : ℕ) (s : ℝ) (p : ℝ≥0∞ := 2) : ℝ≥0∞ :=
  ∫⁻ h : ℝ^n, ENNReal.ofReal (edgeKernel n s h (p := p))

/-- The mass in the support-gap bound is finite for positive order and finite positive exponent. -/
theorem edgeMass_lt_top (hs : 0 < s) (p : ℝ≥0∞ := 2)
    (hp : 0 < p.toReal := by norm_num) : edgeMass n s (p := p) < ∞ :=
  (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (edgeKernel_nonneg (p := p)))).mp
      (integrable_edgeKernel hs p hp).hasFiniteIntegral

/-- Outside a positive support gap, the fractional kernel has no singularity.
The explicit price of the gap is `(1 + δ⁻¹)^(n+ps)`. -/
theorem inv_rpow_le_edgeKernel
    (hs : 0 ≤ (n : ℝ) + p.toReal * s) (hδ : 0 < δ) {h : ℝ^n} (hh : δ ≤ ‖h‖) :
    (‖h‖ ^ ((n : ℝ) + p.toReal * s))⁻¹ ≤
      (1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s) * edgeKernel n s h (p := p) := by
  have hr : 0 < ‖h‖ := hδ.trans_le hh
  have hgap : 1 ≤ δ⁻¹ * ‖h‖ := (le_inv_mul_iff₀ hδ).mpr (by simpa using hh)
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + ‖h‖)
    (by nlinarith : 1 + ‖h‖ ≤ (1 + δ⁻¹) * ‖h‖) hs
  rw [Real.mul_rpow (by positivity) (norm_nonneg h)] at hpow
  rw [edgeKernel, Real.rpow_neg (by positivity), ← div_eq_mul_inv, ← one_div]
  apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hr _)
    (by positivity : 0 < (1 + ‖h‖) ^ ((n : ℝ) + p.toReal * s))).mpr
  simpa only [one_mul] using hpow

/-- The support-gap bound in the nonnegative extended reals, suitable for
Tonelli integration against an arbitrary numerator. -/
theorem div_rpow_le_edgeKernel
    (hs : 0 ≤ (n : ℝ) + p.toReal * s) (hδ : 0 < δ) {x y : ℝ^n}
    (hxy : δ ≤ dist x y) (a : ℝ≥0∞) :
    a / (ENNReal.ofReal ‖x - y‖) ^ ((n : ℝ) + p.toReal * s) ≤
      ENNReal.ofReal ((1 + δ⁻¹) ^ ((n : ℝ) + p.toReal * s)) *
        (a * ENNReal.ofReal (edgeKernel n s (x - y) (p := p))) := by
  have hr : 0 < ‖x - y‖ := hδ.trans_le (by simpa only [dist_eq_norm] using hxy)
  have hb := ENNReal.ofReal_le_ofReal
    (inv_rpow_le_edgeKernel hs hδ (by simpa only [dist_eq_norm] using hxy))
  rw [ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hr _),
    ← ENNReal.ofReal_rpow_of_pos hr,
    ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)] at hb
  simpa only [div_eq_mul_inv, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hb (show 0 ≤ a from zero_le)

/-- The cross term of zero extension is bounded by the support-gap tail. -/
theorem norm_div_rpow_sq_le_edgeKernel
    (hs : 0 ≤ (n : ℝ) + 2 * s) (hδ : 0 < δ) {x y : ℝ^n}
    (hxy : δ ≤ dist x y) (a : ℝ) :
    ‖a / ‖x - y‖ ^ ((n : ℝ) / 2 + s)‖ ^ 2 ≤
      (1 + δ⁻¹) ^ ((n : ℝ) + 2 * s) * (‖a‖ ^ 2 * edgeKernel n s (x - y)) := by
  have hpow : (‖x - y‖ ^ ((n : ℝ) / 2 + s)) ^ 2 =
      ‖x - y‖ ^ ((n : ℝ) + 2 * s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    ring
  have hb := mul_le_mul_of_nonneg_left
    (inv_rpow_le_edgeKernel (p := 2) hs hδ (by simpa only [dist_eq_norm] using hxy)) (sq_nonneg ‖a‖)
  rw [norm_div, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    div_pow, hpow, div_eq_mul_inv]
  simpa only [ENNReal.toReal_ofNat, mul_left_comm] using hb

end SobolevSpace.Fractional.Localization
