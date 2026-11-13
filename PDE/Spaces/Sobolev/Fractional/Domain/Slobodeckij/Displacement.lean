/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Fractional energy in displacement coordinates

The change of variables `y = x - h` writes the fractional pair energy as an
integral over displacement and base point. All integrals are nonnegative extended
integrals, so the identity does not require a prior finiteness bound. Almost-everywhere
strong measurability suffices, including for nonseparable normed codomains.

For the half-space trace order `1 - 1 / p`, take the distance exponent
`q = n + p - 1`. The statements also allow other real distance exponents.
The real and extended-power integrands agree on the diagonal when `p > 0`;
in particular no positive-dimensional assumption is needed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.Fractional

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]

/-- The extended-norm quotient agrees with the totalized real quotient.
For a positive difference exponent both sides vanish on the diagonal. -/
theorem enorm_sub_rpow_div_eq_ofReal (g : ℝ^n → F) (x y : ℝ^n)
    {p : ℝ} (hp : 0 < p) (q : ℝ) :
    ‖g x - g y‖ₑ ^ p / (ENNReal.ofReal ‖x - y‖) ^ q =
      ENNReal.ofReal (‖g x - g y‖ ^ p / ‖x - y‖ ^ q) := by
  by_cases hxy : x = y
  · subst y
    simp [ENNReal.zero_rpow_of_pos hp, Real.zero_rpow hp.ne']
  · rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
      ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)),
      ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos
        (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) q)]

/-- Pair energy equals displacement energy, with the displacement integrated first.
The subtraction change of variables preserves volume in every dimension. -/
theorem lintegral_enorm_sub_div_eq_displacement {g : ℝ^n → F}
    (hg : AEStronglyMeasurable g volume) (p q : ℝ) :
    (∫⁻ z : ℝ^n × ℝ^n,
      ‖g z.1 - g z.2‖ₑ ^ p / (ENNReal.ofReal ‖z.1 - z.2‖) ^ q
      ∂((volume : Measure (ℝ^n)).prod volume)) =
      ∫⁻ h : ℝ^n, ∫⁻ x : ℝ^n,
        ‖g (x - h) - g x‖ₑ ^ p / (ENNReal.ofReal ‖h‖) ^ q := by
  have hpair := (hg.comp_fst.sub hg.comp_snd).enorm
  rw [lintegral_prod _ (by fun_prop)]
  calc
    _ = ∫⁻ x : ℝ^n, ∫⁻ h : ℝ^n,
        ‖g (x - h) - g x‖ₑ ^ p / (ENNReal.ofReal ‖h‖) ^ q := by
      apply lintegral_congr
      intro x
      have h := lintegral_sub_left_eq_self (μ := volume)
        (fun y : ℝ^n ↦
          ‖g x - g y‖ₑ ^ p / (ENNReal.ofReal ‖x - y‖) ^ q) x
      simpa only [sub_sub_cancel, enorm_sub_rev] using h.symm
    _ = _ := by
      have hshift := hg.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub volume volume)
      have hnorm := (hshift.sub hg.comp_fst).enorm
      exact lintegral_lintegral_swap (by fun_prop)

/-- The totalized real-power pair energy has the same displacement formula.
Positivity of `p` ensures agreement with the extended-norm formula on the diagonal. -/
theorem lintegral_ofReal_norm_sub_div_eq_displacement {g : ℝ^n → F}
    (hg : AEStronglyMeasurable g volume) {p : ℝ} (hp : 0 < p) (q : ℝ) :
    (∫⁻ z : ℝ^n × ℝ^n,
      ENNReal.ofReal (‖g z.1 - g z.2‖ ^ p / ‖z.1 - z.2‖ ^ q)
      ∂((volume : Measure (ℝ^n)).prod volume)) =
      ∫⁻ h : ℝ^n, ∫⁻ x : ℝ^n,
        ENNReal.ofReal (‖g (x - h) - g x‖ ^ p / ‖h‖ ^ q) := by
  simp_rw [← enorm_sub_rpow_div_eq_ofReal g _ _ hp q]
  rw [lintegral_enorm_sub_div_eq_displacement hg]
  apply lintegral_congr
  intro h
  apply lintegral_congr
  intro x
  simpa only [sub_sub_cancel_left, norm_neg] using
    enorm_sub_rpow_div_eq_ofReal g (x - h) x hp q

/-- The pair energy equals the displacement integral with a real-power kernel.
This form applies directly to signed-kernel convolution estimates. Its zero
displacement value is zero for `p > 0`, regardless of the distance exponent. -/
theorem lintegral_enorm_sub_div_eq_weighted_displacement {g : ℝ^n → F}
    (hg : AEStronglyMeasurable g volume) {p : ℝ} (hp : 0 < p) (q : ℝ) :
    (∫⁻ z : ℝ^n × ℝ^n,
      ‖g z.1 - g z.2‖ₑ ^ p / (ENNReal.ofReal ‖z.1 - z.2‖) ^ q
      ∂((volume : Measure (ℝ^n)).prod volume)) =
      ∫⁻ h : ℝ^n, ∫⁻ x : ℝ^n,
        ENNReal.ofReal (‖h‖ ^ (-q)) *
          ENNReal.ofReal (‖g (x - h) - g x‖ ^ p) := by
  simp_rw [enorm_sub_rpow_div_eq_ofReal g _ _ hp q]
  rw [lintegral_ofReal_norm_sub_div_eq_displacement hg hp]
  apply lintegral_congr
  intro h
  apply lintegral_congr
  intro x
  rw [Real.rpow_neg (norm_nonneg h), div_eq_mul_inv,
    ENNReal.ofReal_mul (by positivity), mul_comm]

end SobolevSpace.Fractional
