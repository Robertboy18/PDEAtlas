/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.Multidimensional.KernelIntegrability
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Multidimensional Morrey estimates

For `n < p < ∞` and a `C¹` function `u : ℝ^n → ℝ`, Morrey's inequality bounds the Hölder
quotient of `u` by the `Lᵖ` norm of its gradient:

`|u(y) - u(x)| ≤ C(n, p) ‖Du‖_{Lᵖ(ℝ^n)} |y - x|^{1 - n/p}`.

## Main results

* `enorm_sub_le_eLpNorm_fderiv_mul_rpow_of_ballPotential`: the conditional form, taking the
  same-ball point-to-average estimate and the kernel bound as hypotheses.
* `enorm_sub_le_eLpNorm_fderiv_mul_rpow_of_potentialBound`: the kernel hypothesis discharged.
* `enorm_sub_le_eLpNorm_fderiv_mul_rpow`: the unconditional estimate for every `C¹` function,
  with the explicit constant
  `2 · morreyBallAverageConstant n · morreyCenteredKernelConstant n q · 2^{1-n/p}`.
* `norm_sub_le_eLpNorm_fderiv_toReal_mul_rpow_of_ballPotential`,
  `norm_sub_le_eLpNorm_fderiv_toReal_mul_rpow`: real-valued forms for compactly supported `u`,
  where compact support is what makes `‖Du‖_{Lᵖ}` finite.

## How it works

We combine two ingredients, as in Evans's proof. The potential estimate (`Potential`) compares `u x`
and `u y` with the average of `u` over one ball containing both points, and bounds each difference
by the Riesz potential `∫ |Du(z)| |z-x|^{1-n}`. Hölder's inequality with the conjugate exponent `q`
splits that potential into `‖Du‖_{Lᵖ}` times the `L^q` norm of the kernel `|z - x|^{1-n}` over the
ball, and the polar integral of the kernel (`KernelIntegrability`) is finite exactly when
`(n-1) q < n`, that is `p > n`, and scales like `r^{1 - n/p}` with the radius.

## Implementation notes

The unconditional theorem compares both points with the average on the enlarged ball `B(x, 2R)`;
this is where the factors `2^n` (inside `morreyBallAverageConstant`) and `2^{1-n/p}` in the constant
come from. They do not matter for the embedding theorems. Evans, PDE, §5.6.2, compares both points
with the average over `B(x, r) ∩ B(y, r)`, `r = |x - y|` ((24)-(25), p. 282). The conditional
versions take the same-ball point-to-average estimate as a hypothesis.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorem 4, pp. 280-283: step 1 of the proof is the
  potential estimate (21), and step 3 is the Hölder estimate (24)-(25), pp. 282-283.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace

open MeasureTheory Set
open scoped ENNReal

section MultidimensionalFinite

variable {n : ℕ}

/-- The global `L^p` seminorm of the Fréchet derivative, written in the same integral form as
Hölder's inequality. -/
def morreyGradientSeminorm (u : ℝ^n → ℝ) (p : ℝ) : ℝ≥0∞ :=
  (∫⁻ z, ‖fderiv ℝ u z‖ₑ ^ p) ^ (1 / p)

/-- For `p > 0` the gradient seminorm is the `Lᵖ` norm of `Du` in Mathlib's `eLpNorm`. -/
theorem morreyGradientSeminorm_eq_eLpNorm
    (u : ℝ^n → ℝ) {p : ℝ} (hp : 0 < p) :
    morreyGradientSeminorm u p =
      eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume := by
  rw [morreyGradientSeminorm, eLpNorm_eq_lintegral_rpow_enorm_toReal]
  · rw [ENNReal.toReal_ofReal hp.le]
  · exact ENNReal.ofReal_ne_zero_iff.mpr hp
  · exact ENNReal.ofReal_ne_top
  · exact (measurable_fderiv ℝ u).aestronglyMeasurable

/-- Two reals within `B` of a common value are within `2 B` of each other. -/
private theorem enorm_sub_le_two_mul_of_le {a b c : ℝ} {B : ℝ≥0∞} (ha : ‖a - c‖ₑ ≤ B)
    (hb : ‖b - c‖ₑ ≤ B) : ‖b - a‖ₑ ≤ 2 * B :=
  calc ‖b - a‖ₑ ≤ ‖b - c‖ₑ + ‖a - c‖ₑ := by
        simpa only [edist_eq_enorm_sub] using edist_triangle_right b a c
    _ ≤ 2 * B := (add_le_add hb ha).trans_eq (two_mul B).symm

/-- **Multidimensional finite-exponent Morrey estimate** (Evans, PDE, §5.6.2, Theorem 4).

Let `1 ≤ n < p < ∞` and let `q` be conjugate to `p`.  If the same-ball
point-to-average estimate and the kernel estimate hold with constants `A` and `K`, then every
pair of points satisfies

`|u(y)-u(x)| ≤ 2 A K ‖Du‖_{Lᵖ(ℝ^n)} |y-x|^(1-n/p)`.

The proof compares both points to the average on the same `n`-dimensional ball and applies
Hölder's inequality to the Riesz kernels.  The unconditional enlarged-ball theorem below has
no geometric assumptions and an explicit dimension-dependent factor in its constant. -/
theorem enorm_sub_le_eLpNorm_fderiv_mul_rpow_of_ballPotential
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) {A K : ℝ≥0∞}
    (hpotential : HasBallAveragePotentialBound u A)
    (hkernel : HasMorreyKernelBound (n := n) p q K)
    (x y : ℝ^n) :
    ‖u y - u x‖ₑ ≤
      2 * A * K * eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume *
        ENNReal.ofReal ‖y - x‖ ^ morreyExponent n (ENNReal.ofReal p) := by
  by_cases hxy : x = y
  · subst y
    simp
  have hp0 : 0 < p := lt_trans (Nat.cast_pos.mpr hn) hp
  let R : ℝ := dist x y
  have hR : 0 < R := dist_pos.mpr hxy
  -- every point of `closedBall x R` is close to the average: potential, Hölder, kernel bound
  have hpot {a : ℝ^n} (ha : a ∈ Metric.closedBall x R) :
      ‖u a - (⨍ z in Metric.ball x R, u z ∂volume)‖ₑ ≤
        A * (morreyGradientSeminorm u p *
          (K * ENNReal.ofReal R ^ morreyExponent n (ENNReal.ofReal p))) := by
    refine (hpotential hR ha).trans (mul_le_mul_right ?_ A)
    refine (ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq
      (hu.continuous_fderiv one_ne_zero).enorm.aemeasurable
      (ENNReal.continuous_rpow_const.comp
        (continuous_id.sub continuous_const).enorm).aemeasurable).trans ?_
    gcongr
    · exact ENNReal.rpow_le_rpow (lintegral_mono' Measure.restrict_le_self le_rfl)
        (one_div_nonneg.mpr hp0.le)
    · exact hkernel hR ha
  calc ‖u y - u x‖ₑ
      ≤ 2 * (A * (morreyGradientSeminorm u p *
          (K * ENNReal.ofReal R ^ morreyExponent n (ENNReal.ofReal p)))) :=
        enorm_sub_le_two_mul_of_le (hpot (by simp [R, hR.le])) (hpot (by simp [R, dist_comm]))
    _ = 2 * A * K * morreyGradientSeminorm u p *
          ENNReal.ofReal R ^ morreyExponent n (ENNReal.ofReal p) := by ring
    _ = 2 * A * K * eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume *
          ENNReal.ofReal ‖y - x‖ ^ morreyExponent n (ENNReal.ofReal p) := by
      rw [morreyGradientSeminorm_eq_eLpNorm u hp0]
      simp [R, dist_eq_norm, norm_sub_rev]

/-- Conditional multidimensional Morrey estimate in which the kernel
bound is discharged by polar integration.  Callers supply only the
same-ball point-to-average estimate.  Use
`enorm_sub_le_eLpNorm_fderiv_mul_rpow` for the unconditional result. -/
theorem enorm_sub_le_eLpNorm_fderiv_mul_rpow_of_potentialBound
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) {A : ℝ≥0∞}
    (hpotential : HasBallAveragePotentialBound u A)
    (x y : ℝ^n) :
    ‖u y - u x‖ₑ ≤
      2 * A * morreyKernelConstant n q *
          eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume *
        ENNReal.ofReal ‖y - x‖ ^ morreyExponent n (ENNReal.ofReal p) :=
  enorm_sub_le_eLpNorm_fderiv_mul_rpow_of_ballPotential
    u hu hn hp hpq hpotential
      (hasMorreyKernelBound_of_holderConjugate hn hp hpq) x y

/-- **Multidimensional finite-exponent Morrey estimate** for every `C¹` function
(Evans, PDE, §5.6.2, Theorem 4).

For `1 ≤ n < p < ∞`, every `C¹` real-valued function on `ℝ^n` satisfies

`|u(y)-u(x)| ≤ C(n,p) ‖Du‖ₚ |y-x|^(1-n/p)`.

No geometric potential hypothesis remains.  The proof combines
`enorm_sub_ballAverage_le_morreyPotential`, Hölder's inequality, and the
exact polar integral of the Morrey kernel.  The explicit constant below
includes the enlargement factors `2^n` and `2^(1-n/p)`.

This is the global `C¹(ℝ^n)` estimate.  Extending it to a Hölder representative
of an arbitrary `W^{1,p}` class on a bounded `C¹` domain is outside this
theorem's scope. -/
theorem enorm_sub_le_eLpNorm_fderiv_mul_rpow
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) (x y : ℝ^n) :
    ‖u y - u x‖ₑ ≤
      2 * morreyBallAverageConstant n *
          morreyCenteredKernelConstant n q *
          (ENNReal.ofReal 2 ^
            morreyExponent n (ENNReal.ofReal p)) *
        eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume *
        ENNReal.ofReal ‖y - x‖ ^
          morreyExponent n (ENNReal.ofReal p) := by
  by_cases hxy : x = y
  · subst y
    simp
  have hp0 : 0 < p := lt_trans (Nat.cast_pos.mpr hn) hp
  let R : ℝ := dist x y
  have hR : 0 < R := dist_pos.mpr hxy
  -- every point of `closedBall x R` is close to the average: potential on `B(a, 2R)`, Hölder,
  -- and the exact polar integral of the kernel
  have hpot {a : ℝ^n} (ha : a ∈ Metric.closedBall x R) :
      ‖u a - (⨍ z in Metric.ball x R, u z ∂volume)‖ₑ ≤
        morreyBallAverageConstant n * (morreyGradientSeminorm u p *
          (morreyCenteredKernelConstant n q *
            ENNReal.ofReal (2 * R) ^ morreyExponent n (ENNReal.ofReal p))) := by
    refine (enorm_sub_ballAverage_le_morreyPotential u hu hn hR ha).trans
      (mul_le_mul_right ?_ _)
    refine (ENNReal.lintegral_mul_le_Lp_mul_Lq _ hpq
      (hu.continuous_fderiv one_ne_zero).enorm.aemeasurable
      (ENNReal.continuous_rpow_const.comp
        (continuous_id.sub continuous_const).enorm).aemeasurable).trans ?_
    gcongr
    · exact ENNReal.rpow_le_rpow (lintegral_mono' Measure.restrict_le_self le_rfl)
        (one_div_nonneg.mpr hp0.le)
    · exact (lintegral_morreyKernel_rpow_ball_center_root hn hp hpq
        (mul_pos zero_lt_two hR) a).le
  calc ‖u y - u x‖ₑ
      ≤ 2 * (morreyBallAverageConstant n * (morreyGradientSeminorm u p *
          (morreyCenteredKernelConstant n q *
            ENNReal.ofReal (2 * R) ^ morreyExponent n (ENNReal.ofReal p)))) :=
        enorm_sub_le_two_mul_of_le (hpot (by simp [R, hR.le])) (hpot (by simp [R, dist_comm]))
    _ = 2 * morreyBallAverageConstant n * morreyCenteredKernelConstant n q *
          (ENNReal.ofReal 2 ^ morreyExponent n (ENNReal.ofReal p)) *
        morreyGradientSeminorm u p * ENNReal.ofReal R ^ morreyExponent n (ENNReal.ofReal p) := by
      rw [ENNReal.ofReal_mul zero_le_two,
        ENNReal.mul_rpow_of_nonneg _ _ (morreyExponent_ofReal_pos hn hp).le]
      ring
    _ = 2 * morreyBallAverageConstant n * morreyCenteredKernelConstant n q *
          (ENNReal.ofReal 2 ^ morreyExponent n (ENNReal.ofReal p)) *
        eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume *
        ENNReal.ofReal ‖y - x‖ ^ morreyExponent n (ENNReal.ofReal p) := by
      rw [morreyGradientSeminorm_eq_eLpNorm u hp0]
      simp [R, dist_eq_norm, norm_sub_rev]

/-- Real-valued compact-support form of the multidimensional finite-`p` Morrey estimate
(Evans §5.6.2, Theorem 4).

Compact support is used here to prove, rather than assume, finiteness of the global derivative
seminorm.  The only additional hypotheses are the two geometric estimates isolated above and
finiteness of their constants. -/
theorem norm_sub_le_eLpNorm_fderiv_toReal_mul_rpow_of_ballPotential
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u) (hcompact : HasCompactSupport u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) {A K : ℝ≥0∞}
    (hA : A ≠ ∞) (hK : K ≠ ∞)
    (hpotential : HasBallAveragePotentialBound u A)
    (hkernel : HasMorreyKernelBound (n := n) p q K)
    (x y : ℝ^n) :
    |u y - u x| ≤
      2 * A.toReal * K.toReal *
        (eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume).toReal *
          ‖y - x‖ ^ morreyExponent n (ENNReal.ofReal p) := by
  have hgradientFinite : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume ≠ ∞ :=
    ((hu.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport
      (hcompact.fderiv ℝ)).eLpNorm_ne_top
  have hdistanceFinite :
      ENNReal.ofReal ‖y - x‖ ^ morreyExponent n (ENNReal.ofReal p) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (morreyExponent_ofReal_pos hn hp).le ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono (by finiteness)
    (enorm_sub_le_eLpNorm_fderiv_mul_rpow_of_ballPotential u hu hn hp hpq hpotential hkernel x y)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
  simpa [ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs] using hreal

/-- Finite real-valued form of the unconditional multidimensional Morrey
estimate.  Compact support is used only to establish finiteness of the global
`Lᵖ` norm of `Du`; no point-to-average or kernel hypothesis is supplied by the
caller. -/
theorem norm_sub_le_eLpNorm_fderiv_toReal_mul_rpow
    (u : ℝ^n → ℝ) (hu : ContDiff ℝ 1 u)
    (hcompact : HasCompactSupport u)
    {p q : ℝ} (hn : 0 < n) (hp : (n : ℝ) < p)
    (hpq : p.HolderConjugate q) (x y : ℝ^n) :
    |u y - u x| ≤
      2 * (morreyBallAverageConstant n).toReal *
        (morreyCenteredKernelConstant n q).toReal *
        2 ^ morreyExponent n (ENNReal.ofReal p) *
        (eLpNorm (fderiv ℝ u)
          (ENNReal.ofReal p) volume).toReal *
        ‖y - x‖ ^ morreyExponent n (ENNReal.ofReal p) := by
  have hgamma : 0 ≤ morreyExponent n (ENNReal.ofReal p) := (morreyExponent_ofReal_pos hn hp).le
  have hgradientFinite : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) volume ≠ ∞ :=
    ((hu.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport
      (hcompact.fderiv ℝ)).eLpNorm_ne_top
  have haverageFinite : morreyBallAverageConstant n ≠ ∞ := by
    simp [morreyBallAverageConstant]
  have hkernelFinite : morreyCenteredKernelConstant n q ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hpq.symm.pos.le) ENNReal.ofReal_ne_top
  have htwoFinite : ENNReal.ofReal 2 ^ morreyExponent n (ENNReal.ofReal p) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hgamma ENNReal.ofReal_ne_top
  have hdistanceFinite : ENNReal.ofReal ‖y - x‖ ^ morreyExponent n (ENNReal.ofReal p) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hgamma ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono (by finiteness)
    (enorm_sub_le_eLpNorm_fderiv_mul_rpow u hu hn hp hpq x y)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ← ENNReal.toReal_rpow] at hreal
  simpa [ENNReal.toReal_ofReal (norm_nonneg _),
    Real.norm_eq_abs] using hreal

end MultidimensionalFinite

end SobolevSpace
