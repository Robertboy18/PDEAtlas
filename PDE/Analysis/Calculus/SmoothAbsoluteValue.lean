/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import CAS.ExactTactic

/-!
# Smooth approximation of absolute value

For positive `ε`, the function `x ↦ sqrt (x ^ 2 + ε ^ 2) - ε` is a smooth,
one-Lipschitz approximation of `|x|` that fixes zero, lies below `|x|`, and
differs from it by at most `ε`.  Its derivative `x / sqrt (x ^ 2 + ε ^ 2)` has
absolute value at most one and converges pointwise to `sign x` as `ε → 0`.
This is the classical regularization used to prove that `u ↦ |u|`, `u⁺` and
`u⁻` act on `W^{1,p}` with the expected almost-everywhere chain rule: one
composes with the smooth approximation, applies the smooth chain rule, and
passes to the limit by dominated convergence.  In the hint to Problem 18 of
Evans, §5.10, `u⁺` is the limit of `F_ε(u)`, where `F_ε` agrees with this
approximation on `[0, ∞)` and vanishes on `(-∞, 0)`.  We also define a
shifted variant, `smoothLevelProbe`, which vanishes at `0` and at a target
level `c` and has nonzero slope at `c ≠ 0`.

## Main results

* `smoothAbs`, `smoothAbsSlope`: the approximation and its derivative, with
  `hasDerivAt_smoothAbs`, `contDiff_smoothAbs` and
  `lipschitzWith_smoothAbs`.
* `abs_smoothAbsSlope_le_one`, `smoothAbs_le_abs`,
  `abs_smoothAbs_sub_abs_le`: the slope bound and the uniform error bound.
* `tendsto_smoothAbs_of_tendsto_zero`,
  `tendsto_smoothAbsSlope_of_tendsto_zero`: pointwise convergence to `|x|`
  and to `sign x` as the scale tends to zero.
* `smoothLevelProbe`, `smoothLevelProbeSlope` and their properties.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.10, Problems 17 and 18, p. 308.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 7 (Sobolev Spaces), pp. 144-176.
  <https://doi.org/10.1007/978-3-642-61798-0_7>
-/

@[expose] public section

noncomputable section

open Filter
open scoped NNReal Topology

namespace PDE.Analysis.Calculus

/-- Smooth approximation of absolute value with scale `ε`. -/
abbrev smoothAbs (ε x : ℝ) : ℝ :=
  √(x ^ 2 + ε ^ 2) - ε

/-- Derivative multiplier of `smoothAbs`. -/
def smoothAbsSlope (ε x : ℝ) : ℝ :=
  x / √(x ^ 2 + ε ^ 2)

/-- The smooth approximation fixes zero for nonnegative scales. -/
theorem smoothAbs_zero (ε : ℝ) (hε : 0 ≤ ε) :
    smoothAbs ε 0 = 0 := by
  simp [smoothAbs, Real.sqrt_sq_eq_abs, abs_of_nonneg hε]

/-- The expression under the square root is positive at positive scale. -/
theorem smoothAbs_sq_add_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 < x ^ 2 + ε ^ 2 := by
  positivity

/-- Derivative formula for the smooth approximation. -/
theorem hasDerivAt_smoothAbs {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (smoothAbs ε) (smoothAbsSlope ε x) x := by
  cas

/-- The smooth approximation is differentiable at positive scale. -/
theorem differentiable_smoothAbs {ε : ℝ} (hε : 0 < ε) :
    Differentiable ℝ (smoothAbs ε) :=
  fun x ↦ (hasDerivAt_smoothAbs hε x).differentiableAt

/-- The smooth approximation is infinitely differentiable at positive scale. -/
theorem contDiff_smoothAbs {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothAbs ε) := by
  have hinner :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ x ^ 2 + ε ^ 2) :=
    (contDiff_id.pow 2).add contDiff_const
  exact
    (hinner.sqrt fun x ↦ ne_of_gt (smoothAbs_sq_add_pos hε x)).sub
      contDiff_const

/-- Formula for the derivative of the smooth approximation. -/
theorem deriv_smoothAbs {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    deriv (smoothAbs ε) x = smoothAbsSlope ε x :=
  (hasDerivAt_smoothAbs hε x).deriv

/-- The derivative multiplier is continuous at positive scale. -/
theorem continuous_smoothAbsSlope {ε : ℝ} (hε : 0 < ε) :
    Continuous (smoothAbsSlope ε) := by
  unfold smoothAbsSlope
  apply continuous_id.div
    (Real.continuous_sqrt.comp
      ((continuous_id.pow 2).add (continuous_const.pow 2)))
  intro x
  exact ne_of_gt (Real.sqrt_pos.2 (smoothAbs_sq_add_pos hε x))

/-- The derivative multiplier of the smooth approximation has absolute value
at most one. -/
theorem abs_smoothAbsSlope_le_one {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    |smoothAbsSlope ε x| ≤ 1 := by
  rw [smoothAbsSlope, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_one
    (Real.sqrt_pos.2 (smoothAbs_sq_add_pos hε x))).2
  calc
    |x| = √(x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
    _ ≤ √(x ^ 2 + ε ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])

/-- The smooth approximation is one-Lipschitz at positive scale. -/
theorem lipschitzWith_smoothAbs {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (smoothAbs ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (differentiable_smoothAbs hε)
  intro x
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
    Real.norm_eq_abs, deriv_smoothAbs hε]
  exact abs_smoothAbsSlope_le_one hε x

/-- The smooth approximation is nonnegative at nonnegative scale. -/
theorem smoothAbs_nonneg {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    0 ≤ smoothAbs ε x := by
  rw [smoothAbs, sub_nonneg]
  calc
    ε = √(ε ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hε]
    _ ≤ √(x ^ 2 + ε ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])

/-- The smooth approximation lies below absolute value. -/
theorem smoothAbs_le_abs {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    smoothAbs ε x ≤ |x| := by
  rw [smoothAbs, sub_le_iff_le_add]
  have hsqrt_sq :
      √(x ^ 2 + ε ^ 2) ^ 2 =
        x ^ 2 + ε ^ 2 :=
    Real.sq_sqrt (by positivity)
  have habs_sq : |x| ^ 2 = x ^ 2 := sq_abs x
  have hrhs : 0 ≤ |x| + ε :=
    add_nonneg (abs_nonneg x) hε
  nlinarith [mul_nonneg (abs_nonneg x) hε]

/-- The uniform approximation error is at most the scale. -/
theorem abs_smoothAbs_sub_abs_le {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    abs (smoothAbs ε x - |x|) ≤ ε := by
  rw [abs_of_nonpos
      (sub_nonpos.2 (smoothAbs_le_abs hε x)),
    neg_sub]
  have hlower :
      |x| ≤ √(x ^ 2 + ε ^ 2) := by
    calc
      |x| = √(x ^ 2) :=
        (Real.sqrt_sq_eq_abs x).symm
      _ ≤ √(x ^ 2 + ε ^ 2) :=
        Real.sqrt_le_sqrt
          (by nlinarith [sq_nonneg ε])
  unfold smoothAbs
  linarith

/-- Smooth absolute values converge pointwise to absolute value when their
nonnegative scales tend to zero. -/
theorem tendsto_smoothAbs_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hεnonneg : ∀ᶠ k in l, 0 ≤ ε k)
    (hε : Tendsto ε l (𝓝 0)) (x : ℝ) :
    Tendsto (fun k ↦ smoothAbs (ε k) x) l (𝓝 |x|) := by
  rw [tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun k ↦ dist_nonneg)
    (hεnonneg.mono fun k hk ↦ ?_) hε
  simpa only [Real.dist_eq] using abs_smoothAbs_sub_abs_le hk x

/-- The derivative multipliers of smooth absolute values converge pointwise
to the sign function when their scales tend to zero. -/
theorem tendsto_smoothAbsSlope_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝 0)) (x : ℝ) :
    Tendsto (fun k ↦ smoothAbsSlope (ε k) x) l
      (𝓝 (SignType.sign x : ℝ)) := by
  by_cases hx : x = 0
  · subst x
    simpa [smoothAbsSlope] using
      (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ)) l (𝓝 0))
  have hden :
      Tendsto (fun k ↦ √(x ^ 2 + (ε k) ^ 2)) l (𝓝 |x|) := by
    have hsq :
        Tendsto (fun k ↦ x ^ 2 + (ε k) ^ 2) l (𝓝 (x ^ 2)) := by
      simpa using tendsto_const_nhds.add (hε.pow 2)
    simpa only [Real.sqrt_sq_eq_abs] using hsq.sqrt
  have hquot :
      Tendsto (fun k ↦ x / √(x ^ 2 + (ε k) ^ 2)) l
        (𝓝 (x / |x|)) :=
    tendsto_const_nhds.div hden (abs_ne_zero.mpr hx)
  have hsign : x / |x| = (SignType.sign x : ℝ) := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · rw [sign_eq_neg_one_iff.mpr hneg, abs_of_neg hneg]
      field_simp
      norm_num
    · rw [sign_eq_one_iff.mpr hpos, abs_of_pos hpos]
      field_simp
      norm_num
  simpa only [smoothAbsSlope, hsign] using hquot

/-- A smooth one-Lipschitz probe that vanishes at both zero and `c`.

Its nonzero slope at `c ≠ 0` makes it useful for transferring a level-set
statement at zero to an arbitrary level without subtracting a nonintegrable
constant from a global `Lᵖ` function. -/
abbrev smoothLevelProbe (c x : ℝ) : ℝ :=
  smoothAbs 1 (x - c / 2) - smoothAbs 1 (-c / 2)

/-- Derivative multiplier of `smoothLevelProbe`. -/
abbrev smoothLevelProbeSlope (c x : ℝ) : ℝ :=
  smoothAbsSlope 1 (x - c / 2)

/-- The smooth level probe is infinitely differentiable. -/
theorem contDiff_smoothLevelProbe (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothLevelProbe c) := by
  exact
    ((contDiff_smoothAbs (by norm_num)).comp
      (contDiff_id.sub contDiff_const)).sub contDiff_const

/-- The derivative multiplier of the smooth level probe is continuous. -/
theorem continuous_smoothLevelProbeSlope (c : ℝ) :
    Continuous (smoothLevelProbeSlope c) := by
  exact
    (continuous_smoothAbsSlope
      (by norm_num)).comp (continuous_id.sub continuous_const)

/-- Derivative formula for the smooth level probe. -/
theorem hasDerivAt_smoothLevelProbe (c x : ℝ) :
    HasDerivAt (smoothLevelProbe c) (smoothLevelProbeSlope c x) x := by
  cas

/-- The smooth level probe fixes zero. -/
theorem smoothLevelProbe_zero (c : ℝ) :
    smoothLevelProbe c 0 = 0 := by
  simp only [smoothLevelProbe, smoothAbs]
  ring_nf

/-- The smooth level probe vanishes at its target level. -/
theorem smoothLevelProbe_level (c : ℝ) :
    smoothLevelProbe c c = 0 := by
  unfold smoothLevelProbe smoothAbs
  cas

/-- The slope of the smooth level probe has absolute value at most one. -/
theorem abs_smoothLevelProbeSlope_le_one (c x : ℝ) :
    |smoothLevelProbeSlope c x| ≤ 1 :=
  abs_smoothAbsSlope_le_one (by norm_num) (x - c / 2)

/-- The smooth level probe is one-Lipschitz. -/
theorem lipschitzWith_smoothLevelProbe (c : ℝ) :
    LipschitzWith 1 (smoothLevelProbe c) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have h :=
    (lipschitzWith_smoothAbs (by norm_num : (0 : ℝ) < 1)).dist_le_mul
      (x - c / 2) (y - c / 2)
  simpa only [smoothLevelProbe, dist_sub_right, one_mul] using h

/-- At a nonzero target level, the smooth level probe has nonzero slope. -/
theorem smoothLevelProbeSlope_level_ne_zero
    {c : ℝ} (hc : c ≠ 0) :
    smoothLevelProbeSlope c c ≠ 0 := by
  have hhalf : c - c / 2 = c / 2 := by ring
  rw [smoothLevelProbeSlope, hhalf, smoothAbsSlope]
  apply div_ne_zero
  · exact div_ne_zero hc (by norm_num)
  · exact ne_of_gt (Real.sqrt_pos.2
      (smoothAbs_sq_add_pos (by norm_num) (c / 2)))

end PDE.Analysis.Calculus
