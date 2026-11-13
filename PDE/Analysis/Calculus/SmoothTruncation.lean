/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SmoothAbsoluteValue
public import PDE.Analysis.Calculus.Truncation
import CAS.ExactTactic

/-!
# Smooth approximation of interval truncation

Interval truncation `T(x) = a + (x - a)⁺ - (x - b)⁺` (the clamp of `x` to
`[a, b]` when `a ≤ b`) is Lipschitz but not smooth.  We build smooth,
zero-preserving regularizers of it from `smoothAbs`: the smooth positive part
`(x + smoothAbs ε x) / 2` replaces `x⁺`, and the constant `T_ε(0)` is
subtracted so that zero is fixed.  At positive scale the regularizers are
`C^∞`, one-Lipschitz, dominated by `|x|`, and have derivative multipliers
bounded by one.  As nonnegative scales tend to zero they converge pointwise to
the centered truncation `T(x) - T(0)`, which is `T` itself exactly when the
interval contains zero, and their slopes converge to the sign-difference
multiplier `(sign (x - a) - sign (x - b)) / 2`.  These are the ingredients of
the Sobolev chain rule for truncations: compose with `T_ε`, differentiate
smoothly, and pass to the limit by dominated convergence.

## Main results

* `smoothPositivePart`, `smoothIntervalTruncation` and their slopes.
* `hasDerivAt_smoothIntervalTruncation`,
  `contDiff_smoothIntervalTruncation`,
  `lipschitzWith_smoothIntervalTruncation`,
  `abs_smoothIntervalTruncationSlope_le_one`,
  `abs_smoothIntervalTruncation_le`: regularity and bounds at positive
  scale.
* `tendsto_smoothIntervalTruncation_centered_of_tendsto_zero`,
  `tendsto_smoothIntervalTruncation_of_tendsto_zero`,
  `tendsto_smoothIntervalTruncationSlope_of_tendsto_zero`: pointwise limits
  as the scale tends to zero.

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

/-- Smooth positive-part approximation derived from `smoothAbs`. -/
abbrev smoothPositivePart (ε x : ℝ) : ℝ :=
  (x + smoothAbs ε x) / 2

/-- Derivative multiplier of `smoothPositivePart`. -/
abbrev smoothPositivePartSlope (ε x : ℝ) : ℝ :=
  (1 + smoothAbsSlope ε x) / 2

/-- Smooth, zero-preserving approximation of centered interval truncation. -/
abbrev smoothIntervalTruncation (ε a b x : ℝ) : ℝ :=
  (a + smoothPositivePart ε (x - a) -
      smoothPositivePart ε (x - b)) -
    (a + smoothPositivePart ε (-a) -
      smoothPositivePart ε (-b))

/-- Derivative multiplier of `smoothIntervalTruncation`. -/
abbrev smoothIntervalTruncationSlope (ε a b x : ℝ) : ℝ :=
  smoothPositivePartSlope ε (x - a) -
    smoothPositivePartSlope ε (x - b)

/-- Derivative formula for smooth interval truncation. -/
theorem hasDerivAt_smoothIntervalTruncation
    {ε : ℝ} (hε : 0 < ε) (a b x : ℝ) :
    HasDerivAt (smoothIntervalTruncation ε a b)
      (smoothIntervalTruncationSlope ε a b x) x := by
  unfold smoothIntervalTruncation smoothIntervalTruncationSlope smoothPositivePart
    smoothPositivePartSlope smoothAbs smoothAbsSlope
  cas

/-- Smooth interval truncation is infinitely differentiable at positive
scale. -/
theorem contDiff_smoothIntervalTruncation
    {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothIntervalTruncation ε a b) := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (smoothAbs ε) := by
    have hinner :
        ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ ↦ x ^ 2 + ε ^ 2) :=
      (contDiff_id.pow 2).add contDiff_const
    exact
      (hinner.sqrt fun x ↦ ne_of_gt
        (smoothAbs_sq_add_pos hε x)).sub contDiff_const
  have hpos :
      ContDiff ℝ (⊤ : ℕ∞) (smoothPositivePart ε) := by
    exact (contDiff_id.add hsmooth).div_const 2
  exact
    ((contDiff_const.add
      (hpos.comp (contDiff_id.sub contDiff_const))).sub
        (hpos.comp (contDiff_id.sub contDiff_const))).sub contDiff_const

/-- Smooth interval truncation fixes zero. -/
theorem smoothIntervalTruncation_zero (ε a b : ℝ) :
    smoothIntervalTruncation ε a b 0 = 0 := by
  simp [smoothIntervalTruncation]

/-- The derivative multiplier of smooth interval truncation is continuous. -/
theorem continuous_smoothIntervalTruncationSlope
    {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    Continuous (smoothIntervalTruncationSlope ε a b) := by
  have hslope : Continuous (smoothAbsSlope ε) := by
    unfold smoothAbsSlope
    apply continuous_id.div
      (Real.continuous_sqrt.comp
        ((continuous_id.pow 2).add (continuous_const.pow 2)))
    intro x
    exact ne_of_gt (Real.sqrt_pos.2 (smoothAbs_sq_add_pos hε x))
  exact
    (((continuous_const.add
      (hslope.comp (continuous_id.sub continuous_const))).div_const 2).sub
      ((continuous_const.add
        (hslope.comp (continuous_id.sub continuous_const))).div_const 2))

/-- The derivative multiplier of smooth interval truncation has absolute
value at most one. -/
theorem abs_smoothIntervalTruncationSlope_le_one
    {ε : ℝ} (hε : 0 < ε) (a b x : ℝ) :
    |smoothIntervalTruncationSlope ε a b x| ≤ 1 := by
  have ha := abs_smoothAbsSlope_le_one hε (x - a)
  have hb := abs_smoothAbsSlope_le_one hε (x - b)
  rw [smoothIntervalTruncationSlope, smoothPositivePartSlope]
  have hsub :
      |smoothAbsSlope ε (x - a) -
          smoothAbsSlope ε (x - b)| ≤ 2 := by
    calc
      _ ≤ |smoothAbsSlope ε (x - a)| +
          |smoothAbsSlope ε (x - b)| := abs_sub _ _
      _ ≤ 2 := by linarith
  rw [show
      (1 + smoothAbsSlope ε (x - a)) / 2 -
          (1 + smoothAbsSlope ε (x - b)) / 2 =
        (smoothAbsSlope ε (x - a) -
          smoothAbsSlope ε (x - b)) / 2 by ring,
    abs_div]
  norm_num
  linarith

/-- Smooth interval truncation is one-Lipschitz at positive scale. -/
theorem lipschitzWith_smoothIntervalTruncation
    {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    LipschitzWith 1 (smoothIntervalTruncation ε a b) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_smoothIntervalTruncation hε a b x).differentiableAt
  · intro x
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one,
      Real.norm_eq_abs,
      (hasDerivAt_smoothIntervalTruncation hε a b x).deriv]
    exact abs_smoothIntervalTruncationSlope_le_one hε a b x

/-- Smooth interval truncation is dominated by absolute value. -/
theorem abs_smoothIntervalTruncation_le
    {ε : ℝ} (hε : 0 < ε) (a b x : ℝ) :
    |smoothIntervalTruncation ε a b x| ≤ |x| := by
  have h :=
    (lipschitzWith_smoothIntervalTruncation hε a b).dist_le_mul x 0
  simpa [smoothIntervalTruncation_zero] using h

/-- Smooth positive parts converge pointwise to positive part as their
nonnegative scales tend to zero. -/
theorem tendsto_smoothPositivePart_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hεnonneg : ∀ᶠ k in l, 0 ≤ ε k)
    (hε : Tendsto ε l (𝓝 0)) (x : ℝ) :
    Tendsto (fun k ↦ smoothPositivePart (ε k) x) l
      (𝓝 x⁺) := by
  have habs :=
    tendsto_smoothAbs_of_tendsto_zero hεnonneg hε x
  have hpos : x⁺ = (x + |x|) / 2 := by
    have h := add_abs_eq_two_nsmul_posPart x
    rw [two_nsmul] at h
    linarith
  simpa only [smoothPositivePart, hpos] using
    (tendsto_const_nhds.add habs).div_const 2

/-- Smooth positive-part slopes converge pointwise to the sign
coefficient. -/
theorem tendsto_smoothPositivePartSlope_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝 0)) (x : ℝ) :
    Tendsto (fun k ↦ smoothPositivePartSlope (ε k) x) l
      (𝓝 ((1 + (SignType.sign x : ℝ)) / 2)) := by
  have hslope :=
    tendsto_smoothAbsSlope_of_tendsto_zero hε x
  simpa only [smoothPositivePartSlope] using
    (tendsto_const_nhds.add hslope).div_const 2

/-- Smooth zero-preserving truncations converge pointwise to centered
interval truncation. -/
theorem tendsto_smoothIntervalTruncation_centered_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hεnonneg : ∀ᶠ k in l, 0 ≤ ε k)
    (hε : Tendsto ε l (𝓝 0))
    (a b x : ℝ) :
    Tendsto (fun k ↦ smoothIntervalTruncation (ε k) a b x) l
      (𝓝 (centeredIntervalTruncation a b x)) := by
  have hxa :=
    tendsto_smoothPositivePart_of_tendsto_zero
      hεnonneg hε (x - a)
  have hxb :=
    tendsto_smoothPositivePart_of_tendsto_zero
      hεnonneg hε (x - b)
  have hzeroa :=
    tendsto_smoothPositivePart_of_tendsto_zero
      hεnonneg hε (-a)
  have hzerob :=
    tendsto_smoothPositivePart_of_tendsto_zero
      hεnonneg hε (-b)
  have hconst : Tendsto (fun _ : ι ↦ a) l (𝓝 a) :=
    tendsto_const_nhds
  have hlimit :=
    ((hconst.add hxa).sub hxb).sub
      ((hconst.add hzeroa).sub hzerob)
  simpa [smoothIntervalTruncation, centeredIntervalTruncation,
    intervalTruncation] using hlimit

/-- Smooth zero-preserving truncations converge pointwise to interval
truncation when the interval contains zero. -/
theorem tendsto_smoothIntervalTruncation_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hεnonneg : ∀ᶠ k in l, 0 ≤ ε k)
    (hε : Tendsto ε l (𝓝 0))
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (x : ℝ) :
    Tendsto (fun k ↦ smoothIntervalTruncation (ε k) a b x) l
      (𝓝 (intervalTruncation a b x)) := by
  simpa [centeredIntervalTruncation_eq_intervalTruncation ha hb] using
    tendsto_smoothIntervalTruncation_centered_of_tendsto_zero
      hεnonneg hε a b x

/-- Slopes of smooth interval truncations converge pointwise to the
sign-difference coefficient. -/
theorem tendsto_smoothIntervalTruncationSlope_of_tendsto_zero
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : Tendsto ε l (𝓝 0)) (a b x : ℝ) :
    Tendsto (fun k ↦
      smoothIntervalTruncationSlope (ε k) a b x) l
      (𝓝 (((SignType.sign (x - a) : ℝ) -
        (SignType.sign (x - b) : ℝ)) / 2)) := by
  have ha :=
    tendsto_smoothPositivePartSlope_of_tendsto_zero
      hε (x - a)
  have hb :=
    tendsto_smoothPositivePartSlope_of_tendsto_zero
      hε (x - b)
  convert ha.sub hb using 1
  congr 2
  ring

end PDE.Analysis.Calculus
