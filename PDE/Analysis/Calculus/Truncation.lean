/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import PDE.Analysis.Calculus.AbsoluteValue

/-!
# Positive parts and interval truncations

We derive almost-everywhere chain rules for scalar functions with
finitely many kinks: the positive part `x⁺`, the negative part `x⁻`, and the
interval truncation `a + (x - a)⁺ - (x - b)⁺`, which is the clamp
`min b (max a x)` when `a ≤ b`.  If `f : ℝ → ℝ` has derivative `f'` almost
everywhere, then `(f)⁺` has derivative `((1 + sign f) / 2) f'` almost
everywhere, and similarly for `f⁻` and for the truncation with the
coefficient `(sign (f - a) - sign (f - b)) / 2`.  The coefficient is `1`
where `f` lies strictly inside the interval and `0` strictly outside; on the
endpoint fibres it takes an intermediate value, which is harmless because
`f'` vanishes almost everywhere there.  All three rules follow from the
almost-everywhere chain rule for `|f|` (`ae_hasDerivAt_abs`) through the
identities `x⁺ = (x + |x|) / 2` and `x⁻ = (|x| - x) / 2`, so the level-set
argument is not repeated.  These are the one-dimensional facts behind the
Sobolev truncation results, the counterparts of Problem 18 of Evans, §5.10,
which asks for `Du⁺ = Du` almost everywhere on `{u > 0}`, `Du⁺ = 0` almost
everywhere on `{u ≤ 0}` and `Du = 0` almost everywhere on `{u = 0}` when
`u ∈ W^{1,p}(U)`.

## Main results

* `intervalTruncation`, `centeredIntervalTruncation`: truncation to `[a, b]`
  and its zero-preserving variant, with `intervalTruncation_eq_min_max` and
  the one-Lipschitz bounds.
* `ae_hasDerivAt_posPart`, `ae_hasDerivAt_negPart`: chain rules for
  Mathlib's canonical positive and negative parts.
* `ae_hasDerivAt_intervalTruncation`: chain rule for interval truncation.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.10, Problem 18, p. 308.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 7 (Sobolev Spaces), pp. 144-176.
  <https://doi.org/10.1007/978-3-642-61798-0_7>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory

namespace PDE.Analysis.Calculus

private theorem real_posPart_eq (x : ℝ) :
    x⁺ = (x + |x|) / 2 := by
  have h := add_abs_eq_two_nsmul_posPart x
  rw [two_nsmul] at h
  linarith

private theorem real_negPart_eq (x : ℝ) :
    x⁻ = (|x| - x) / 2 := by
  have h := abs_sub_eq_two_nsmul_negPart x
  rw [two_nsmul] at h
  linarith

/-- Truncation to the interval with endpoints `a` and `b`. When `a ≤ b`, this
is `min b (max a x)`. -/
def intervalTruncation (a b x : ℝ) : ℝ :=
  a + (x - a)⁺ - (x - b)⁺

/-- Interval truncation centered to fix zero. On finite-measure domains the
subtracted constant can be restored after composition. -/
def centeredIntervalTruncation (a b x : ℝ) : ℝ :=
  intervalTruncation a b x - intervalTruncation a b 0

/-- The algebraic interval truncation is the usual clamping operation. -/
theorem intervalTruncation_eq_min_max
    {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    intervalTruncation a b x = min b (max a x) := by
  change a + max (x - a) 0 - max (x - b) 0 = min b (max a x)
  by_cases hxa : x ≤ a
  · have hxb : x ≤ b := hxa.trans hab
    simp [max_eq_right (sub_nonpos.mpr hxa),
      max_eq_right (sub_nonpos.mpr hxb), max_eq_left hxa,
      min_eq_right hab]
  · have hax : a ≤ x := le_of_not_ge hxa
    by_cases hxb : x ≤ b
    · simp [max_eq_left (sub_nonneg.mpr hax),
        max_eq_right (sub_nonpos.mpr hxb), max_eq_right hax,
        min_eq_right hxb]
    · have hbx : b ≤ x := le_of_not_ge hxb
      simp [max_eq_left (sub_nonneg.mpr hax),
        max_eq_left (sub_nonneg.mpr hbx), max_eq_right hax,
        min_eq_left hbx]

/-- Truncation to a nonempty interval is one-Lipschitz. -/
theorem lipschitzWith_intervalTruncation
    {a b : ℝ} (hab : a ≤ b) :
    LipschitzWith 1 (intervalTruncation a b) := by
  rw [show intervalTruncation a b = fun x ↦ min b (max a x) by
    funext x
    exact intervalTruncation_eq_min_max hab x]
  simpa only [Function.id_def, min_comm] using
    ((LipschitzWith.id.const_max a).min_const b)

/-- Centered interval truncation fixes zero. -/
@[simp]
theorem centeredIntervalTruncation_zero (a b : ℝ) :
    centeredIntervalTruncation a b 0 = 0 := by
  simp [centeredIntervalTruncation]

/-- Centering preserves the one-Lipschitz bound for interval truncation. -/
theorem lipschitzWith_centeredIntervalTruncation
    {a b : ℝ} (hab : a ≤ b) :
    LipschitzWith 1 (centeredIntervalTruncation a b) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simpa [centeredIntervalTruncation, dist_sub_right] using
    (lipschitzWith_intervalTruncation hab).dist_le_mul x y

/-- If the truncation interval contains zero, centering changes nothing. -/
theorem centeredIntervalTruncation_eq_intervalTruncation
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    centeredIntervalTruncation a b = intervalTruncation a b := by
  funext x
  rw [centeredIntervalTruncation]
  have hzero : intervalTruncation a b 0 = 0 := by
    rw [intervalTruncation_eq_min_max (ha.trans hb)]
    simp [ha, hb]
  simp [hzero]

/-- Almost-everywhere chain rule for Mathlib's canonical positive part. -/
theorem ae_hasDerivAt_posPart
    {f f' : ℝ → ℝ}
    (hf : ∀ᵐ x ∂volume, HasDerivAt f (f' x) x) :
    ∀ᵐ x ∂volume,
      HasDerivAt (fun y ↦ (f y)⁺)
        (((1 + (SignType.sign (f x) : ℝ)) / 2) * f' x) x := by
  filter_upwards [hf, ae_hasDerivAt_abs hf] with x hx habs
  have h := (hx.add habs).div_const 2
  have hcoeff :
      (1 + (SignType.sign (f x) : ℝ)) / 2 * f' x =
        (f' x + (SignType.sign (f x) : ℝ) * f' x) / 2 := by
    ring
  rw [hcoeff]
  simpa only [real_posPart_eq, Pi.add_apply] using h

/-- Almost-everywhere chain rule for Mathlib's canonical negative part. -/
theorem ae_hasDerivAt_negPart
    {f f' : ℝ → ℝ}
    (hf : ∀ᵐ x ∂volume, HasDerivAt f (f' x) x) :
    ∀ᵐ x ∂volume,
      HasDerivAt (fun y ↦ (f y)⁻)
        ((((SignType.sign (f x) : ℝ) - 1) / 2) * f' x) x := by
  filter_upwards [hf, ae_hasDerivAt_abs hf] with x hx habs
  have h := (habs.sub hx).div_const 2
  have hcoeff :
      ((SignType.sign (f x) : ℝ) - 1) / 2 * f' x =
        ((SignType.sign (f x) : ℝ) * f' x - f' x) / 2 := by
    ring
  rw [hcoeff]
  simpa only [real_negPart_eq, Pi.sub_apply] using h

/-- Almost-everywhere chain rule for interval truncation. When `a ≤ b`, the
coefficient is one in the open interval and zero outside the closed interval.
Its endpoint value is harmless because the inner derivative vanishes almost
everywhere on each endpoint fiber. Without `a ≤ b`, this remains the derivative
of the displayed algebraic formula but does not describe interval clamping. -/
theorem ae_hasDerivAt_intervalTruncation
    {f f' : ℝ → ℝ} (a b : ℝ)
    (hf : ∀ᵐ x ∂volume, HasDerivAt f (f' x) x) :
    ∀ᵐ x ∂volume,
      HasDerivAt (fun y ↦ intervalTruncation a b (f y))
        ((((SignType.sign (f x - a) : ℝ) -
          (SignType.sign (f x - b) : ℝ)) / 2) * f' x) x := by
  have hfa :
      ∀ᵐ x ∂volume, HasDerivAt (fun y ↦ f y - a) (f' x) x := by
    filter_upwards [hf] with x hx
    simpa using hx.sub_const a
  have hfb :
      ∀ᵐ x ∂volume, HasDerivAt (fun y ↦ f y - b) (f' x) x := by
    filter_upwards [hf] with x hx
    simpa using hx.sub_const b
  filter_upwards
    [ae_hasDerivAt_posPart hfa,
      ae_hasDerivAt_posPart hfb] with x hpa hpb
  have h :
      HasDerivAt
        (fun y ↦
          a + ((f y - a)⁺ - (f y - b)⁺))
        ((1 + (SignType.sign (f x - a) : ℝ)) / 2 * f' x -
          (1 + (SignType.sign (f x - b) : ℝ)) / 2 * f' x) x :=
    (hasDerivAt_const_add_iff a).2 (hpa.sub hpb)
  have hcoeff :
      ((SignType.sign (f x - a) : ℝ) -
          (SignType.sign (f x - b) : ℝ)) / 2 * f' x =
        (1 + (SignType.sign (f x - a) : ℝ)) / 2 * f' x -
          (1 + (SignType.sign (f x - b) : ℝ)) / 2 * f' x := by
    ring
  rw [hcoeff]
  apply h.congr_of_eventuallyEq
  filter_upwards with y
  simp [intervalTruncation]
  ring

end PDE.Analysis.Calculus
