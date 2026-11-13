/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity.Finset
import PDE.Analysis.Calculus.LevelSet

/-!
# Almost-everywhere chain rule for absolute value

If a real function is differentiable almost everywhere, so is its absolute
value, and we identify the derivative almost everywhere. Where the function is
nonzero this is Mathlib's ordinary chain rule. On the zero level set the
derivative vanishes almost everywhere by `ae_deriv_eq_zero_on_levelSet`. We
also prove the elementary bounds `|sign x| ≤ 1` and
`|(sign (x - a) - sign (x - b)) / 2| ≤ 1` on the slopes of `|·|` and of centered interval
truncations, which the Sobolev composition theorems share.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Calculus

/-- The real sign of a number has absolute value at most one. -/
theorem abs_coe_sign_le_one (x : ℝ) : |(SignType.sign x : ℝ)| ≤ 1 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [sign_neg hx]
  · subst x
    simp
  · simp [sign_pos hx]

/-- The averaged difference of two real signs, the slope of a centered interval truncation, has
absolute value at most one. -/
theorem abs_sign_sub_sign_div_two_le_one (a b x : ℝ) :
    |((SignType.sign (x - a) : ℝ) - (SignType.sign (x - b) : ℝ)) / 2| ≤ 1 := by
  have ha := abs_coe_sign_le_one (x - a)
  have hb := abs_coe_sign_le_one (x - b)
  rw [abs_div]
  norm_num
  calc
    |(SignType.sign (x - a) : ℝ) - (SignType.sign (x - b) : ℝ)| / 2
        ≤ (|(SignType.sign (x - a) : ℝ)| + |(SignType.sign (x - b) : ℝ)|) / 2 := by
      gcongr
      exact abs_sub _ _
    _ ≤ 1 := by linarith

/-- If `f` has derivative `f'` almost everywhere, then `|f|` has derivative
`sign(f) f'` almost everywhere. -/
theorem ae_hasDerivAt_abs
    {f f' : ℝ → ℝ}
    (hf : ∀ᵐ x ∂volume, HasDerivAt f (f' x) x) :
    ∀ᵐ x ∂volume,
      HasDerivAt (fun y ↦ |f y|)
        ((SignType.sign (f x) : ℝ) * f' x) x := by
  filter_upwards
    [hf, ae_deriv_eq_zero_on_levelSet f 0] with x hx hlevel
  by_cases hfx : f x = 0
  · have hderiv : f' x = 0 := by
      rw [← hx.deriv, hlevel hfx]
    have hx0 : HasDerivAt f 0 x := by
      simpa [hderiv] using hx
    have habs0 : HasDerivAt (fun y ↦ |f y|) 0 x := by
      apply HasDerivAt.of_isLittleO
      simpa [hfx, Real.norm_eq_abs] using hx0.isLittleO.norm_left
    simpa [hfx, hderiv] using habs0
  · rcases lt_or_gt_of_ne hfx with hneg | hpos
    · have hnear : ∀ᶠ y in 𝓝 x, f y < 0 :=
        hx.continuousAt (Iio_mem_nhds hneg)
      have habs : HasDerivAt (fun y ↦ |f y|) (-f' x) x := by
        apply hx.neg.congr_of_eventuallyEq
        filter_upwards [hnear] with y hy
        simp [abs_of_neg hy]
      have hs : SignType.sign (f x) = -1 :=
        sign_eq_neg_one_iff.mpr hneg
      simpa [hs] using habs
    · have hnear : ∀ᶠ y in 𝓝 x, 0 < f y :=
        hx.continuousAt (Ioi_mem_nhds hpos)
      have habs : HasDerivAt (fun y ↦ |f y|) (f' x) x := by
        apply hx.congr_of_eventuallyEq
        filter_upwards [hnear] with y hy
        simp [abs_of_pos hy]
      have hs : SignType.sign (f x) = 1 :=
        sign_eq_one_iff.mpr hpos
      simpa [hs] using habs

end PDE.Analysis.Calculus
