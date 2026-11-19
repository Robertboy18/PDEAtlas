/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Error bounds for linear interpolation

An upper bound for the absolute second derivative controls the endpoint linear
interpolant with the factor `(b - a)^2 / 8`. The proof adds a quadratic
function to obtain a convex function, then applies its endpoint chord inequality.
Only continuity on the closed interval and classical derivatives in its interior
are required. This is the one-dimensional estimate behind the cell bound (7.1) of Hou, Wang and
Yang. The interpolant is a convex combination of its endpoint
values, so it keeps a common upper bound of them (`linearInterpolant_le`).

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 7.3, (7.1).
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Approximation

open Set

/-- The affine interpolant through two endpoint values. -/
def linearInterpolant (a b fa fb x : ℝ) : ℝ :=
  (b - x) / (b - a) * fa + (x - a) / (b - a) * fb

/-- A convex function lies below its endpoint affine interpolant. -/
theorem ConvexOn.le_linearInterpolant {f : ℝ → ℝ} {a b x : ℝ}
    (hf : ConvexOn ℝ (Set.Icc a b) f) (hab : a < b) (hx : x ∈ Set.Icc a b) :
    f x ≤ linearInterpolant a b (f a) (f b) x := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  have hpoint : (b - x) / (b - a) * a + (x - a) / (b - a) * b = x := by
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  have h := hf.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩
    (div_nonneg (sub_nonneg.mpr hx.2) hden.le)
    (div_nonneg (sub_nonneg.mpr hx.1) hden.le) hsum
  simpa only [smul_eq_mul, hpoint, linearInterpolant] using h

private theorem sub_linearInterpolant_le {f f' f'' : ℝ → ℝ} {a b x M : ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt f (f' y) y)
    (hderiv' : ∀ y ∈ Set.Ioo a b, HasDerivAt f' (f'' y) y)
    (hlower : ∀ y ∈ Set.Ioo a b, -M ≤ f'' y) (hx : x ∈ Set.Icc a b) :
    f x - linearInterpolant a b (f a) (f b) x ≤ M * (x - a) * (b - x) / 2 := by
  let g := fun y ↦ f y + M / 2 * y ^ 2
  let g' := fun y ↦ f' y + M * y
  have hg : ConvexOn ℝ (Set.Icc a b) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := g')
      (f'' := fun y ↦ f'' y + M) (convex_Icc a b)
      (hcont.add (continuousOn_const.mul (continuousOn_id.pow 2)))
    · intro y hy
      have hy' : y ∈ Set.Ioo a b := by simpa only [interior_Icc] using hy
      have hquadratic : HasDerivAt (fun z ↦ M / 2 * z ^ 2) (M * y) y := by
        convert (hasDerivAt_pow 2 y).const_mul (M / 2) using 1
        ring
      exact ((hderiv y hy').fun_add hquadratic).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo a b := by simpa only [interior_Icc] using hy
      exact ((hderiv' y hy').fun_add (hasDerivAt_const_mul M)).hasDerivWithinAt
    · intro y hy
      have hy' : y ∈ Set.Ioo a b := by simpa only [interior_Icc] using hy
      linarith [hlower y hy']
  have hchord := ConvexOn.le_linearInterpolant hg hab hx
  have hidentity : linearInterpolant a b (g a) (g b) x - g x =
      linearInterpolant a b (f a) (f b) x - f x + M * (x - a) * (b - x) / 2 := by
    dsimp [linearInterpolant, g]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  linarith

/-- If `|f''| ≤ M` on `(a, b)`, the endpoint interpolant is within `M (x - a) (b - x) / 2`
of `f` at `x`. -/
theorem abs_sub_linearInterpolant_le {f f' f'' : ℝ → ℝ} {a b x M : ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt f (f' y) y)
    (hderiv' : ∀ y ∈ Set.Ioo a b, HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Ioo a b, |f'' y| ≤ M) (hx : x ∈ Set.Icc a b) :
    |f x - linearInterpolant a b (f a) (f b) x| ≤ M * (x - a) * (b - x) / 2 := by
  apply abs_le.mpr
  constructor
  · have hneg := sub_linearInterpolant_le (M := M) (f := fun y ↦ -f y)
      (f' := fun y ↦ -f' y) (f'' := fun y ↦ -f'' y) hab hcont.neg
      (fun y hy ↦ (hderiv y hy).neg) (fun y hy ↦ (hderiv' y hy).neg)
      (fun y hy ↦ by linarith [(abs_le.mp (hbound y hy)).2]) hx
    have hid : linearInterpolant a b (-f a) (-f b) x =
        -linearInterpolant a b (f a) (f b) x := by unfold linearInterpolant; ring
    rw [hid] at hneg
    linarith
  · exact sub_linearInterpolant_le hab hcont hderiv hderiv'
      (fun y hy ↦ (abs_le.mp (hbound y hy)).1) hx

/-- If `|f''| ≤ M` on `(a, b)`, the endpoint interpolant is within `M (b - a)^2 / 8` of `f`
on `[a, b]`. -/
theorem abs_sub_linearInterpolant_le_uniform {f f' f'' : ℝ → ℝ} {a b x M : ℝ}
    (hab : a < b) (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ y ∈ Set.Ioo a b, HasDerivAt f (f' y) y)
    (hderiv' : ∀ y ∈ Set.Ioo a b, HasDerivAt f' (f'' y) y)
    (hbound : ∀ y ∈ Set.Ioo a b, |f'' y| ≤ M) (hx : x ∈ Set.Icc a b) :
    |f x - linearInterpolant a b (f a) (f b) x| ≤ M * (b - a) ^ 2 / 8 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound ((a + b) / 2) ⟨by linarith, by linarith⟩)
  apply (abs_sub_linearInterpolant_le hab hcont hderiv hderiv' hbound hx).trans
  have hprod : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
    nlinarith [sq_nonneg (x - (a + b) / 2)]
  nlinarith [mul_le_mul_of_nonneg_left hprod hM]

/-- Endpoint interpolation preserves a common upper bound of its two values. -/
theorem linearInterpolant_le {a b x fa fb B : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b)
    (hfa : fa ≤ B) (hfb : fb ≤ B) : linearInterpolant a b fa fb x ≤ B := by
  have hden : 0 < b - a := sub_pos.mpr hab
  have hw₀ : 0 ≤ (b - x) / (b - a) := div_nonneg (sub_nonneg.mpr hx.2) hden.le
  have hw₁ : 0 ≤ (x - a) / (b - a) := div_nonneg (sub_nonneg.mpr hx.1) hden.le
  have hsum : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
    rw [← add_div, show b - x + (x - a) = b - a by ring, div_self hden.ne']
  unfold linearInterpolant
  calc _ ≤ (b - x) / (b - a) * B + (x - a) / (b - a) * B :=
        add_le_add (mul_le_mul_of_nonneg_left hfa hw₀) (mul_le_mul_of_nonneg_left hfb hw₁)
    _ = B := by rw [← add_mul, hsum, one_mul]

end PDE.Analysis.Approximation
