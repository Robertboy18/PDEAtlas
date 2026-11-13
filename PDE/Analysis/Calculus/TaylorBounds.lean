/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Taylor bounds from derivative enclosures

Cauchy's mean value theorem transfers a bound on a derivative divided by a
monomial to the corresponding bound on its primitive. Repeated application
gives Taylor remainder bounds using explicit derivative functions, including
piecewise polynomial functions whose derivatives match at subdivision points.
-/

@[expose] public section

namespace PDE

open Set

/-- A weighted derivative enclosure integrates with the exact monomial factor.
The intermediate coefficient remains in the given interval. -/
theorem exists_monomial_remainder
    {f f' : ℝ → ℝ} {r lo hi : ℝ} (n : ℕ) (hr : 0 < r)
    (hcont : ContinuousOn f (Icc 0 r))
    (hderiv : ∀ x ∈ Ioo 0 r, HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Ioo 0 r, f' x / x ^ n ∈ Icc lo hi) :
    ∃ c ∈ Icc lo hi, f r - f 0 = r ^ (n + 1) / (n + 1) * c := by
  obtain ⟨x, hx, heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hr hcont hderiv
    (fun x ↦ x ^ (n + 1)) (fun x ↦ (n + 1 : ℝ) * x ^ n)
    (continuousOn_id.pow (n + 1)) (fun x _ ↦ by
      simpa using hasDerivAt_pow (n + 1) x)
  refine ⟨f' x / x ^ n, hbound x hx, ?_⟩
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hxpow : x ^ n ≠ 0 := pow_ne_zero n hx.1.ne'
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero] at heq
  field_simp
  nlinarith only [heq]

/-- A zero first derivative leaves a quadratic remainder enclosed by the
second derivative on the segment. -/
theorem exists_quadratic_remainder
    {f f' f'' : ℝ → ℝ} {r lo hi : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (Icc 0 r)) (hcont' : ContinuousOn f' (Icc 0 r))
    (hderiv : ∀ x ∈ Ioo 0 r, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x ∈ Ioo 0 r, HasDerivAt f' (f'' x) x)
    (hzero : f' 0 = 0) (hbound : ∀ x ∈ Ioo 0 r, f'' x ∈ Icc lo hi) :
    ∃ c ∈ Icc lo hi, f r - f 0 = r ^ 2 / 2 * c := by
  have hweighted : ∀ x ∈ Ioo 0 r, f' x / x ^ 1 ∈ Icc lo hi := by
    intro x hx
    obtain ⟨y, hy, heq⟩ := exists_hasDerivAt_eq_slope f' f'' hx.1
      (hcont'.mono (Icc_subset_Icc le_rfl hx.2.le))
      (fun y hy ↦ hderiv' y ⟨hy.1, hy.2.trans hx.2⟩)
    simp only [hzero, sub_zero] at heq
    rw [pow_one, ← heq]
    exact hbound y ⟨hy.1, hy.2.trans hx.2⟩
  convert exists_monomial_remainder 1 hr hcont hderiv hweighted using 1
  norm_num

/-- A function with zero value and second derivative at the origin has a
regular quotient with a quadratic remainder controlled by its third derivative.
Applied to the radial derivative of an even function, this is the fourth
derivative estimate required for the regularized axis quotient. -/
theorem exists_cubic_quotient_remainder
    {f f' f'' f''' : ℝ → ℝ} {r lo hi : ℝ} (hr : 0 < r)
    (hcont : ContinuousOn f (Icc 0 r)) (hcont' : ContinuousOn f' (Icc 0 r))
    (hcont'' : ContinuousOn f'' (Icc 0 r))
    (hderiv : ∀ x ∈ Ioo 0 r, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x ∈ Ioo 0 r, HasDerivAt f' (f'' x) x)
    (hderiv'' : ∀ x ∈ Ioo 0 r, HasDerivAt f'' (f''' x) x)
    (hzero : f 0 = 0) (hzero'' : f'' 0 = 0)
    (hbound : ∀ x ∈ Ioo 0 r, f''' x ∈ Icc lo hi) :
    ∃ c ∈ Icc lo hi, f r / r = f' 0 + r ^ 2 / 6 * c := by
  have hweighted : ∀ x ∈ Ioo 0 r,
      (f' x - f' 0) / x ^ 2 ∈ Icc (lo / 2) (hi / 2) := by
    intro x hx
    obtain ⟨c, hc, heq⟩ := exists_quadratic_remainder hx.1
      (hcont'.mono (Icc_subset_Icc le_rfl hx.2.le))
      (hcont''.mono (Icc_subset_Icc le_rfl hx.2.le))
      (fun y hy ↦ hderiv' y ⟨hy.1, hy.2.trans hx.2⟩)
      (fun y hy ↦ hderiv'' y ⟨hy.1, hy.2.trans hx.2⟩) hzero''
      (fun y hy ↦ hbound y ⟨hy.1, hy.2.trans hx.2⟩)
    have hratio : (f' x - f' 0) / x ^ 2 = c / 2 := by
      rw [heq]
      field_simp [hx.1.ne']
    rw [hratio]
    exact ⟨by linarith [hc.1], by linarith [hc.2]⟩
  obtain ⟨c, hc, heq⟩ := exists_monomial_remainder
    (f := fun x ↦ f x - x * f' 0) (f' := fun x ↦ f' x - f' 0) 2 hr
    (hcont.sub (continuousOn_id.mul continuousOn_const))
    (fun x hx ↦ by
      convert (hderiv x hx).sub ((hasDerivAt_id x).mul_const (f' 0)) using 1 <;>
        first | rfl | simp only [one_mul])
    hweighted
  refine ⟨2 * c, ⟨by linarith [hc.1], by linarith [hc.2]⟩, ?_⟩
  simp only [hzero, zero_mul, sub_self, sub_zero] at heq
  field_simp
  nlinarith only [heq]

/-- The quadratic remainder formula also holds on a segment reduced to the origin. -/
theorem exists_quadratic_remainder_of_nonneg
    {f f' f'' : ℝ → ℝ} {r lo hi : ℝ} (hr : 0 ≤ r)
    (hcont : ContinuousOn f (Icc 0 r)) (hcont' : ContinuousOn f' (Icc 0 r))
    (hderiv : ∀ x ∈ Ioo 0 r, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x ∈ Ioo 0 r, HasDerivAt f' (f'' x) x)
    (hzero : f' 0 = 0) (hbound : ∀ x ∈ Icc 0 r, f'' x ∈ Icc lo hi) :
    ∃ c ∈ Icc lo hi, f r - f 0 = r ^ 2 / 2 * c := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    exact ⟨f'' 0, hbound 0 ⟨le_rfl, le_rfl⟩, by simp⟩
  · exact exists_quadratic_remainder hr hcont hcont' hderiv hderiv' hzero
      (fun x hx ↦ hbound x ⟨hx.1.le, hx.2.le⟩)

/-- The cubic quotient remainder includes the limiting derivative at the origin.
No division by zero is used to represent that regularized axis value. -/
theorem exists_regularized_cubic_quotient_remainder
    {f f' f'' f''' : ℝ → ℝ} {r lo hi : ℝ} (hr : 0 ≤ r)
    (hcont : ContinuousOn f (Icc 0 r)) (hcont' : ContinuousOn f' (Icc 0 r))
    (hcont'' : ContinuousOn f'' (Icc 0 r))
    (hderiv : ∀ x ∈ Ioo 0 r, HasDerivAt f (f' x) x)
    (hderiv' : ∀ x ∈ Ioo 0 r, HasDerivAt f' (f'' x) x)
    (hderiv'' : ∀ x ∈ Ioo 0 r, HasDerivAt f'' (f''' x) x)
    (hzero : f 0 = 0) (hzero'' : f'' 0 = 0)
    (hbound : ∀ x ∈ Icc 0 r, f''' x ∈ Icc lo hi) :
    ∃ c ∈ Icc lo hi,
      (if r = 0 then f' 0 else f r / r) = f' 0 + r ^ 2 / 6 * c := by
  rcases hr.eq_or_lt with hr | hr
  · subst r
    exact ⟨f''' 0, hbound 0 ⟨le_rfl, le_rfl⟩, by simp⟩
  · rw [ite_eq_right hr.ne']
    exact exists_cubic_quotient_remainder hr hcont hcont' hcont''
      hderiv hderiv' hderiv'' hzero hzero'' (fun x hx ↦ hbound x ⟨hx.1.le, hx.2.le⟩)

end PDE
