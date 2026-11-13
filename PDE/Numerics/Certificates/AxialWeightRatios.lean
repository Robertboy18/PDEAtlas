/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.AxialWeight

/-!
# Cell bounds of ratios of axial weights

For axial weights `w`, `w'` and a factor `|x₀|^p |x|^q`, on the open quadrant in a cell,
`ratioUpper w w' p q` and `ratioLower w w' p q` bound `w/w'` from above and below by the bounds
of the shifted weights `|x₀|^p |x|^q w` and `|x₀|^p |x|^q w'`; the factor cancels a singularity
that both weights share, at the axis (`p = 1/2` for the weights with the factor `|x₀|^{-1/2}`) or
at the origin. `shiftRatioUpper w w' p q` bounds `w/w'` by `|x₀|^p |x|^q U`, with `U` the upper
bound of `w` over the lower bound of the shifted `w'`: the factor survives into the bound, for
ratios that are singular or vanish at the axis or the origin.

## Main definitions

* `ratioUpper`: the upper bound of `|x₀|^p |x|^q w` on a cell over the lower bound of
  `|x₀|^p |x|^q w'`, when the latter is positive.
* `ratioLower`: the lower bound of `|x₀|^p |x|^q w` over the upper bound of `|x₀|^p |x|^q w'`.
* `shiftRatioUpper`: the upper bound of `w` over the lower bound of `|x₀|^p |x|^q w'`.

## Main results

* `div_le_ratioUpper`: on the cell, `w(x) / w'(x) ≤ U` when `ratioUpper` returns `some U`.
* `ratioLower_le_div`: on the cell, `L ≤ w(x) / w'(x)` when `ratioLower` returns `some L`.
* `div_le_mul_shiftRatioUpper`: on the cell, `w(x) / w'(x) ≤ |x₀|^p |x|^q U` when
  `shiftRatioUpper` returns `some U`.
-/

@[expose] public section

namespace CAS.Numerics.AxialWeight

variable {C : PlaneCell} {bits : ℕ} {x : EuclideanSpace ℝ (Fin 2)}

/-- The upper bound of `|x₀|^p |x|^q w` on `C` over the lower bound of `|x₀|^p |x|^q w'`, when
the latter is positive. -/
def ratioUpper (w w' : AxialWeight) (p q : ℚ) (C : PlaneCell) (bits : ℕ) : Option ℚ :=
  match axialTermsUpper (AxialTerm.shift p q w.terms) C bits with
  | some u =>
    if 0 < axialTermsLower (AxialTerm.shift p q w'.terms) C bits then
      some (u / axialTermsLower (AxialTerm.shift p q w'.terms) C bits)
    else none
  | none => none

/-- The lower bound of `|x₀|^p |x|^q w` on `C` over the upper bound of `|x₀|^p |x|^q w'`, when
the lower bound of `|x₀|^p |x|^q w'` is positive. -/
def ratioLower (w w' : AxialWeight) (p q : ℚ) (C : PlaneCell) (bits : ℕ) : Option ℚ :=
  match axialTermsUpper (AxialTerm.shift p q w'.terms) C bits with
  | some u =>
    if 0 < axialTermsLower (AxialTerm.shift p q w'.terms) C bits then
      some (axialTermsLower (AxialTerm.shift p q w.terms) C bits / u)
    else none
  | none => none

/-- The upper bound of `w` on `C` over the lower bound of `|x₀|^p |x|^q w'`, when the latter is
positive. -/
def shiftRatioUpper (w w' : AxialWeight) (p q : ℚ) (C : PlaneCell) (bits : ℕ) : Option ℚ :=
  match axialTermsUpper w.terms C bits with
  | some u =>
    if 0 < axialTermsLower (AxialTerm.shift p q w'.terms) C bits then
      some (u / axialTermsLower (AxialTerm.shift p q w'.terms) C bits)
    else none
  | none => none

/-- At a point with `x₀ > 0` the shift factor `|x₀|^p |x|^q` is positive. -/
theorem shift_factor_pos (hx : 0 < x 0) (p q : ℚ) : 0 < |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) := by
  have h0 := abs_pos.2 hx.ne'
  have hn : 0 < ‖x‖ := h0.trans_le (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x 0)
  positivity

/-- **Upper bounds of ratios on a cell.** -/
theorem div_le_ratioUpper {w w' : AxialWeight} {p q : ℚ} {U : ℚ} (hC : C.Valid) (hx : C.Mem x)
    (h : w.ratioUpper w' p q C bits = some U) : w.value x / w'.value x ≤ U := by
  unfold ratioUpper at h
  split at h
  · rename_i u hu
    split_ifs at h with hl
    cases h
    push_cast
    exact div_le_of_shift w' hC hx hu hl
  · simp at h

/-- **Lower bounds of ratios on a cell.** -/
theorem ratioLower_le_div {w w' : AxialWeight} {p q : ℚ} {L : ℚ} (hC : C.Valid) (hx : C.Mem x)
    (h : w.ratioLower w' p q C bits = some L) : (L : ℝ) ≤ w.value x / w'.value x := by
  unfold ratioLower at h
  split at h
  · rename_i u hu
    split_ifs at h with hl
    cases h
    have hs := axialTermsLower_le (w.nonneg.shift p q) hC hx bits
    have hs' := le_axialTermsUpper (w'.nonneg.shift p q) hC hx bits hu
    have hl' := axialTermsLower_le (w'.nonneg.shift p q) hC hx bits
    rw [axialTermsValue_shift p q _ hx.1] at hs hs' hl'
    have hK := shift_factor_pos hx.1 p q
    have hl0 : (0 : ℝ) < axialTermsLower (AxialTerm.shift p q w'.terms) C bits := by
      exact_mod_cast hl
    have hw' : 0 < |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) * axialTermsValue w'.terms x :=
      hl0.trans_le hl'
    rw [value, value, ← mul_div_mul_left (axialTermsValue w.terms x) _ hK.ne']
    push_cast
    exact div_le_div₀ (mul_nonneg hK.le (w.value_nonneg hx.1)) hs hw' hs'
  · simp at h

/-- **Ratios with the factor kept outside.** -/
theorem div_le_mul_shiftRatioUpper {w w' : AxialWeight} {p q : ℚ} {U : ℚ} (hC : C.Valid)
    (hx : C.Mem x) (h : w.shiftRatioUpper w' p q C bits = some U) :
    w.value x / w'.value x ≤ |x 0| ^ (p : ℝ) * ‖x‖ ^ (q : ℝ) * U := by
  unfold shiftRatioUpper at h
  split at h
  · rename_i u hu
    split_ifs at h with hl
    cases h
    push_cast
    exact div_le_mul_of_shift w' hC hx hu hl
  · simp at h

end CAS.Numerics.AxialWeight
