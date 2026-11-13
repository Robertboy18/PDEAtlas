/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import PDE.Analysis.Integration.Primitive.Basic

/-!
# Superlinear scalar data

The primitive is the interval integral of the reaction. The hypotheses
below record the scalar bounds in Evans, §8.5.2, Theorem 3. The energy derivative,
the Palais–Smale condition, and the mountain-pass geometry are derived from them in
`Superlinear.Existence`.

The parameter `γ` is only assumed to be less than one half. Its positivity follows
from the primitive bounds and the mean-value theorem.
-/

@[expose] public section

noncomputable section

open Set
open PDE.Analysis (primitive hasDerivAt_primitive)

namespace PDE.Elliptic.Semilinear.Superlinear

/-- The scalar hypotheses for a superlinear reaction. The exponent is real;
the dimensional subcritical restriction is imposed by the Sobolev application. -/
structure Hypotheses (f : ℝ → ℝ) (p C γ a A : ℝ) : Prop where
  contDiff : ContDiff ℝ 1 f
  one_lt : 1 < p
  reaction_bound : ∀ z, |f z| ≤ C * (1 + |z| ^ p)
  deriv_bound : ∀ z, |deriv f z| ≤ C * (1 + |z| ^ (p - 1))
  primitive_nonneg : ∀ z, 0 ≤ primitive f z
  primitive_le : ∀ z, primitive f z ≤ γ * f z * z
  gamma_lt_half : γ < 1 / 2
  lower_pos : 0 < a
  lower_le_upper : a ≤ A
  primitive_lower : ∀ z, a * |z| ^ (p + 1) ≤ |primitive f z|
  primitive_upper : ∀ z, |primitive f z| ≤ A * |z| ^ (p + 1)

variable {f : ℝ → ℝ} {p C γ a A : ℝ}

namespace Hypotheses

/-- The derivative is the derivative of the `C¹` reaction. -/
theorem hasDerivAt (h : Hypotheses f p C γ a A) (z : ℝ) :
    HasDerivAt f (deriv f z) z :=
  (h.contDiff.differentiable (by simp) z).hasDerivAt

/-- Positivity of the lower potential bound forces strict positivity off zero. -/
theorem primitive_pos (h : Hypotheses f p C γ a A) {z : ℝ} (hz : z ≠ 0) :
    0 < primitive f z := by
  have hl := h.primitive_lower z
  rw [abs_of_nonneg (h.primitive_nonneg z)] at hl
  exact (mul_pos h.lower_pos (Real.rpow_pos_of_pos (abs_pos.mpr hz) _)).trans_le hl

/-- The upper primitive coefficient is positive. -/
theorem upper_pos (h : Hypotheses f p C γ a A) : 0 < A :=
  h.lower_pos.trans_le h.lower_le_upper

/-- The reaction vanishes at zero because its primitive has a minimum there. -/
theorem reaction_zero (h : Hypotheses f p C γ a A) : f 0 = 0 := by
  have hmin : IsMinOn (primitive f) univ 0 := by
    intro z _
    simpa using h.primitive_nonneg z
  exact (hmin.isLocalMin (by simp)).hasDerivAt_eq_zero
    (hasDerivAt_primitive h.contDiff.continuous 0)

/-- The growth coefficient in the data is nonnegative. -/
theorem coefficient_nonneg (h : Hypotheses f p C γ a A) : 0 ≤ C := by
  have hb := h.reaction_bound 0
  simpa [h.reaction_zero, Real.zero_rpow (ne_of_gt (zero_lt_one.trans h.one_lt))]
    using hb

/-- Positivity of `γ` is a consequence of the hypotheses, not an additional
assumption. A positive secant of the primitive supplies a positive derivative. -/
theorem gamma_pos (h : Hypotheses f p C γ a A) : 0 < γ := by
  have hd := hasDerivAt_primitive h.contDiff.continuous
  have hc : Continuous (primitive f) :=
    continuous_iff_continuousAt.mpr fun z ↦ (hd z).continuousAt
  obtain ⟨c, hc, hfc⟩ := exists_hasDerivAt_eq_slope (primitive f) f
    (by norm_num : (0 : ℝ) < 1) hc.continuousOn (fun z _ ↦ hd z)
  have hf1 := h.primitive_pos (by norm_num : (1 : ℝ) ≠ 0)
  have hfcpos : 0 < f c := by rw [hfc]; simpa using hf1
  have hFc := h.primitive_pos (ne_of_gt hc.1)
  have hmul : 0 < γ * (f c * c) := by
    simpa only [mul_assoc] using hFc.trans_le (h.primitive_le c)
  exact (mul_pos_iff_of_pos_right (mul_pos hfcpos hc.1)).mp hmul

end Hypotheses

end PDE.Elliptic.Semilinear.Superlinear
