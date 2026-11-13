/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PositivePartRpow

/-!
# Regularity of the superquadratic wave source

For `p>2`, the nonlinearity `|s|^p` is `C²` across zero. This follows
by writing it as the sum of two positive-part powers. It supplies the source
regularity needed by the three-dimensional retarded Kirchhoff construction.
-/

@[expose] public noncomputable section

namespace WaveEquation.SmallData

/-- A positive-part power of exponent greater than two is twice continuously
differentiable, including at its interface. -/
theorem contDiff_two_posPart_rpow {p : ℝ} (hp : 2 < p) :
    ContDiff ℝ 2 (fun x : ℝ ↦ x⁺ ^ p) := by
  rw [show (2 : WithTop ℕ∞) = (1 : ℕ) + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun x ↦ (PDE.Analysis.hasDerivAt_posPart_rpow (by linarith) x).differentiableAt, ?_, ?_⟩
  · norm_num
  · have hd : deriv (fun x : ℝ ↦ x⁺ ^ p) = fun x ↦ p * x⁺ ^ (p - 1) :=
      funext fun x ↦ (PDE.Analysis.hasDerivAt_posPart_rpow (by linarith) x).deriv
    rw [hd]
    exact contDiff_const.mul (PDE.Analysis.contDiff_one_posPart_rpow (by linarith))

/-- The absolute power source is `C²` for every real exponent above two. -/
theorem contDiff_two_abs_rpow {p : ℝ} (hp : 2 < p) :
    ContDiff ℝ 2 (fun x : ℝ ↦ |x| ^ p) := by
  have heq : (fun x : ℝ ↦ |x| ^ p) = fun x ↦ x⁺ ^ p + (-x)⁺ ^ p := by
    funext x
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx, posPart_eq_self.mpr hx,
        posPart_eq_zero.mpr (neg_nonpos.mpr hx), Real.zero_rpow (by linarith), add_zero]
    · rw [abs_of_nonpos hx, posPart_eq_zero.mpr hx,
        posPart_eq_self.mpr (neg_nonneg.mpr hx), Real.zero_rpow (by linarith), zero_add]
  rw [heq]
  exact (contDiff_two_posPart_rpow hp).add ((contDiff_two_posPart_rpow hp).comp contDiff_neg)

end WaveEquation.SmallData
