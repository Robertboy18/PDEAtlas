/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Asymptotics.NonstationaryPhase.Euclidean.Transfer

/-!
# Rapid decay for Euclidean nonstationary phase

A compactly supported smooth amplitude has inverse-frequency decay of every
order if the smooth phase has no critical point on its topological support.
At each step, integration by parts replaces the amplitude by the divergence of
its product with the normalized phase gradient. Smoothness and support control
are proved for this transfer, and the final constant comes from an L¹ norm.
The argument applies in arbitrary finite dimension to complex Banach amplitudes.

`exists_norm_integral_osc_smul_le_pow` is the bound `O(ε^m)` in Evans's stationary phase
method, §4.5.3(b), for an amplitude whose support contains no critical point, with frequency
`ξ = 1 / ε`. Evans changes variables near each point of the support to make the phase affine,
Lemma 3(i), and applies Lemma 1; we integrate by parts along `∇φ / |∇φ|²` on the whole support
(`transferAmplitude`), so no charts or partition of unity are needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), Lemma 1, p. 221, Lemma 3(i), p. 223, and the
  stationary phase method, p. 226. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.NonstationaryPhase

open MeasureTheory

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
/-- A smooth phase noncritical on the compact support of a smooth amplitude
gives every inverse power of frequency for the whole-space oscillatory integral.
The constants are obtained from the transferred amplitudes, not supplied as
regularity or estimate hypotheses. In particular, complex Banach amplitudes
are allowed, and no noncriticality is required outside the original support. -/
theorem exists_norm_integral_osc_smul_le_pow
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {f : ℝ^n → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcompact : HasCompactSupport f)
    (hne : ∀ x ∈ tsupport f, fderiv ℝ φ x ≠ 0) (k : ℕ) :
    ∃ C ≥ 0, ∀ ξ : ℝ, ξ ≠ 0 →
      ‖∫ x, osc ξ (φ x) • f x‖ ≤ C / |ξ| ^ k := by
  induction k generalizing f with
  | zero =>
    refine ⟨∫ x, ‖f x‖, integral_nonneg (fun x ↦ norm_nonneg _), ?_⟩
    intro ξ _
    simpa only [pow_zero, div_one, norm_smul, norm_osc_eq_one, one_mul] using
      norm_integral_le_integral_norm (fun x ↦ osc ξ (φ x) • f x)
  | succ k ih =>
    have hg := contDiff_transferAmplitude hφ hf hne
    have hgc : HasCompactSupport (transferAmplitude φ f) :=
      hcompact.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_transferAmplitude_subset φ f)
    have hgn : ∀ x ∈ tsupport (transferAmplitude φ f), fderiv ℝ φ x ≠ 0 :=
      fun x hx ↦ hne x (tsupport_transferAmplitude_subset φ f hx)
    obtain ⟨C, hC, hbound⟩ := ih hg hgc hgn
    refine ⟨C, hC, fun ξ hξ ↦ ?_⟩
    have hn := congrArg norm (integral_osc_smul_transferAmplitude hφ hf hcompact hne ξ)
    simp only [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, norm_neg] at hn
    calc
      ‖∫ x, osc ξ (φ x) • f x‖ =
          ‖∫ x, osc ξ (φ x) • transferAmplitude φ f x‖ / |ξ| :=
        (eq_div_iff (abs_ne_zero.mpr hξ)).mpr (by simpa only [mul_comm] using hn)
      _ ≤ (C / |ξ| ^ k) / |ξ| :=
        div_le_div_of_nonneg_right (hbound ξ hξ) (abs_nonneg ξ)
      _ = C / |ξ| ^ (k + 1) := by rw [div_div, pow_succ]

end PDE.Analysis.NonstationaryPhase
