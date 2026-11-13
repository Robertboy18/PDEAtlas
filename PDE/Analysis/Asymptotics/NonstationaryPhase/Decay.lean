/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Asymptotics.NonstationaryPhase
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Rapid decay for a smooth nonstationary phase

For a smooth real phase with nowhere vanishing derivative and a smooth amplitude
supported inside an interval, each integration by parts gains another inverse power
of frequency. The transferred amplitude is the derivative of `f / φ'`; its support
stays inside the original support, so every boundary term vanishes.

This is the one-dimensional case, for a phase without critical points, of the bound
`O(ε^m)` in Evans's stationary phase method, §4.5.3(b), with frequency `ξ = 1 / ε`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), Lemma 1, p. 221, and the stationary phase
  method, p. 226. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis

open scoped ContDiff Interval
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [CompleteSpace E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
/-- A smooth amplitude supported inside an interval has arbitrarily high
inverse-frequency decay against a smooth phase whose derivative never vanishes.
The constant may depend on the phase, amplitude, interval, and requested order. -/
theorem exists_norm_integral_osc_comp_smul_le_pow
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφ' : ∀ t, deriv φ t ≠ 0) (a b : ℝ) (k : ℕ)
    {f : ℝ → E} (hf : ContDiff ℝ ∞ f) (hs : tsupport f ⊆ Set.Ioo a b) :
    ∃ C ≥ 0, ∀ ξ : ℝ, ξ ≠ 0 →
      ‖∫ t in a..b, osc ξ (φ t) • f t‖ ≤ C / |ξ| ^ k := by
  induction k generalizing f with
  | zero =>
    obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn hf.continuous.continuousOn
    refine ⟨max M 0 * |b - a|, mul_nonneg (le_max_right _ _) (abs_nonneg _), ?_⟩
    intro ξ _
    simp only [pow_zero, div_one]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    simpa only [norm_smul, norm_osc_eq_one, one_mul] using
      (hM t (Set.uIoc_subset_uIcc ht)).trans (le_max_left M 0)
  | succ k ih =>
    have hpd : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    let g : ℝ → E := fun t ↦ (deriv φ t)⁻¹ • f t
    have hg : ContDiff ℝ ∞ g := (hpd.inv hφ').smul hf
    have hgd : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
    have hgs : tsupport g ⊆ Set.Ioo a b :=
      (tsupport_smul_subset_right _ _).trans hs
    obtain ⟨C, hC, hbound⟩ := ih hgd (tsupport_deriv_subset.trans hgs)
    refine ⟨C, hC, fun ξ hξ ↦ ?_⟩
    have ha : g a = 0 := image_eq_zero_of_notMem_tsupport (fun ht ↦ (hgs ht).1.false)
    have hb : g b = 0 := image_eq_zero_of_notMem_tsupport (fun ht ↦ (hgs ht).2.false)
    have hid := integral_osc_comp_smul_phase_deriv_eq ξ a b hξ
      (fun t _ ↦ (hφ.differentiable (by simp) t).hasDerivAt)
      hpd.continuous.continuousOn
      (fun t _ ↦ (hg.differentiable (by simp) t).hasDerivAt)
      (hgd.continuous.intervalIntegrable a b)
    have heq :
        (∫ t in a..b, osc ξ (φ t) • (deriv φ t • g t)) =
          ∫ t in a..b, osc ξ (φ t) • f t := by
      apply intervalIntegral.integral_congr
      intro t _
      change osc ξ (φ t) • (deriv φ t • g t) = osc ξ (φ t) • f t
      rw [show deriv φ t • g t = f t from smul_inv_smul₀ (hφ' t) (f t)]
    rw [heq, ha, hb] at hid
    have hn :
        ‖∫ t in a..b, osc ξ (φ t) • f t‖ =
          ‖∫ t in a..b, osc ξ (φ t) • deriv g t‖ / |ξ| := by
      rw [hid]
      simp [norm_smul, div_eq_inv_mul]
    rw [hn, pow_succ, ← div_div]
    exact div_le_div_of_nonneg_right (hbound ξ hξ) (abs_nonneg _)

end PDE.Analysis
