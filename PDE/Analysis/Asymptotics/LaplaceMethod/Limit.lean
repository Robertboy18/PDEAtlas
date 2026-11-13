/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Asymptotics.LaplaceMethod
public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import CAS.ExactTactic

/-!
# Laplace asymptotics at a nondegenerate minimum

Taylor's theorem identifies the rescaled phase from its second derivative.
A quadratic lower bound supplies an integrable Gaussian majorant for a bounded
continuous amplitude. Dominated convergence then gives the leading asymptotic.

`tendsto_laplace_integral` is the one-dimensional absolute form of Evans's lemma
(Asymptotics) in §4.5.2: for a `C²` phase with `φ 0 = 0`, `φ' 0 = 0` and `δ y² ≤ φ y`, and a
bounded continuous amplitude, `∫ exp (-φ y / ε²) a y dy = ε √(2π / φ'' 0) a 0 + o(ε)`. Evans
proves the ratio limit (24) for a continuous phase by showing that the normalized weights (25)
concentrate at the minimum.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.2, the lemma (Asymptotics), (24)-(25), and its
  proof, p. 217. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Asymptotics

open Filter MeasureTheory Set
open scoped Topology

/-- A stationary C² phase has its quadratic Taylor limit after rescaling.
The coefficient is the second derivative at the stationary point. -/
theorem tendsto_rescaled_stationary_phase
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hzero : φ 0 = 0) (hstationary : deriv φ 0 = 0) (x : ℝ) :
    Tendsto (fun ε : ℝ ↦ φ (ε * x) / ε ^ 2)
      (𝓝[>] 0) (𝓝 (deriv (deriv φ) 0 / 2 * x ^ 2)) := by
  have ht := Real.taylor_tendsto (n := 2) (x₀ := 0) convex_univ (mem_univ 0)
    hφ.contDiffOn
  have hpoly (y : ℝ) :
      taylorWithinEval φ 2 univ 0 y = deriv (deriv φ) 0 / 2 * y ^ 2 := by
    rw [taylorWithinEval_succ φ 1, taylorWithinEval_succ φ 0]
    simp only [taylor_within_zero_eval, iteratedDerivWithin_univ,
      iteratedDeriv_succ, iteratedDeriv_zero, hzero, hstationary, smul_eq_mul]
    norm_num
    cas
  simp only [nhdsWithin_univ, sub_zero, hpoly] at ht
  have hx : Tendsto (fun ε : ℝ ↦ ε * x) (𝓝[>] 0) (𝓝 0) := by
    simpa using (show Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) from
      nhdsWithin_le_nhds).mul_const x
  have hr := (ht.comp hx).mul_const (x ^ 2)
  have hlim := hr.add_const (deriv (deriv φ) 0 / 2 * x ^ 2)
  simp only [zero_mul, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have he : ε ≠ 0 := ne_of_gt hε
  by_cases hx : x = 0
  · simp [hx, hzero]
  · simp only [Function.comp_apply]
    cas using [he, hx]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A quadratically coercive stationary phase and a bounded continuous amplitude
have the Gaussian leading limit. The normalization is written using the spatial
scale `ε`; the usual large parameter is `ε⁻²`. -/
theorem tendsto_laplace_integral
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hzero : φ 0 = 0) (hstationary : deriv φ 0 = 0)
    {δ : ℝ} (hδ : 0 < δ) (hlower : ∀ y, δ * y ^ 2 ≤ φ y)
    {a : ℝ → E} (ha : Continuous a) {M : ℝ} (hM : ∀ y, ‖a y‖ ≤ M) :
    Tendsto (fun ε : ℝ ↦ ε⁻¹ • ∫ y : ℝ, Real.exp (-φ y / ε ^ 2) • a y)
      (𝓝[>] 0) (𝓝 (√(Real.pi / (deriv (deriv φ) 0 / 2)) • a 0)) := by
  let c := deriv (deriv φ) 0 / 2
  let F (ε x : ℝ) := Real.exp (-φ (ε * x) / ε ^ 2) • a (ε * x)
  have hbound (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
      ‖F ε x‖ ≤ Real.exp (-δ * x ^ 2) * M := by
    have he : ε ^ 2 > 0 := sq_pos_of_pos hε
    have hscale : δ * x ^ 2 ≤ φ (ε * x) / ε ^ 2 := by
      apply (le_div_iff₀ he).mpr
      calc
        δ * x ^ 2 * ε ^ 2 = δ * (ε * x) ^ 2 := by cas
        _ ≤ φ (ε * x) := hlower _
    have hexp : Real.exp (-φ (ε * x) / ε ^ 2) ≤ Real.exp (-δ * x ^ 2) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div, neg_mul] using neg_le_neg hscale
    dsimp only [F]
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul hexp (hM _) (norm_nonneg _) (Real.exp_pos _).le
  have hlimit (x : ℝ) :
      Tendsto (fun ε ↦ F ε x) (𝓝[>] 0) (𝓝 (Real.exp (-c * x ^ 2) • a 0)) := by
    have hp := Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_rescaled_stationary_phase hφ hzero hstationary x).neg
    have hx : Tendsto (fun ε : ℝ ↦ ε * x) (𝓝[>] 0) (𝓝 0) := by
      simpa using (show Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) from
        nhdsWithin_le_nhds).mul_const x
    simpa only [F, c, neg_div, neg_mul, Function.comp_apply] using
      hp.smul (ha.continuousAt.tendsto.comp hx)
  have hint :
      Tendsto (fun ε : ℝ ↦ ∫ x, F ε x) (𝓝[>] 0)
        (𝓝 (∫ x : ℝ, Real.exp (-c * x ^ 2) • a 0)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun x : ℝ ↦ Real.exp (-δ * x ^ 2) * M)
    · apply Eventually.of_forall
      intro ε
      exact (((Real.continuous_exp.comp
        ((hφ.continuous.comp (continuous_const.mul continuous_id)).neg.div_const _)).smul
          (ha.comp (continuous_const.mul continuous_id)))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ae_of_all _ (hbound ε hε)
    · exact (integrable_exp_neg_mul_sq hδ).mul_const M
    · exact ae_of_all _ hlimit
  rw [integral_smul_const, integral_gaussian] at hint
  apply hint.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change (∫ x : ℝ, (fun y ↦ Real.exp (-φ y / ε ^ 2) • a y) (ε * x)) = _
  simpa only [abs_of_pos (inv_pos.mpr hε)] using!
    Measure.integral_comp_mul_left (fun y ↦ Real.exp (-φ y / ε ^ 2) • a y) ε

end PDE.Analysis.Asymptotics
