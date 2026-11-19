/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Asymptotics.OscillatoryIntegral
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Nonstationary phase on an interval

For a real phase `φ` with nonvanishing derivative, integration by parts transfers
a derivative to the amplitude divided by `φ'`. The resulting estimate retains
the boundary terms and applies to amplitudes in an arbitrary complex Banach space.

Evans, §4.5.3(b), handles a nonvanishing gradient by changing variables to make the phase
affine, Lemma 3(i), and integrating by parts, Lemma 1. In one dimension we integrate by parts
directly, using `hasDerivAt_osc_comp`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.3(b), Lemma 1, p. 221, and Lemma 3(i), p. 223.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis

open scoped Interval
open MeasureTheory intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [CompleteSpace E] [IsScalarTower ℝ ℂ E]

/-- The chain rule for an oscillation with a differentiable real phase. -/
theorem hasDerivAt_osc_comp {φ : ℝ → ℝ} {φ' t : ℝ} (ω : ℝ)
    (hφ : HasDerivAt φ φ' t) :
    HasDerivAt (fun s ↦ osc ω (φ s))
      (((ω : ℂ) * Complex.I * osc ω (φ t)) * φ') t := by
  simpa only [Function.comp_def, Complex.real_smul, mul_comm] using!
    (hasDerivAt_osc ω (φ t)).scomp t hφ

omit [IsScalarTower ℝ ℂ E] in
/-- Integration by parts for a nonlinear phase, with the derivative of the phase
absorbed into the amplitude. This form also permits zeros of the phase derivative. -/
theorem integral_osc_comp_smul_phase_deriv_eq
    {φ φ' : ℝ → ℝ} {g g' : ℝ → E} (ω a b : ℝ) (hω : ω ≠ 0)
    (hφ : ∀ t ∈ [[a, b]], HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' [[a, b]])
    (hg : ∀ t ∈ [[a, b]], HasDerivAt g (g' t) t)
    (hg' : IntervalIntegrable g' volume a b) :
    (∫ t in a..b, osc ω (φ t) • (φ' t • g t)) =
      (((ω : ℂ) * Complex.I)⁻¹) •
        (osc ω (φ b) • g b - osc ω (φ a) • g a -
          ∫ t in a..b, osc ω (φ t) • g' t) := by
  let c : ℂ := (ω : ℂ) * Complex.I
  have hc : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hω) Complex.I_ne_zero
  have hcont : ContinuousOn (fun t ↦ osc ω (φ t)) [[a, b]] :=
    (continuous_osc ω).comp_continuousOn
      (fun t ht ↦ (hφ t ht).continuousAt.continuousWithinAt)
  have hd : ∀ t ∈ [[a, b]], HasDerivAt (fun s ↦ osc ω (φ s))
      (c * osc ω (φ t) * φ' t) t := fun t ht ↦ hasDerivAt_osc_comp ω (hφ t ht)
  have hdi : IntervalIntegrable (fun t ↦ c * osc ω (φ t) * φ' t) volume a b :=
    ((continuousOn_const.mul hcont).mul
      (Complex.continuous_ofReal.comp_continuousOn hφ')).intervalIntegrable
  have hp := integral_smul_deriv_eq_deriv_smul hd hg hdi hg'
  have heq :
      (∫ t in a..b, (c * osc ω (φ t) * φ' t) • g t) =
        c • ∫ t in a..b, osc ω (φ t) • (φ' t • g t) := by
    rw [← intervalIntegral.integral_smul]
    apply integral_congr
    intro t _
    simp only [mul_smul, ← Complex.coe_algebraMap, algebraMap_smul]
  rw [heq] at hp
  have hi :
      c • (∫ t in a..b, osc ω (φ t) • (φ' t • g t)) =
        osc ω (φ b) • g b - osc ω (φ a) • g a -
          ∫ t in a..b, osc ω (φ t) • g' t := by
    rw [hp]
    abel
  rw [← hi, inv_smul_smul₀ hc]

omit [IsScalarTower ℝ ℂ E] in
/-- A nonlinear phase gains one inverse power of frequency when its normalized
amplitude and the derivative of that amplitude are bounded. -/
theorem norm_integral_osc_comp_smul_phase_deriv_le
    {φ φ' : ℝ → ℝ} {g g' : ℝ → E} (ω a b : ℝ) (hω : ω ≠ 0)
    (hφ : ∀ t ∈ [[a, b]], HasDerivAt φ (φ' t) t)
    (hφ' : ContinuousOn φ' [[a, b]])
    (hg : ∀ t ∈ [[a, b]], HasDerivAt g (g' t) t)
    (hg' : IntervalIntegrable g' volume a b)
    (M M' : ℝ) (hM : ∀ t ∈ [[a, b]], ‖g t‖ ≤ M)
    (hM' : ∀ t ∈ [[a, b]], ‖g' t‖ ≤ M') :
    ‖∫ t in a..b, osc ω (φ t) • (φ' t • g t)‖ ≤
      (2 * M + |b - a| * M') / |ω| := by
  rw [integral_osc_comp_smul_phase_deriv_eq ω a b hω hφ hφ' hg hg', norm_smul]
  have hn : ‖((ω : ℂ) * Complex.I)⁻¹‖ = |ω|⁻¹ := by simp
  rw [hn, ← div_eq_inv_mul]
  apply div_le_div_of_nonneg_right _ (abs_nonneg ω)
  have hi : ‖∫ t in a..b, osc ω (φ t) • g' t‖ ≤ M' * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    simpa only [norm_smul, norm_osc_eq_one, one_mul] using
      hM' t (Set.uIoc_subset_uIcc ht)
  calc
    ‖osc ω (φ b) • g b - osc ω (φ a) • g a -
        ∫ t in a..b, osc ω (φ t) • g' t‖
      ≤ ‖osc ω (φ b) • g b‖ + ‖osc ω (φ a) • g a‖ +
          ‖∫ t in a..b, osc ω (φ t) • g' t‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ M + M + M' * |b - a| := by
      simp only [norm_smul, norm_osc_eq_one, one_mul]
      exact add_le_add (add_le_add (hM b (by simp)) (hM a (by simp))) hi
    _ = 2 * M + |b - a| * M' := by ring

omit [IsScalarTower ℝ ℂ E] [CompleteSpace E] in
/-- The one-dimensional nonstationary-phase estimate for a twice differentiable
phase and a differentiable Banach-valued amplitude. The lower bound on `|φ'|`
controls division by the phase derivative; `K` bounds the curvature of the phase. If `E` is
not complete, the integral is `0` and the bound is nonnegative. -/
theorem norm_integral_osc_comp_smul_le
    {φ φ' φ'' : ℝ → ℝ} {f f' : ℝ → E} (ω a b : ℝ) (hω : ω ≠ 0)
    (hφ : ∀ t ∈ [[a, b]], HasDerivAt φ (φ' t) t)
    (hφ' : ∀ t ∈ [[a, b]], HasDerivAt φ' (φ'' t) t)
    (hφ'' : ContinuousOn φ'' [[a, b]])
    (hf : ∀ t ∈ [[a, b]], HasDerivAt f (f' t) t)
    (hf' : ContinuousOn f' [[a, b]])
    (δ M M' K : ℝ) (hδ : 0 < δ)
    (hphase : ∀ t ∈ [[a, b]], δ ≤ |φ' t|)
    (hM : ∀ t ∈ [[a, b]], ‖f t‖ ≤ M)
    (hM' : ∀ t ∈ [[a, b]], ‖f' t‖ ≤ M')
    (hK : ∀ t ∈ [[a, b]], |φ'' t| ≤ K) :
    ‖∫ t in a..b, osc ω (φ t) • f t‖ ≤
      (2 * (M / δ) + |b - a| * (M' / δ + K / δ ^ 2 * M)) / |ω| := by
  rcases em (CompleteSpace E) with hE | hE
  swap
  · have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a Set.left_mem_uIcc)
    have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' a Set.left_mem_uIcc)
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a Set.left_mem_uIcc)
    rw [intervalIntegral, integral_of_not_completeSpace hE, integral_of_not_completeSpace hE,
      sub_zero, norm_zero]
    positivity
  have hne (t : ℝ) (ht : t ∈ [[a, b]]) : φ' t ≠ 0 :=
    abs_pos.mp (hδ.trans_le (hphase t ht))
  have hpc : ContinuousOn φ' [[a, b]] :=
    fun t ht ↦ (hφ' t ht).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f [[a, b]] :=
    fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt
  let g : ℝ → E := fun t ↦ (φ' t)⁻¹ • f t
  let g' : ℝ → E :=
    fun t ↦ (φ' t)⁻¹ • f' t + (-φ'' t / (φ' t) ^ 2) • f t
  have hg : ∀ t ∈ [[a, b]], HasDerivAt g (g' t) t :=
    fun t ht ↦ ((hφ' t ht).inv (hne t ht)).smul (hf t ht)
  have hgc : ContinuousOn g' [[a, b]] :=
    ((hpc.inv₀ hne).smul hf').add
      ((hφ''.neg.div (hpc.pow 2) (fun t ht ↦ pow_ne_zero 2 (hne t ht))).smul hfc)
  have hinv (t : ℝ) (ht : t ∈ [[a, b]]) : |(φ' t)⁻¹| ≤ δ⁻¹ := by
    rw [abs_inv]
    exact inv_anti₀ hδ (hphase t ht)
  have hgb : ∀ t ∈ [[a, b]], ‖g t‖ ≤ M / δ := by
    intro t ht
    calc
      ‖g t‖ = |(φ' t)⁻¹| * ‖f t‖ := norm_smul _ _
      _ ≤ δ⁻¹ * M := mul_le_mul (hinv t ht) (hM t ht) (norm_nonneg _) (by positivity)
      _ = M / δ := (div_eq_inv_mul _ _).symm
  have hgb' : ∀ t ∈ [[a, b]], ‖g' t‖ ≤ M' / δ + K / δ ^ 2 * M := by
    intro t ht
    have hs : δ ^ 2 ≤ (φ' t) ^ 2 := by
      calc
        δ ^ 2 ≤ |φ' t| ^ 2 := pow_le_pow_left₀ hδ.le (hphase t ht) 2
        _ = (φ' t) ^ 2 := sq_abs _
    have hquot : |-φ'' t / (φ' t) ^ 2| ≤ K / δ ^ 2 := by
      rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg (φ' t))]
      exact div_le_div₀ ((abs_nonneg _).trans (hK t ht)) (hK t ht)
        (sq_pos_of_pos hδ) hs
    calc
      ‖g' t‖ ≤ ‖(φ' t)⁻¹ • f' t‖ + ‖(-φ'' t / (φ' t) ^ 2) • f t‖ :=
        norm_add_le _ _
      _ = |(φ' t)⁻¹| * ‖f' t‖ + |-φ'' t / (φ' t) ^ 2| * ‖f t‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ δ⁻¹ * M' + K / δ ^ 2 * M :=
        add_le_add
          (mul_le_mul (hinv t ht) (hM' t ht) (norm_nonneg _) (by positivity))
          (mul_le_mul hquot (hM t ht) (norm_nonneg _)
            (div_nonneg ((abs_nonneg _).trans (hK t ht)) (sq_nonneg _)))
      _ = M' / δ + K / δ ^ 2 * M := by rw [div_eq_inv_mul M' δ]
  have hi := norm_integral_osc_comp_smul_phase_deriv_le ω a b hω hφ hpc hg
    hgc.intervalIntegrable (M / δ) (M' / δ + K / δ ^ 2 * M) hgb hgb'
  have heq :
      (∫ t in a..b, osc ω (φ t) • (φ' t • g t)) =
        ∫ t in a..b, osc ω (φ t) • f t := by
    apply integral_congr
    intro t ht
    change osc ω (φ t) • (φ' t • g t) = osc ω (φ t) • f t
    rw [show φ' t • g t = f t from smul_inv_smul₀ (hne t ht) (f t)]
  rwa [heq] at hi

end PDE.Analysis
