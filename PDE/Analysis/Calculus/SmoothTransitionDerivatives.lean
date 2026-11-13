/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivatives and endpoint flatness of the exponential transition

The formulas keep the small transition factor visible. This permits
quantitative bounds near zero without replacing that factor by zero.

## Main definitions

* `smoothTransitionRate`: the rate `1/t² + 1/(1 - t)²` in the first derivative formula.

## Main results

* `smoothTransition_eq_inv_one_add_exp`: `σ(t) = (1 + exp(1/t - 1/(1 - t)))⁻¹` on `(0, 1)`, for
  `σ = Real.smoothTransition`.
* `deriv_smoothTransition`: `σ' = σ (1 - σ) (1/t² + 1/(1 - t)²)` on `(0, 1)`.
* `deriv_deriv_smoothTransition`: the second derivative on `(0, 1)` as `σ (1 - σ)` times an
  explicit factor.
* `iteratedDeriv_smoothTransition_zero`: every derivative of `σ` vanishes at `0`.
-/

@[expose] public noncomputable section

open scoped Topology

namespace PDE.Analysis

/-- The exponential formula on the open transition interval. -/
theorem smoothTransition_eq_inv_one_add_exp {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    Real.smoothTransition t = (1 + Real.exp (1 / t - 1 / (1 - t)))⁻¹ := by
  have hgap : 0 < 1 - t := sub_pos.mpr ht₁
  have hexp : Real.exp (-1 / (1 - t)) =
      Real.exp (-1 / t) * Real.exp (1 / t - 1 / (1 - t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Real.smoothTransition, expNegInvGlue, not_le.mpr ht,
    not_le.mpr hgap, ite_false]
  simp only [neg_div, one_div] at hexp
  rw [hexp]
  have hden : 1 + Real.exp (1 / t - 1 / (1 - t)) ≠ 0 := by positivity
  field_simp [Real.exp_ne_zero, hden]

/-- The positive logarithmic rate in the first derivative formula. -/
def smoothTransitionRate (t : ℝ) : ℝ :=
  1 / t ^ 2 + 1 / (1 - t) ^ 2

/-- The derivative of the rate retains the two endpoint singularities. -/
theorem hasDerivAt_smoothTransitionRate {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    HasDerivAt smoothTransitionRate (-2 / t ^ 3 + 2 / (1 - t) ^ 3) t := by
  have hgap : 1 - t ≠ 0 := (sub_pos.mpr ht₁).ne'
  convert (((hasDerivAt_id t).pow 2).inv (pow_ne_zero 2 ht.ne')).add
    ((((hasDerivAt_const t 1).sub (hasDerivAt_id t)).pow 2).inv
      (pow_ne_zero 2 hgap)) using 1
  · funext s
    simp [smoothTransitionRate, one_div]
  · simp only [Pi.pow_apply, Pi.sub_apply, id_eq]
    field_simp [ht.ne', hgap]
    ring

/-- The first derivative has an explicit small transition factor. -/
theorem hasDerivAt_smoothTransition {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    HasDerivAt Real.smoothTransition
      (Real.smoothTransition t * (1 - Real.smoothTransition t) * smoothTransitionRate t) t := by
  have hgap : 1 - t ≠ 0 := (sub_pos.mpr ht₁).ne'
  have hexponent := ((hasDerivAt_id t).inv ht.ne').sub
    (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).inv hgap)
  have hden : 1 + Real.exp (t⁻¹ - (1 - t)⁻¹) ≠ 0 := by positivity
  have hd := (hexponent.exp.const_add 1).inv hden
  have heq : Real.smoothTransition =ᶠ[𝓝 t]
      fun s ↦ (1 + Real.exp (s⁻¹ - (1 - s)⁻¹))⁻¹ := by
    filter_upwards [eventually_gt_nhds ht, eventually_lt_nhds ht₁] with s hs hs₁
    simpa only [one_div] using smoothTransition_eq_inv_one_add_exp hs hs₁
  convert hd.congr_of_eventuallyEq heq using 1
  rw [smoothTransition_eq_inv_one_add_exp ht ht₁]
  simp only [smoothTransitionRate, one_div, Pi.sub_apply, Pi.inv_apply, id_eq]
  field_simp
  ring

/-- Pointwise first derivative on the open transition interval. -/
theorem deriv_smoothTransition {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    deriv Real.smoothTransition t =
      Real.smoothTransition t * (1 - Real.smoothTransition t) * smoothTransitionRate t :=
  (hasDerivAt_smoothTransition ht ht₁).deriv

/-- The second derivative preserves the same small transition factor. -/
theorem hasDerivAt_deriv_smoothTransition {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    HasDerivAt (deriv Real.smoothTransition)
      (Real.smoothTransition t * (1 - Real.smoothTransition t) *
        ((1 - 2 * Real.smoothTransition t) * smoothTransitionRate t ^ 2 +
          (-2 / t ^ 3 + 2 / (1 - t) ^ 3))) t := by
  have hχ := hasDerivAt_smoothTransition ht ht₁
  have hd := (hχ.mul ((hasDerivAt_const t 1).sub hχ)).mul
    (hasDerivAt_smoothTransitionRate ht ht₁)
  have heq : deriv Real.smoothTransition =ᶠ[𝓝 t] fun s ↦
      Real.smoothTransition s * (1 - Real.smoothTransition s) * smoothTransitionRate s := by
    filter_upwards [eventually_gt_nhds ht, eventually_lt_nhds ht₁] with s hs hs₁
    exact deriv_smoothTransition hs hs₁
  convert hd.congr_of_eventuallyEq heq using 1
  simp only [Pi.sub_apply, Pi.mul_apply]
  ring

/-- Pointwise second derivative on the open transition interval. -/
theorem deriv_deriv_smoothTransition {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    deriv (deriv Real.smoothTransition) t =
      Real.smoothTransition t * (1 - Real.smoothTransition t) *
        ((1 - 2 * Real.smoothTransition t) * smoothTransitionRate t ^ 2 +
          (-2 / t ^ 3 + 2 / (1 - t) ^ 3)) :=
  (hasDerivAt_deriv_smoothTransition ht ht₁).deriv

/-- Every derivative vanishes at the flat endpoint, including the value. -/
theorem iteratedDeriv_smoothTransition_zero (n : ℕ) :
    iteratedDeriv n Real.smoothTransition 0 = 0 := by
  have hf : ContDiff ℝ n Real.smoothTransition := Real.smoothTransition.contDiff
  have hz : ContDiff ℝ n (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
  have heq : Set.EqOn Real.smoothTransition (fun _ ↦ 0) (Set.Iio 0) :=
    fun _ ht ↦ Real.smoothTransition.zero_of_nonpos ht.le
  have hd := heq.iteratedDeriv_of_isOpen isOpen_Iio n
  have hc := hd.closure (hf.continuous_iteratedDeriv n le_rfl)
    (hz.continuous_iteratedDeriv n le_rfl)
  simpa using hc (show (0 : ℝ) ∈ closure (Set.Iio 0) by simp)

/-- The derivative of `Real.smoothTransition` vanishes outside `[0, 1]`, so it has compact
support. -/
theorem hasCompactSupport_deriv_smoothTransition :
    HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro (K := Set.Icc (0 : ℝ) 1) isCompact_Icc
  intro x hx
  by_cases hx0 : 0 ≤ x
  · have hx1 : 1 < x := lt_of_not_ge (fun hx1 ↦ hx ⟨hx0, hx1⟩)
    have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [eventually_gt_nhds hx1] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    exact ((hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq heq).deriv
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds (lt_of_not_ge hx0)] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq).deriv

/-- `Real.smoothTransition` has a finite Lipschitz constant. -/
theorem exists_lipschitzWith_smoothTransition :
    ∃ C : NNReal, LipschitzWith C Real.smoothTransition := by
  obtain ⟨C, hC⟩ := (Real.smoothTransition.contDiff (n := 1)).contDiffOn
    |>.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1) isCompact_Icc
  refine ⟨C, ?_⟩
  have h := hC.to_restrict.comp (LipschitzWith.projIcc (a := 0) (b := 1) zero_le_one)
  simpa only [mul_one, Function.comp_def, Set.domRestrict_apply,
    Real.smoothTransition.projIcc] using h

end PDE.Analysis
