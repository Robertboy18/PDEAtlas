/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LineDeriv.Continuous
public import PDE.Analysis.MeasureTheory.Lp.IntegralDerivative
public import PDE.Analysis.MeasureTheory.Lp.PowerGrowthContinuity
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Integral potentials with conjugate derivative growth

A scalar potential of `p`-growth, with continuous derivative of `(p - 1)`-growth,
defines a strictly Fréchet differentiable functional on `Lᵖ` for `1 < p < ∞`.
Its derivative is Mathlib's integral pairing with the actual superposition
operator in the conjugate space. The finite measure allows constant offsets in
both growth bounds.

The proof reuses differentiation along `Lᵖ` lines and the continuous line-derivative
criterion. It does not require that the derivative take values in `L²`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  {p q : ℝ≥0∞} [ENNReal.HolderConjugate p q]
  {G g : ℝ → ℝ} {A B C : ℝ}

/-- A continuous scalar map of conjugate power growth sends `Lᵖ` to `Lᵠ`.
The constant offset is allowed on a finite measure space. For `p = ∞` the growth bound makes
`g` bounded. -/
theorem memLp_comp_of_conjugate_growth
    (hc : Continuous g)
    (hg : ∀ s, |g s| ≤ C * (1 + |s| ^ (p.toReal - 1)))
    (u : Lp ℝ p μ) : MemLp (fun x ↦ g (u x)) q μ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · obtain ⟨K, hK⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hc.continuousOn
    have hbound : ∀ s, |g s| ≤ max K (2 * C) := by
      intro s
      rcases le_or_gt |s| 1 with hs | hs
      · simpa only [Real.norm_eq_abs] using (hK s (abs_le.mp hs)).trans (le_max_left _ _)
      · have h1 : |s| ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hs.le (by norm_num)
        have h0 : 0 ≤ |s| ^ (-1 : ℝ) := Real.rpow_nonneg (abs_nonneg s) _
        have hgs := hg s
        simp only [ENNReal.toReal_top, zero_sub] at hgs
        have hC : 0 ≤ C := by nlinarith [abs_nonneg (g s)]
        exact hgs.trans ((by nlinarith : C * (1 + |s| ^ (-1 : ℝ)) ≤ 2 * C).trans
          (le_max_right _ _))
    exact MemLp.of_bound (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u))
      (max K (2 * C)) (ae_of_all μ fun x ↦ by simpa only [Real.norm_eq_abs] using hbound (u x))
  apply (Lp.memLp u).comp_of_norm_rpow_sub_one_le hp_top (a := fun _ ↦ g)
    (hc.measurable.comp measurable_snd) (memLp_const C)
  exact ae_of_all μ fun _ s ↦ by simpa [Real.norm_eq_abs, mul_add] using hg s

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The strict derivative of an integral potential is the actual `Lᵠ`–`Lᵖ`
pairing with its continuous derivative. Both constants at zero are unrestricted. -/
theorem hasStrictFDerivAt_integral_Lp_of_deriv_growth
    (hp : 1 < p) (hp_top : p ≠ ∞)
    (hd : ∀ s, HasDerivAt G (g s) s) (hc : Continuous g)
    (hG : ∀ s, |G s| ≤ A + B * |s| ^ p.toReal)
    (hg : ∀ s, |g s| ≤ C * (1 + |s| ^ (p.toReal - 1)))
    (u : Lp ℝ p μ) :
    HasStrictFDerivAt (fun w : Lp ℝ p μ ↦ ∫ x, G (w x) ∂μ)
      ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p
        (Lp.superposition (fun _ ↦ g)
          (memLp_comp_of_conjugate_growth hc hg) u)) u := by
  let N := Lp.superposition (fun _ : α ↦ g)
    (memLp_comp_of_conjugate_growth (μ := μ) (q := q) hc hg)
  have hN : Continuous N := by
    exact Lp.continuous_superposition_of_conjugate_growth hp hp_top (G := fun _ : α ↦ g)
      (hc.measurable.comp measurable_snd) (ae_of_all μ fun _ ↦ hc) (memLp_const C)
      (ae_of_all μ fun _ s ↦ by simpa [Real.norm_eq_abs, mul_add] using hg s)
  let P := (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p
  apply PDE.hasStrictFDerivAt_of_hasLineDerivAt_of_continuousAt
    (D := fun w ↦ P (N w)) _ (P.continuous.comp hN).continuousAt
  intro w v
  have hcont : Continuous G := continuous_iff_continuousAt.mpr fun s ↦ (hd s).continuousAt
  have hbase : Integrable (fun x ↦ G (w x)) μ := by
    apply (Lp.memLp w).integrable_comp_of_norm_rpow_le
      (ne_of_gt (zero_lt_one.trans hp)) hp_top (G := fun _ ↦ G)
      (hcont.measurable.comp measurable_snd) (integrable_const A)
    exact ae_of_all μ fun _ s ↦ by simpa only [Real.norm_eq_abs] using hG s
  let dF : α → ℝ → ℝ →L[ℝ] ℝ :=
    fun _ s ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (g s)
  have hdF : Measurable (fun z : α × ℝ × ℝ ↦ dF z.1 z.2.1 z.2.2) := by
    simpa [dF, Pi.mul_def, Function.comp_def] using
      measurable_snd.snd.mul (hc.measurable.comp measurable_snd.fst)
  have hgrowth : ∀ᵐ x ∂μ, ∀ s, ‖dF x s‖ ≤ C + C * ‖s‖ ^ (p.toReal - 1) := by
    apply ae_of_all
    intro x s
    simp only [dF, ContinuousLinearMap.norm_smulRight_apply, norm_one, one_mul,
      Real.norm_eq_abs]
    simpa only [mul_add, mul_one] using hg s
  have hderiv := ((Lp.memLp w).hasDerivAt_integral_of_deriv_growth (Lp.memLp v)
    (q := q) hp_top (F := fun _ ↦ G) (dF := dF)
    (hcont.measurable.comp measurable_snd) hdF
    (ae_of_all μ fun _ s ↦ (hd s).hasFDerivAt)
    (memLp_const C) hgrowth hbase).2.2
  change HasDerivAt (fun t : ℝ ↦ ∫ x, G ((w + t • v) x) ∂μ) (P (N w) v) 0
  convert hderiv using 1
  · ext t
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add w (t • v), Lp.coeFn_smul t v] with x ha hs
    simp only [ha, Pi.add_apply, hs, Pi.smul_apply]
  · rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_superposition (fun _ : α ↦ g)
      (memLp_comp_of_conjugate_growth (μ := μ) (q := q) hc hg) w] with x hx
    simp only [N] at *
    simp [dF, hx, ContinuousLinearMap.mul_apply', mul_comm]

include q in
/-- Conjugate derivative growth makes the integral potential `C¹` on `Lᵖ`. -/
theorem contDiff_integral_Lp_of_deriv_growth
    (hp : 1 < p) (hp_top : p ≠ ∞)
    (hd : ∀ s, HasDerivAt G (g s) s) (hc : Continuous g)
    (hG : ∀ s, |G s| ≤ A + B * |s| ^ p.toReal)
    (hg : ∀ s, |g s| ≤ C * (1 + |s| ^ (p.toReal - 1))) :
    ContDiff ℝ 1 (fun w : Lp ℝ p μ ↦ ∫ x, G (w x) ∂μ) := by
  let N := Lp.superposition (fun _ : α ↦ g)
    (memLp_comp_of_conjugate_growth (μ := μ) (q := q) hc hg)
  have hN : Continuous N :=
    Lp.continuous_superposition_of_conjugate_growth hp hp_top (G := fun _ : α ↦ g)
      (hc.measurable.comp measurable_snd) (ae_of_all μ fun _ ↦ hc) (memLp_const C)
      (ae_of_all μ fun _ s ↦ by simpa [Real.norm_eq_abs, mul_add] using hg s)
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨_, ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p).continuous.comp hN,
      fun w ↦ (hasStrictFDerivAt_integral_Lp_of_deriv_growth
        hp hp_top hd hc hG hg w).hasFDerivAt⟩

end MeasureTheory
