/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2WeightedRules
import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2CosineRule

/-!
# The split rule in `β` at a fixed `θ`

The exact quadrant rules of `TrigPoly2WeightedRules` integrate in `β` first, at every fixed `θ`:
for families `p`, `q` with componentwise equal parities about `0` and `π/2` in `β`, the section
`β ↦ ∑_c p_c q_c (β, θ)` is an even cosine series, integrated over `[0, π/2]` by the trapezoid
rule (`integral_sum_mul_eq_trapezoid`), and `cos β` times it by the sine rule at the reversed
nodes (`integral_cos_mul_sum_mul_eq_rule`). For `r = p + μ g` with `g = cos β · w` this gives the
split rule of `∫₀^{π/2} ∑_c r_c r'_c dβ` at every `θ` (`integral_sum_split_eq_rule`): the integral
of a sum of squares, so the node sums of the split rule are nonnegative at every `θ` when
`r = r'`, whatever weights in `θ` they are later summed with.
-/

@[expose] public section

namespace PDE.Analysis.TrigPoly2

open CAS.Analysis
open Finset

variable {Mβ Mθ Nβ Nθ Lβ Lθ : ℕ} {R : Type} [Field R] [Algebra R ℝ]

/-- **Trapezoid rule at a fixed `θ`.** -/
theorem integral_sum_mul_eq_trapezoid {ι : Type*} (s : Finset ι) (p : ι → TrigPoly2 Mβ Mθ R)
    (q : ι → TrigPoly2 Nβ Nθ R) {N : ℕ} (hN : (Mβ + Nβ) / 2 < 2 * N)
    (hβ0 : ∀ c ∈ s, ∃ e, ParityAtβ 0 e (p c) ∧ ParityAtβ 0 e (q c))
    (hβπ : ∀ c ∈ s, ∃ e, ParityAtβ (Real.pi / 2) e (p c) ∧ ParityAtβ (Real.pi / 2) e (q c))
    (θ : ℝ) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∑ c ∈ s, (p c).eval β θ * (q c).eval β θ =
      ∑ j : Fin (N + 1), quarterTrapezoidWeight N j *
        ∑ c ∈ s, (p c).eval (j * Real.pi / (2 * N)) θ * (q c).eval (j * Real.pi / (2 * N)) θ := by
  have hf : IsEvenCosineSeries ((Mβ + Nβ) / 2)
      fun β ↦ ∑ c ∈ s, ((p c).mul (q c)).eval β θ :=
    IsEvenCosineSeries.sum s fun c hc ↦ isEvenCosineSeries_β
      (isEvenAtβ_mul_of_parity (hβ0 c hc)) (isEvenAtβ_mul_of_parity (hβπ c hc)) θ
  simpa only [eval_mul] using hf.integral_eq_trapezoid hN

/-- **Sine rule at the reversed nodes at a fixed `θ`**, for the products with the weight
`cos β`. -/
theorem integral_cos_mul_sum_mul_eq_rule {ι : Type*} (s : Finset ι) (p : ι → TrigPoly2 Mβ Mθ R)
    (q : ι → TrigPoly2 Nβ Nθ R) {N : ℕ} (hN0 : 0 < N) (hN : (Mβ + Nβ) / 2 ≤ N)
    (hβ0 : ∀ c ∈ s, ∃ e, ParityAtβ 0 e (p c) ∧ ParityAtβ 0 e (q c))
    (hβπ : ∀ c ∈ s, ∃ e, ParityAtβ (Real.pi / 2) e (p c) ∧ ParityAtβ (Real.pi / 2) e (q c))
    (θ : ℝ) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), Real.cos β * ∑ c ∈ s, (p c).eval β θ * (q c).eval β θ =
      ∑ j : Fin (N + 1), quarterSinWeight N j *
        ∑ c ∈ s, (p c).eval (Real.pi / 2 - j * Real.pi / (2 * N)) θ *
          (q c).eval (Real.pi / 2 - j * Real.pi / (2 * N)) θ := by
  have hf : IsEvenCosineSeries ((Mβ + Nβ) / 2)
      fun β ↦ ∑ c ∈ s, ((p c).mul (q c)).eval β θ :=
    IsEvenCosineSeries.sum s fun c hc ↦ isEvenCosineSeries_β
      (isEvenAtβ_mul_of_parity (hβ0 c hc)) (isEvenAtβ_mul_of_parity (hβπ c hc)) θ
  have h := hf.integral_mul_cos_eq_rule hN0 hN
  simp only [eval_mul] at h
  rw [← h]
  exact intervalIntegral.integral_congr fun β _ ↦ mul_comm _ _

/-- **Split rule at a fixed `θ`.** For `r_c = p_c + μ g_c` and `r'_c = p'_c + μ g'_c` with
`g = cos β · w`, `g' = cos β · w'`, the integral over `β ∈ [0, π/2]` of `∑_c r_c r'_c` is the
trapezoid sums of `∑ p p'` and of `μ² ∑ g g'` plus `μ` times the sine sums at the reversed nodes
of `∑ p w'` and `∑ w p'`. -/
theorem integral_sum_split_eq_rule {ι : Type*} (s : Finset ι) (p p' : ι → TrigPoly2 Mβ Mθ R)
    (g g' : ι → TrigPoly2 Nβ Nθ R) (w w' : ι → TrigPoly2 Lβ Lθ R)
    (hg : ∀ c ∈ s, ∀ β θ, (g c).eval β θ = Real.cos β * (w c).eval β θ)
    (hg' : ∀ c ∈ s, ∀ β θ, (g' c).eval β θ = Real.cos β * (w' c).eval β θ)
    {N : ℕ} (hN0 : 0 < N) (hNp : (Mβ + Mβ) / 2 < 2 * N) (hNg : (Nβ + Nβ) / 2 < 2 * N)
    (hNm : (Mβ + Lβ) / 2 ≤ N)
    (hp0 : ∀ c ∈ s, ∃ e, ParityAtβ 0 e (p c) ∧ ParityAtβ 0 e (p' c))
    (hpπ : ∀ c ∈ s, ∃ e, ParityAtβ (Real.pi / 2) e (p c) ∧ ParityAtβ (Real.pi / 2) e (p' c))
    (hg0 : ∀ c ∈ s, ∃ e, ParityAtβ 0 e (g c) ∧ ParityAtβ 0 e (g' c))
    (hgπ : ∀ c ∈ s, ∃ e, ParityAtβ (Real.pi / 2) e (g c) ∧ ParityAtβ (Real.pi / 2) e (g' c))
    (hm0 : ∀ c ∈ s, ∃ e, ParityAtβ 0 e (p c) ∧ ParityAtβ 0 e (w' c))
    (hmπ : ∀ c ∈ s, ∃ e, ParityAtβ (Real.pi / 2) e (p c) ∧ ParityAtβ (Real.pi / 2) e (w' c))
    (hm0' : ∀ c ∈ s, ∃ e, ParityAtβ 0 e (p' c) ∧ ParityAtβ 0 e (w c))
    (hmπ' : ∀ c ∈ s, ∃ e, ParityAtβ (Real.pi / 2) e (p' c) ∧ ParityAtβ (Real.pi / 2) e (w c))
    (μ θ : ℝ) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∑ c ∈ s, ((p c).eval β θ + μ * (g c).eval β θ) *
        ((p' c).eval β θ + μ * (g' c).eval β θ) =
      ∑ j : Fin (N + 1), quarterTrapezoidWeight N j *
          ∑ c ∈ s, (p c).eval (j * Real.pi / (2 * N)) θ * (p' c).eval (j * Real.pi / (2 * N)) θ +
        μ ^ 2 * ∑ j : Fin (N + 1), quarterTrapezoidWeight N j *
          ∑ c ∈ s, (g c).eval (j * Real.pi / (2 * N)) θ * (g' c).eval (j * Real.pi / (2 * N)) θ +
        μ * (∑ j : Fin (N + 1), quarterSinWeight N j *
            ∑ c ∈ s, (p c).eval (Real.pi / 2 - j * Real.pi / (2 * N)) θ *
              (w' c).eval (Real.pi / 2 - j * Real.pi / (2 * N)) θ +
          ∑ j : Fin (N + 1), quarterSinWeight N j *
            ∑ c ∈ s, (p' c).eval (Real.pi / 2 - j * Real.pi / (2 * N)) θ *
              (w c).eval (Real.pi / 2 - j * Real.pi / (2 * N)) θ) := by
  have hpt : ∀ β, ∑ c ∈ s, ((p c).eval β θ + μ * (g c).eval β θ) *
      ((p' c).eval β θ + μ * (g' c).eval β θ) =
      ∑ c ∈ s, (p c).eval β θ * (p' c).eval β θ +
        μ ^ 2 * ∑ c ∈ s, (g c).eval β θ * (g' c).eval β θ +
        μ * (Real.cos β * ∑ c ∈ s, (p c).eval β θ * (w' c).eval β θ +
          Real.cos β * ∑ c ∈ s, (p' c).eval β θ * (w c).eval β θ) := fun β ↦ by
    have key : ∀ c ∈ s, ((p c).eval β θ + μ * (g c).eval β θ) *
        ((p' c).eval β θ + μ * (g' c).eval β θ) =
        (p c).eval β θ * (p' c).eval β θ + μ ^ 2 * ((g c).eval β θ * (g' c).eval β θ) +
          μ * (Real.cos β * ((p c).eval β θ * (w' c).eval β θ) +
            Real.cos β * ((p' c).eval β θ * (w c).eval β θ)) := fun c hc ↦ by
      have e1 : (p c).eval β θ * (g' c).eval β θ =
          Real.cos β * ((p c).eval β θ * (w' c).eval β θ) := by rw [hg' c hc β θ]; ring
      have e2 : (p' c).eval β θ * (g c).eval β θ =
          Real.cos β * ((p' c).eval β θ * (w c).eval β θ) := by rw [hg c hc β θ]; ring
      linear_combination μ * e1 + μ * e2
    rw [sum_congr rfl key, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_add_distrib,
      ← mul_sum, ← mul_sum]
  simp only [hpt]
  have cpp : Continuous fun β ↦ ∑ c ∈ s, (p c).eval β θ * (p' c).eval β θ :=
    continuous_finsetSum _ fun c _ ↦
      ((p c).continuous_eval_β θ).mul
        ((p' c).continuous_eval_β θ)
  have cgg : Continuous fun β ↦ ∑ c ∈ s, (g c).eval β θ * (g' c).eval β θ :=
    continuous_finsetSum _ fun c _ ↦
      ((g c).continuous_eval_β θ).mul
        ((g' c).continuous_eval_β θ)
  have cpw : Continuous fun β ↦ Real.cos β * ∑ c ∈ s, (p c).eval β θ * (w' c).eval β θ :=
    Real.continuous_cos.mul (continuous_finsetSum _ fun c _ ↦
      ((p c).continuous_eval_β θ).mul
        ((w' c).continuous_eval_β θ))
  have cwp : Continuous fun β ↦ Real.cos β * ∑ c ∈ s, (p' c).eval β θ * (w c).eval β θ :=
    Real.continuous_cos.mul (continuous_finsetSum _ fun c _ ↦
      ((p' c).continuous_eval_β θ).mul
        ((w c).continuous_eval_β θ))
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add,
    integral_sum_mul_eq_trapezoid s p p' hNp hp0 hpπ θ,
    integral_sum_mul_eq_trapezoid s g g' hNg hg0 hgπ θ,
    integral_cos_mul_sum_mul_eq_rule s p w' hN0 hNm hm0 hmπ θ,
    integral_cos_mul_sum_mul_eq_rule s p' w hN0 hNm hm0' hmπ' θ]
  · exact cpw.intervalIntegrable _ _
  · exact cwp.intervalIntegrable _ _
  · exact cpp.intervalIntegrable _ _
  · exact (continuous_const.mul cgg).intervalIntegrable _ _
  · exact (cpp.add (continuous_const.mul cgg)).intervalIntegrable _ _
  · exact (continuous_const.mul (cpw.add cwp)).intervalIntegrable _ _

end PDE.Analysis.TrigPoly2
