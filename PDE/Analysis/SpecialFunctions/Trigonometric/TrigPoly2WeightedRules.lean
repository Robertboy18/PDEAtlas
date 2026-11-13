/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2QuotientParity

/-!
# Exact rules for products of tables of different degrees, with the weight `cos β`

The quadrant rules for `∫₀^{π/2}∫₀^{π/2} (∑_c p_c q_c) sin θ` hold for tables `p_c` and `q_c` of
different degrees: the product has the sum of the degrees, so the trapezoid rule in `β` needs
`(Mβ + Nβ) / 2 < 2N` (`integral_integral_sum_mul_mul_sin_eq_rule_of_le`).

A product that is odd about `β = π/2` is `cos β` times a product that is even about `0` and about
`π/2`. Its integral over the quadrant follows from the sine rule after the substitution
`β = π/2 - t`, which turns `cos β` into `sin t` and keeps the evenness, so the weights are the
sine weights at the reversed nodes `π/2 - jπ/(2N) = (N - j)π/(2N)` of the same grid
(`integral_mul_cos_eq_rule`, `integral_integral_mul_cos_sum_mul_mul_sin_eq_rule`). This rule
needs `(Mβ + Nβ) / 2 ≤ N`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open CAS.Analysis
open Finset

/-- The cosine-weighted quarter rule: for an even cosine series `f` of degree `D ≤ N`,
`∫₀^{π/2} cos β f(β) dβ = ∑_n w_n f(π/2 - nπ/(2N))` with the sine weights. -/
theorem _root_.CAS.Analysis.IsEvenCosineSeries.integral_mul_cos_eq_rule {D : ℕ} {f : ℝ → ℝ}
    (hf : IsEvenCosineSeries D f) {N : ℕ} (hN : 0 < N) (hDN : D ≤ N) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), f β * Real.cos β =
      ∑ n : Fin (N + 1), quarterSinWeight N n * f (Real.pi / 2 - n * Real.pi / (2 * N)) := by
  have hrefl : IsEvenCosineSeries D (fun t ↦ f (Real.pi / 2 - t)) := by
    obtain ⟨a, ha⟩ := hf
    refine ⟨fun k ↦ (-1) ^ k * a k, fun x ↦ ?_⟩
    dsimp only
    rw [ha (Real.pi / 2 - x)]
    refine sum_congr rfl fun k _ ↦ ?_
    have h : 2 * (k : ℝ) * (Real.pi / 2 - x) = (k : ℝ) * Real.pi - 2 * k * x := by ring
    rw [h, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
    ring
  have hsub := intervalIntegral.integral_comp_sub_left (fun β ↦ f β * Real.cos β)
    (a := 0) (b := Real.pi / 2) (Real.pi / 2)
  simp only [sub_zero, sub_self] at hsub
  rw [← hsub]
  have hcos : ∀ t, f (Real.pi / 2 - t) * Real.cos (Real.pi / 2 - t) =
      f (Real.pi / 2 - t) * Real.sin t := fun t ↦ by rw [Real.cos_pi_div_two_sub]
  simp only [hcos]
  exact hrefl.integral_mul_sin_eq_rule hN hDN

/-- The quadrant integral against `sin θ` is additive in continuous integrands. -/
theorem integral_integral_add_mul_sin {F G : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    (hG : Continuous (Function.uncurry G)) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2), (F β θ + G β θ) * Real.sin θ =
      (∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2), F β θ * Real.sin θ) +
        ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2), G β θ * Real.sin θ := by
  have hFs : Continuous fun p : ℝ × ℝ ↦ F p.1 p.2 * Real.sin p.2 :=
    hF.mul (Real.continuous_sin.comp continuous_snd)
  have hGs : Continuous fun p : ℝ × ℝ ↦ G p.1 p.2 * Real.sin p.2 :=
    hG.mul (Real.continuous_sin.comp continuous_snd)
  have hin : ∀ β, ∫ θ in (0 : ℝ)..(Real.pi / 2), (F β θ + G β θ) * Real.sin θ =
      (∫ θ in (0 : ℝ)..(Real.pi / 2), F β θ * Real.sin θ) +
        ∫ θ in (0 : ℝ)..(Real.pi / 2), G β θ * Real.sin θ := fun β ↦ by
    simp only [add_mul]
    exact intervalIntegral.integral_add
      ((hFs.comp (Continuous.prodMk_right β)).intervalIntegrable _ _)
      ((hGs.comp (Continuous.prodMk_right β)).intervalIntegrable _ _)
  simp only [hin]
  exact intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β θ ↦ F β θ * Real.sin θ) hFs _ _).intervalIntegrable _ _)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun β θ ↦ G β θ * Real.sin θ) hGs _ _).intervalIntegrable _ _)

/-- Constants come out of the quadrant integral. -/
theorem integral_integral_const_mul_mul_sin (c : ℝ) (F : ℝ → ℝ → ℝ) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2), c * F β θ * Real.sin θ =
      c * ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2), F β θ * Real.sin θ := by
  simp only [mul_assoc, intervalIntegral.integral_const_mul]

namespace TrigPoly2

variable {Mβ Mθ Nβ Nθ : ℕ} {R : Type} [Field R] [Algebra R ℝ]

/-- The θ-derivative commutes with a quotient by `cos β`. -/
theorem eval_dθ_mul_cos_β {q : TrigPoly2 Nβ Nθ R} {p : TrigPoly2 Mβ Mθ R}
    (h : ∀ β θ, q.eval β θ * Real.cos β = p.eval β θ) (β θ : ℝ) :
    q.dθ.eval β θ * Real.cos β = p.dθ.eval β θ := by
  have hq := (hasDerivAt_eval_θ q β θ).mul_const (Real.cos β)
  rw [show (fun t ↦ q.eval β t * Real.cos β) = p.eval β from funext (h β)] at hq
  exact hq.unique (hasDerivAt_eval_θ p β θ)

/-- **Exact rule for products of tables of different degrees.** -/
theorem integral_integral_sum_mul_mul_sin_eq_rule_of_le {ι : Type*} (s : Finset ι)
    (p : ι → TrigPoly2 Mβ Mθ R) (q : ι → TrigPoly2 Nβ Nθ R) {N P : ℕ}
    (hN : (Mβ + Nβ) / 2 < 2 * N) (hP : 0 < P) (hMP : (Mθ + Nθ) / 2 ≤ P)
    (hβ0 : ∀ c ∈ s, ∃ e, ParityAtβ 0 e (p c) ∧ ParityAtβ 0 e (q c))
    (hβπ : ∀ c ∈ s, ∃ e, ParityAtβ (Real.pi / 2) e (p c) ∧ ParityAtβ (Real.pi / 2) e (q c))
    (hθ0 : ∀ c ∈ s, ∃ e, ParityAtθ 0 e (p c) ∧ ParityAtθ 0 e (q c))
    (hθπ : ∀ c ∈ s, ∃ e, ParityAtθ (Real.pi / 2) e (p c) ∧ ParityAtθ (Real.pi / 2) e (q c)) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2),
        (∑ c ∈ s, (p c).eval β θ * (q c).eval β θ) * Real.sin θ =
      ∑ j : Fin (N + 1), ∑ n : Fin (P + 1), quarterTrapezoidWeight N j * quarterSinWeight P n *
        ∑ c ∈ s, (p c).eval (j * Real.pi / (2 * N)) (n * Real.pi / (2 * P)) *
          (q c).eval (j * Real.pi / (2 * N)) (n * Real.pi / (2 * P)) := by
  have hf : ∀ β θ, ∑ c ∈ s, (p c).eval β θ * (q c).eval β θ =
      ∑ c ∈ s, ((p c).mul (q c)).eval β θ := fun β θ ↦ by simp only [eval_mul]
  simp only [hf]
  refine integral_integral_mul_sin_eq_rule (f := fun β θ ↦ ∑ c ∈ s, ((p c).mul (q c)).eval β θ)
    hN hP hMP (fun θ ↦ IsEvenCosineSeries.sum s fun c hc ↦ ?_)
    (fun β ↦ IsEvenCosineSeries.sum s fun c hc ↦ ?_)
  · exact isEvenCosineSeries_β (isEvenAtβ_mul_of_parity (hβ0 c hc))
      (isEvenAtβ_mul_of_parity (hβπ c hc)) θ
  · exact isEvenCosineSeries_θ (isEvenAtθ_mul_of_parity (hθ0 c hc))
      (isEvenAtθ_mul_of_parity (hθπ c hc)) β

/-- **Exact rule with the weight `cos β`.** For families `p`, `q` with componentwise equal
parities about `0` and `π/2` in each variable, `∫∫ cos β (∑_c p_c q_c) sin θ` over `[0, π/2]²` is
the sine rule in `β` at the reversed nodes and in `θ`. -/
theorem integral_integral_mul_cos_sum_mul_mul_sin_eq_rule {ι : Type*} (s : Finset ι)
    (p : ι → TrigPoly2 Mβ Mθ R) (q : ι → TrigPoly2 Nβ Nθ R) {N P : ℕ} (hN0 : 0 < N)
    (hN : (Mβ + Nβ) / 2 ≤ N) (hP : 0 < P) (hMP : (Mθ + Nθ) / 2 ≤ P)
    (hβ0 : ∀ c ∈ s, ∃ e, ParityAtβ 0 e (p c) ∧ ParityAtβ 0 e (q c))
    (hβπ : ∀ c ∈ s, ∃ e, ParityAtβ (Real.pi / 2) e (p c) ∧ ParityAtβ (Real.pi / 2) e (q c))
    (hθ0 : ∀ c ∈ s, ∃ e, ParityAtθ 0 e (p c) ∧ ParityAtθ 0 e (q c))
    (hθπ : ∀ c ∈ s, ∃ e, ParityAtθ (Real.pi / 2) e (p c) ∧ ParityAtθ (Real.pi / 2) e (q c)) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.cos β * (∑ c ∈ s, (p c).eval β θ * (q c).eval β θ) * Real.sin θ =
      ∑ j : Fin (N + 1), ∑ n : Fin (P + 1), quarterSinWeight N j * quarterSinWeight P n *
        ∑ c ∈ s, (p c).eval (Real.pi / 2 - j * Real.pi / (2 * N)) (n * Real.pi / (2 * P)) *
          (q c).eval (Real.pi / 2 - j * Real.pi / (2 * N)) (n * Real.pi / (2 * P)) := by
  set f : ℝ → ℝ → ℝ := fun β θ ↦ ∑ c ∈ s, ((p c).mul (q c)).eval β θ with hfdef
  have hf : ∀ β θ, ∑ c ∈ s, (p c).eval β θ * (q c).eval β θ = f β θ := fun β θ ↦ by
    simp only [hfdef, eval_mul]
  simp only [hf]
  have hfβ : ∀ θ, IsEvenCosineSeries ((Mβ + Nβ) / 2) fun β ↦ f β θ := fun θ ↦
    IsEvenCosineSeries.sum s fun c hc ↦ isEvenCosineSeries_β
      (isEvenAtβ_mul_of_parity (hβ0 c hc)) (isEvenAtβ_mul_of_parity (hβπ c hc)) θ
  have hfθ : ∀ β, IsEvenCosineSeries ((Mθ + Nθ) / 2) (f β) := fun β ↦
    IsEvenCosineSeries.sum s fun c hc ↦ isEvenCosineSeries_θ
      (isEvenAtθ_mul_of_parity (hθ0 c hc)) (isEvenAtθ_mul_of_parity (hθπ c hc)) β
  have hθrule : ∀ β, ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.cos β * f β θ * Real.sin θ =
      ∑ n : Fin (P + 1), quarterSinWeight P n * (Real.cos β * f β (n * Real.pi / (2 * P))) := by
    intro β
    have h := (hfθ β).integral_mul_sin_eq_rule hP hMP
    simp only [mul_assoc]
    rw [intervalIntegral.integral_const_mul, h, mul_sum]
    exact sum_congr rfl fun n _ ↦ by ring
  simp only [hθrule]
  have hcont : ∀ n : Fin (P + 1), Continuous fun β ↦
      quarterSinWeight P n * (Real.cos β * f β (n * Real.pi / (2 * P))) := fun n ↦
    continuous_const.mul (Real.continuous_cos.mul (hfβ _).continuous)
  rw [intervalIntegral.integral_finsetSum fun n _ ↦ (hcont n).intervalIntegrable _ _]
  simp only [show ∀ (n : Fin (P + 1)) (β : ℝ), quarterSinWeight P n *
      (Real.cos β * f β (n * Real.pi / (2 * P))) =
        quarterSinWeight P n * (f β (n * Real.pi / (2 * P)) * Real.cos β) from
      fun n β ↦ by ring, intervalIntegral.integral_const_mul]
  simp only [fun n ↦ (hfβ ((n : ℝ) * Real.pi / (2 * P))).integral_mul_cos_eq_rule hN0 hN,
    mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun j _ ↦ sum_congr rfl fun n _ ↦ by ring

end TrigPoly2

end PDE.Analysis
