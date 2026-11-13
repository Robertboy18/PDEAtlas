/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2

/-!
# The quarter-period rule with the weight `cos β`

An even cosine series `f` of degree `D` is integrated against `cos β` on `[0, π/2]` exactly by
the sine rule read backwards from `π/2`: the substitution `β = π/2 - γ` turns the weight into
`sin γ` and `f (π/2 - γ)` is again an even cosine series of degree `D`
(`IsEvenCosineSeries.integral_mul_cos_eq_rule`). For a table even about `0` and `π/2` in both
variables the tensor rule follows (`TrigPoly2.integral_integral_mul_cos_mul_sin_eq_rule`). The
rule integrates the odd-about-`π/2` products `cos β · E` that the quadrant rule of squares does
not reach, on the same node set `j π / (2N)`.
-/

@[expose] public noncomputable section

namespace CAS.Analysis.IsEvenCosineSeries

open Finset PDE.Analysis

variable {D : ℕ} {f : ℝ → ℝ}

/-- An even cosine series read backwards from `π/2` is an even cosine series of the same
degree. -/
theorem comp_pi_div_two_sub (hf : IsEvenCosineSeries D f) :
    IsEvenCosineSeries D (fun γ ↦ f (Real.pi / 2 - γ)) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun k ↦ (-1) ^ k * a k, fun γ ↦ ?_⟩
  change f (Real.pi / 2 - γ) = _
  rw [ha]
  refine sum_congr rfl fun k _ ↦ ?_
  have h : 2 * (k : ℝ) * (Real.pi / 2 - γ) = k * Real.pi - 2 * k * γ := by ring
  rw [h, Real.cos_sub, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  ring

/-- The rule for the weight `cos β`: `∫₀^{π/2} f (β) cos β dβ = ∑ₙ wₙ f (π/2 - n π / (2N))` with
the sine-rule weights, for an even cosine series of degree `D ≤ N`. -/
theorem integral_mul_cos_eq_rule (hf : IsEvenCosineSeries D f) {N : ℕ} (hN : 0 < N)
    (hDN : D ≤ N) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), f β * Real.cos β =
      ∑ n : Fin (N + 1), quarterSinWeight N n * f (Real.pi / 2 - n * Real.pi / (2 * N)) := by
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun γ ↦ f (Real.pi / 2 - γ) * Real.sin γ) (a := 0) (b := Real.pi / 2) (Real.pi / 2)
  simp only [sub_sub_cancel, sub_zero, sub_self] at hsub
  have hcos : (fun β ↦ f β * Real.cos β) = fun β ↦ f β * Real.sin (Real.pi / 2 - β) := by
    funext β
    rw [Real.sin_pi_div_two_sub]
  rw [hcos, hsub]
  exact hf.comp_pi_div_two_sub.integral_mul_sin_eq_rule hN hDN

end CAS.Analysis.IsEvenCosineSeries

namespace PDE.Analysis

open CAS.Analysis
open Finset

namespace TrigPoly2

variable {Mβ Mθ : ℕ} {R : Type} [Field R] [Algebra R ℝ]

/-- The tensor rule with the weights `cos β` and `sin θ`: a table even about `0` and `π/2` in both
variables, of degrees with `Mβ / 2 ≤ N` and `Mθ / 2 ≤ P`, is integrated against
`cos β sin θ` over the quadrant by the sine rule in both variables, the `β` nodes read from
`π/2`. -/
theorem integral_integral_mul_cos_mul_sin_eq_rule (p : TrigPoly2 Mβ Mθ R)
    (hβ0 : p.IsEvenAtβ 0) (hβπ : p.IsEvenAtβ (Real.pi / 2)) (hθ0 : p.IsEvenAtθ 0)
    (hθπ : p.IsEvenAtθ (Real.pi / 2)) {N P : ℕ} (hN : 0 < N) (hMN : Mβ / 2 ≤ N) (hP : 0 < P)
    (hMP : Mθ / 2 ≤ P) :
    ∫ β in (0 : ℝ)..(Real.pi / 2), ∫ θ in (0 : ℝ)..(Real.pi / 2),
        p.eval β θ * Real.cos β * Real.sin θ =
      ∑ n : Fin (N + 1), ∑ m : Fin (P + 1), quarterSinWeight N n * quarterSinWeight P m *
        p.eval (Real.pi / 2 - n * Real.pi / (2 * N)) (m * Real.pi / (2 * P)) := by
  have hin : ∀ β, ∫ θ in (0 : ℝ)..(Real.pi / 2), p.eval β θ * Real.cos β * Real.sin θ =
      Real.cos β * ∑ m : Fin (P + 1), quarterSinWeight P m * p.eval β (m * Real.pi / (2 * P)) := by
    intro β
    have h := ((isEvenCosineSeries_θ hθ0 hθπ β).mono hMP).integral_mul_sin_eq_rule hP le_rfl
    rw [← h, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    ring
  simp only [hin]
  have hout : ∀ m : Fin (P + 1), ∫ β in (0 : ℝ)..(Real.pi / 2),
      p.eval β (m * Real.pi / (2 * P)) * Real.cos β =
      ∑ n : Fin (N + 1), quarterSinWeight N n *
        p.eval (Real.pi / 2 - n * Real.pi / (2 * N)) (m * Real.pi / (2 * P)) := fun m ↦
    ((isEvenCosineSeries_β hβ0 hβπ _).mono hMN).integral_mul_cos_eq_rule hN le_rfl
  have hcont : ∀ m : Fin (P + 1), IntervalIntegrable
      (fun β ↦ p.eval β (m * Real.pi / (2 * P)) * Real.cos β) MeasureTheory.volume 0
        (Real.pi / 2) := fun m ↦
    ((p.continuous_eval_β _).mul Real.continuous_cos).intervalIntegrable _ _
  calc ∫ β in (0 : ℝ)..(Real.pi / 2), Real.cos β *
        ∑ m : Fin (P + 1), quarterSinWeight P m * p.eval β (m * Real.pi / (2 * P)) =
      ∫ β in (0 : ℝ)..(Real.pi / 2), ∑ m : Fin (P + 1), quarterSinWeight P m *
        (p.eval β (m * Real.pi / (2 * P)) * Real.cos β) := by
        refine intervalIntegral.integral_congr fun β _ ↦ ?_
        simp only [Finset.mul_sum]
        exact sum_congr rfl fun m _ ↦ by ring
    _ = ∑ m : Fin (P + 1), quarterSinWeight P m * ∫ β in (0 : ℝ)..(Real.pi / 2),
        p.eval β (m * Real.pi / (2 * P)) * Real.cos β := by
        rw [intervalIntegral.integral_finsetSum fun m _ ↦ (hcont m).const_mul _]
        simp only [intervalIntegral.integral_const_mul]
    _ = _ := by
        simp only [hout, Finset.mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun n _ ↦ sum_congr rfl fun m _ ↦ by ring

end TrigPoly2

end PDE.Analysis
