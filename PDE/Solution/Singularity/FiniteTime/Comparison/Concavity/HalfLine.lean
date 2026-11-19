/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PDE.Solution.Singularity.FiniteTime.Comparison.Concavity.Basic
import PDE.Solution.Singularity.FiniteTime.Comparison.Concavity.RightEndpoint

/-!
# Future half-line obstruction from the concavity method

A positive mass and its momentum cannot satisfy the concavity inequality with
positive forcing on an entire future half-line. The proof first waits until
the momentum is positive and then chooses the right endpoint to equal its own
Riccati horizon. This is the nonexistence of global solutions given by Levine's concavity
argument (1974), in the form of `Concavity.RightEndpoint`.

## References

* H. A. Levine, "Instability and nonexistence of global solutions to nonlinear wave equations
  of the form `P u_tt = -A u + F(u)`", *Trans. Amer. Math. Soc.* 192 (1974), 1-21, proof of
  Theorem I, (II-2)-(II-4).
  <https://doi.org/10.1090/S0002-9947-1974-0344697-2>
-/

@[expose] public section

open Set

namespace PDE.Solution.Singularity.FiniteTime.Concavity

/-- A positive mass and its momentum cannot satisfy the concavity inequality

`(1 + a) P(t)² ≤ I(t) (P'(t) - b)`

at every future time when `a > 0` and `b > 0`.

The proof first uses `P' ≥ b` to find a time with positive momentum. It then
applies `right_endpoint_lt_riccati_horizon` with the endpoint chosen to be that
same horizon, giving a strict self-inequality. -/
theorem not_concavity_inequality_on_Ici
    {I P : ℝ → ℝ} {a b t₀ : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hI : ∀ t, t₀ ≤ t → HasDerivAt I (P t) t)
    (hP : ∀ t, t₀ ≤ t → DifferentiableAt ℝ P t)
    (hpos : ∀ t, t₀ ≤ t → 0 < I t) :
    ¬ ∀ t, t₀ ≤ t →
      (1 + a) * P t ^ 2 ≤ I t * (deriv P t - b) := by
  intro hconcavity
  let t₁ := t₀ + (|P t₀| + 1) / b
  have ht₀t₁ : t₀ < t₁ := by
    dsimp [t₁]
    exact lt_add_of_pos_right t₀ (div_pos (by positivity) hb)
  have hP_cont : ContinuousOn P (Icc t₀ t₁) :=
    fun t ht ↦ (hP t ht.1).continuousAt.continuousWithinAt
  have hP_diff : DifferentiableOn ℝ P (interior (Icc t₀ t₁)) := by
    intro t ht
    rw [interior_Icc] at ht
    exact (hP t ht.1.le).differentiableWithinAt
  have hsecond : ∀ t ∈ interior (Icc t₀ t₁), b ≤ deriv P t := by
    intro t ht
    rw [interior_Icc] at ht
    exact le_momentum_deriv_of_concavity ha.le (hpos t ht.1.le)
      (hconcavity t ht.1.le)
  have hmomentum_growth :
      b * (t₁ - t₀) ≤ P t₁ - P t₀ := by
    exact (convex_Icc t₀ t₁).mul_sub_le_image_sub_of_le_deriv
      hP_cont hP_diff hsecond
      t₀ (left_mem_Icc.mpr ht₀t₁.le)
      t₁ (right_mem_Icc.mpr ht₀t₁.le) ht₀t₁.le
  have hstep : b * (t₁ - t₀) = |P t₀| + 1 := by
    dsimp [t₁]
    field_simp [hb.ne']
    ring
  rw [hstep] at hmomentum_growth
  have hP₁ : 0 < P t₁ := by
    nlinarith [neg_abs_le (P t₀)]
  let T := t₁ + (a * (P t₁ / I t₁))⁻¹
  have hendpoint : T < t₁ + (a * (P t₁ / I t₁))⁻¹ := by
    apply right_endpoint_lt_riccati_horizon
      (I := I) (P := P) ha hb.le
    · intro t ht
      exact hI t (ht₀t₁.le.trans ht.1)
    · intro t ht
      exact hP t (ht₀t₁.le.trans ht.1)
    · exact hpos t₁ ht₀t₁.le
    · exact hP₁
    · intro t ht
      exact hpos t (ht₀t₁.le.trans ht.1)
    · intro t ht
      exact hconcavity t (ht₀t₁.le.trans ht.1.le)
  dsimp [T] at hendpoint
  exact (lt_irrefl _) hendpoint

end PDE.Solution.Singularity.FiniteTime.Concavity
