/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analytic.CauchyKovalevskaya.Solution.InitialData

/-!
# A nonlinear coupled analytic Cauchy problem

The principal matrix has the state on its diagonal and ones off the diagonal.
The initial function is `(x, 1 + x²)`. The analytic existence theorem accepts
coefficients analytic at the prescribed initial state and analytic initial data.
It constructs a solution of both coupled equations with that initial function
on a ball of positive radius. Evans, §4.6.3, Theorem 2, states this theorem for the
first-order system (15) with zero data and coefficients independent of the normal variable.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, (14)-(15) and Theorem 2 (Cauchy–Kovalevskaya
  Theorem), pp. 239-240.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Examples.Analytic.CauchyKovalevskaya.Coupled

open PDE.Analytic.CauchyKovalevskaya

/-- A state-dependent principal matrix with nonzero off-diagonal coupling. -/
def coefficients (_j : Fin 1) (i k : Fin 2) (z : (Fin 2 ⊕ Fin 1) → ℝ) : ℝ :=
  if i = k then z (.inl i) else 1

/-- Spatial forcing `(x, 1 + x²)`. -/
def forcing (i : Fin 2) (z : (Fin 2 ⊕ Fin 1) → ℝ) : ℝ :=
  Fin.cases (z (.inr 0)) (fun _ ↦ 1 + z (.inr 0) ^ 2) i

/-- Nonzero, nonconstant analytic initial data. -/
def initialData (x : Fin 1 → ℝ) (i : Fin 2) : ℝ :=
  Fin.cases (x 0) (fun _ ↦ 1 + x 0 ^ 2) i

/-- Each principal entry is either a coordinate or a constant. -/
theorem analyticAt_coefficients (j : Fin 1) (i k : Fin 2) (z : (Fin 2 ⊕ Fin 1) → ℝ) :
    AnalyticAt ℝ (coefficients j i k) z := by
  unfold coefficients
  by_cases h : i = k
  · simp only [ite_eq_left h]
    exact (ContinuousLinearMap.proj (.inl i) :
      ((Fin 2 ⊕ Fin 1) → ℝ) →L[ℝ] ℝ).analyticAt z
  · simp only [ite_eq_right h]
    exact analyticAt_const

/-- Polynomial forcing is analytic at every state and spatial position. -/
theorem analyticAt_forcing (i : Fin 2) (z : (Fin 2 ⊕ Fin 1) → ℝ) :
    AnalyticAt ℝ (forcing i) z := by
  let X : (((Fin 2 ⊕ Fin 1) → ℝ) →L[ℝ] ℝ) := ContinuousLinearMap.proj (.inr 0)
  refine Fin.cases ?_ (fun _ ↦ ?_) i
  · exact X.analyticAt z
  · exact analyticAt_const.add ((X.analyticAt z).pow 2)

/-- The prescribed vector-valued initial function is analytic. -/
theorem analyticAt_initialData : AnalyticAt ℝ initialData 0 := by
  let X : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  apply AnalyticAt.pi
  intro i
  refine Fin.cases ?_ (fun _ ↦ ?_) i
  · exact X.analyticAt 0
  · exact analyticAt_const.add ((X.analyticAt 0).pow 2)

/-- Analytic existence for the two coupled nonlinear equations with initial function
`(x, 1 + x²)`, on a ball of positive radius. -/
theorem exists_analytic_coupled_solution :
    ∃ r : ℝ, 0 < r ∧ ∃ u : (Fin 2 → ℝ) → Fin 2 → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball (0 : Fin 1 → ℝ) r,
        u (Fin.cons 0 x) 0 = x 0 ∧ u (Fin.cons 0 x) 1 = 1 + x 0 ^ 2) ∧
      ∀ p ∈ Metric.ball 0 r,
        (fderiv ℝ (fun y ↦ u y 0) p (Pi.single 0 1) =
          u p 0 * fderiv ℝ (fun y ↦ u y 0) p (Pi.single 1 1) +
            fderiv ℝ (fun y ↦ u y 1) p (Pi.single 1 1) + p 1) ∧
        (fderiv ℝ (fun y ↦ u y 1) p (Pi.single 0 1) =
          fderiv ℝ (fun y ↦ u y 0) p (Pi.single 1 1) +
            u p 1 * fderiv ℝ (fun y ↦ u y 1) p (Pi.single 1 1) + (1 + p 1 ^ 2)) := by
  obtain ⟨r, hr, u, hua, hut, hue⟩ := exists_analytic_solution
    coefficients forcing initialData
    (fun j i k ↦ analyticAt_coefficients j i k _) (fun i ↦ analyticAt_forcing i _)
    analyticAt_initialData
  refine ⟨r, hr, u, hua, ?_, ?_⟩
  · intro x hx
    exact ⟨congrFun (hut x hx) 0, congrFun (hut x hx) 1⟩
  · intro p hp
    constructor
    · simpa [rightHandSide, coefficients, forcing, arguments,
        Fin.sum_univ_one, Fin.sum_univ_two, Fin.tail] using hue p hp 0
    · simpa [rightHandSide, coefficients, forcing, arguments,
        Fin.sum_univ_one, Fin.sum_univ_two, Fin.tail] using! hue p hp 1

end PDE.Examples.Analytic.CauchyKovalevskaya.Coupled
