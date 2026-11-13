/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analytic.CauchyKovalevskaya.Solution.TimeDependent


/-!
# Analytic time-dependent transport

A scalar transport equation shows the Cauchy–Kovalevskaya existence theorem with
explicit time dependence and nonzero analytic initial data. Evans, §4.6.3, reduces such
problems to zero data and to coefficients independent of the normal variable before Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, (14)-(15) and Theorem 2 (Cauchy–Kovalevskaya
  Theorem), pp. 239-240.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Examples.Analytic.CauchyKovalevskaya

open PDE.Analytic.CauchyKovalevskaya

/-- The time-dependent existence theorem gives an analytic solution of
`u_t = u_x + t + u` with nonzero data `u(0,x) = 1 + x`. -/
theorem exists_analytic_time_dependent_transport :
    ∃ r : ℝ, 0 < r ∧ ∃ u : (Fin 2 → ℝ) → Fin 1 → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball (0 : Fin 1 → ℝ) r, u (Fin.cons 0 x) 0 = 1 + x 0) ∧
      ∀ p ∈ Metric.ball 0 r,
        fderiv ℝ (fun y ↦ u y 0) p (Pi.single 0 1) =
          fderiv ℝ (fun y ↦ u y 0) p (Pi.single 1 1) + (p 0 + u p 0) := by
  let B (_j _i _k : Fin 1) (_z : ℝ × ((Fin 1 ⊕ Fin 1) → ℝ)) : ℝ := 1
  let c (_i : Fin 1) (z : ℝ × ((Fin 1 ⊕ Fin 1) → ℝ)) := z.1 + z.2 (.inl 0)
  let g (x : Fin 1 → ℝ) (_i : Fin 1) := 1 + x 0
  let T : (ℝ × ((Fin 1 ⊕ Fin 1) → ℝ)) →L[ℝ] ℝ :=
    ContinuousLinearMap.fst ℝ ℝ ((Fin 1 ⊕ Fin 1) → ℝ)
  let P : (ℝ × ((Fin 1 ⊕ Fin 1) → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (.inl 0)).comp
      (ContinuousLinearMap.snd ℝ ℝ ((Fin 1 ⊕ Fin 1) → ℝ))
  have hc (i : Fin 1) : AnalyticAt ℝ (c i) (0, Sum.elim (g 0) 0) :=
    (T.analyticAt _).add (P.analyticAt _)
  have hg : AnalyticAt ℝ g 0 :=
    AnalyticAt.pi (fun _ ↦ analyticAt_const.add
      ((ContinuousLinearMap.proj 0 : (Fin 1 → ℝ) →L[ℝ] ℝ).analyticAt 0))
  obtain ⟨r, hr, u, hua, hut, hue⟩ := exists_analytic_solution_time_dependent
    B c g (fun _ _ _ ↦ analyticAt_const) hc hg
  refine ⟨r, hr, u, hua, ?_, ?_⟩
  · intro x hx
    exact congrFun (hut x hx) 0
  · intro p hp
    simpa [timeDependentRightHandSide, B, c, arguments, Fin.sum_univ_one] using hue p hp 0

end PDE.Examples.Analytic.CauchyKovalevskaya
