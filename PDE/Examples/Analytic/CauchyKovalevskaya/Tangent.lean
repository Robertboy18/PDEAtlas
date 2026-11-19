/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analytic.CauchyKovalevskaya.Solution.Existence
public import PDE.Analytic.CauchyKovalevskaya.Solution.Uniqueness
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import CAS.ExactTactic

/-!
# Identifying a nonlinear Cauchy solution by checked differentiation

The analytic existence theorem for zero initial data constructs a local
solution of `u_t = u u_x + x` from the analytic coefficients.
Analytic germ uniqueness identifies it with `x tan t`. The scalar
tangent derivative is checked by the computer algebra system SymLean; the Fréchet chain and
product rules transfer it to the finite-coordinate spacetime of the theorem. The existence
theorem is the Cauchy–Kovalevskaya theorem, Evans, §4.6.3, Theorem 2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.6.3, (14)-(15) and Theorem 2 (Cauchy–Kovalevskaya
  Theorem), pp. 239-240.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Topology
open Filter

noncomputable section

namespace PDE.Examples.Analytic.CauchyKovalevskaya.Tangent

open PDE.Analytic.CauchyKovalevskaya

/-- The comparison function `(t, x) ↦ x tan t` for the nonlinear Cauchy problem. -/
def profile (p : Fin 2 → ℝ) : ℝ := p 1 * Real.tan (p 0)

/-- The comparison function is analytic at the spacetime origin. -/
theorem analyticAt_profile : AnalyticAt ℝ profile 0 := by
  let T : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let X : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  have hs := Real.analyticAt_sin.comp (T.analyticAt 0)
  have hc := Real.analyticAt_cos.comp (T.analyticAt 0)
  unfold profile
  simpa only [Real.tan_eq_sin_div_cos] using!
    (X.analyticAt 0).mul (hs.div hc (by simp [T]))

/-- Checked scalar differentiation and the Fréchet chain rule give the derivative of
`(t, x) ↦ x tan t` in every direction, at points where `cos t ≠ 0`. -/
theorem fderiv_profile (p h : Fin 2 → ℝ) (hc : Real.cos (p 0) ≠ 0) :
    fderiv ℝ profile p h =
      p 1 * ((1 / Real.cos (p 0) ^ 2) * h 0) + Real.tan (p 0) * h 1 := by
  let T : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  let X : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  have ht : HasDerivAt Real.tan (1 / Real.cos (p 0) ^ 2) (p 0) := by
    cas using hc
  have hd := X.hasFDerivAt.mul (ht.comp_hasFDerivAt p T.hasFDerivAt)
  have he := congrArg (fun D : (Fin 2 → ℝ) →L[ℝ] ℝ ↦ D h) hd.fderiv
  simpa [T, X, Function.comp_def] using! he

/-- The explicit function satisfies the nonlinear equation where `cos t ≠ 0`.
The final rational identity is checked by the computer algebra system. -/
theorem profile_equation (p : Fin 2 → ℝ) (hc : Real.cos (p 0) ≠ 0) :
    fderiv ℝ profile p (Pi.single 0 1) =
      profile p * fderiv ℝ profile p (Pi.single 1 1) + p 1 := by
  rw [fderiv_profile p _ hc, fderiv_profile p _ hc]
  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), mul_one, mul_zero, add_zero, zero_add,
    profile]
  have hs := Real.sin_sq_add_cos_sq (p 0)
  cas using hc

/-- Analytic coefficient germs and zero initial data give a solution on a
positive ball. Uniqueness identifies its germ with the explicit function
whose Fréchet derivative and equation were checked above. -/
theorem exists_analytic_solution_eq_profile :
    ∃ r : ℝ, 0 < r ∧ ∃ u : (Fin 2 → ℝ) → Fin 1 → ℝ,
      AnalyticOnNhd ℝ u (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball (0 : Fin 1 → ℝ) r, u (Fin.cons 0 x) = 0) ∧
      (∀ p ∈ Metric.ball 0 r,
        fderiv ℝ (fun y ↦ u y 0) p (Pi.single 0 1) =
          u p 0 * fderiv ℝ (fun y ↦ u y 0) p (Pi.single 1 1) + p 1) ∧
      u =ᶠ[𝓝 0] fun p _ ↦ profile p := by
  let B (_j _i _k : Fin 1) (z : (Fin 1 ⊕ Fin 1) → ℝ) := z (.inl 0)
  let c (_i : Fin 1) (z : (Fin 1 ⊕ Fin 1) → ℝ) := z (.inr 0)
  have hB (j i k : Fin 1) : AnalyticAt ℝ (B j i k) 0 := by
    simpa only [B] using!
      (ContinuousLinearMap.proj (.inl 0) : ((Fin 1 ⊕ Fin 1) → ℝ) →L[ℝ] ℝ).analyticAt 0
  have hc (i : Fin 1) : AnalyticAt ℝ (c i) 0 := by
    simpa only [c] using!
      (ContinuousLinearMap.proj (.inr 0) : ((Fin 1 ⊕ Fin 1) → ℝ) →L[ℝ] ℝ).analyticAt 0
  obtain ⟨r, hr, u, hua, hut, hue⟩ := exists_analytic_solution_zero B c hB hc
  have hu0 := hua 0 (Metric.mem_ball_self hr)
  let T : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hcos : ∀ᶠ p : Fin 2 → ℝ in 𝓝 0, Real.cos (p 0) ≠ 0 :=
    (isOpen_ne_fun (Real.continuous_cos.comp T.continuous) continuous_const).mem_nhds
      (by simp [T])
  have htrace (i : Fin 1) : (fun x : Fin 1 → ℝ ↦ u (Fin.cons 0 x) i) =ᶠ[𝓝 0] 0 := by
    filter_upwards [Metric.ball_mem_nhds 0 hr] with x hx
    exact congrFun (hut x hx) i
  have hEq (i : Fin 1) :
      (fun p ↦ fderiv ℝ (fun y ↦ u y i) p (Pi.single 0 1))
        =ᶠ[𝓝 0] rightHandSide B c u i := by
    filter_upwards [Metric.ball_mem_nhds 0 hr] with p hp
    exact hue p hp i
  have heq := eventuallyEq_of_analytic_solutions_zero hB hc
    (fun i ↦
      ((ContinuousLinearMap.proj i : (Fin 1 → ℝ) →L[ℝ] ℝ).analyticAt _).comp hu0)
    (v := fun p _ ↦ profile p) (fun _ ↦ analyticAt_profile) htrace
    (fun _ ↦ Filter.Eventually.of_forall (fun x ↦ by simp [profile])) hEq
    (fun _ ↦ by
      filter_upwards [hcos] with p hp
      simpa [rightHandSide, B, c, arguments, Fin.sum_univ_one, Fin.tail] using!
        profile_equation p hp)
  refine ⟨r, hr, u, hua, hut, ?_, heq⟩
  intro p hp
  simpa [rightHandSide, B, c, arguments, Fin.sum_univ_one, Fin.tail] using hue p hp 0

end PDE.Examples.Analytic.CauchyKovalevskaya.Tangent
