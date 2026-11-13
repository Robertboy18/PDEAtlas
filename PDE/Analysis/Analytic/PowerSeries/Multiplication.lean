/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Analytic.PowerSeries.Approximation

/-!
# Products of commutative analytic expansions

Polynomial Taylor approximations identify the coefficients of an analytic product.
Only finite polynomial multiplication is needed; convergence and remainder estimates
come from native multilinear expansions.
-/

@[expose] public section

open scoped Topology
open Filter Asymptotics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The commutative coefficients of an analytic product are the formal Cauchy product. -/
theorem HasFPowerSeriesAt.toMvPowerSeries_mul
    {f g : (ι → ℝ) → ℝ} {p q r : FormalMultilinearSeries ℝ (ι → ℝ) ℝ}
    (hp : HasFPowerSeriesAt f p 0) (hq : HasFPowerSeriesAt g q 0)
    (hr : HasFPowerSeriesAt (f * g) r 0) :
    r.toMvPowerSeries = p.toMvPowerSeries * q.toMvPowerSeries := by
  classical
  ext a
  let N := a.degree + 1
  let P := p.toMvPowerSeries.truncTotal N
  let Q := q.toMvPowerSeries.truncTotal N
  have hP := P.hasFiniteFPowerSeriesOnBall_eval.toHasFPowerSeriesOnBall.hasFPowerSeriesAt
  have h₁ := (hp.isBigO_sub_eval_truncTotal_pow N).mul
    (hq.continuousAt.isBigO_one ℝ)
  have h₂ := (hP.continuousAt.isBigO_one ℝ).mul
    (hq.isBigO_sub_eval_truncTotal_pow N)
  simp only [mul_one] at h₁
  simp only [one_mul] at h₂
  have he : (fun x ↦ f x * g x - MvPolynomial.eval x (P * Q))
      =O[𝓝 0] fun x ↦ ‖x‖ ^ N := by
    simpa only [P, Q, MvPolynomial.eval_mul, sub_mul, mul_sub,
      sub_add_sub_cancel] using h₁.add h₂
  exact (hr.coeff_eq_of_isBigO_sub_eval (P * Q) he a (Nat.lt_succ_self _)).trans
    (MvPowerSeries.coeff_truncTotal_mul_truncTotal_eq_coeff_mul
      p.toMvPowerSeries q.toMvPowerSeries (Nat.lt_succ_self _))
