/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Constant
public import PDE.Analysis.Evolution.ODE.Linear.Scalar
import CAS.ExactTactic

/-!
# Constant-rate scalar solutions

For a constant rate `κ`, the integrating-factor solution `scalarLinearSolution` is
`e^{-κ(t-t₀)} r₀ + ∫_{t₀}^t e^{-κ(t-s)} f(s) ds`, for either sign of `κ` and `f`. A
function `r` continuous on `[t₀, t₁]` with `r' = -κ r + f` on `(t₀, t₁)` equals this
solution at `t₁`. The proof applies `eq_exp_apply_add_integral_of_hasDerivAt` to
the operator `-κ • 1`.
-/

@[expose] public noncomputable section

open MeasureTheory NormedSpace Set

namespace PDE.Analysis.Evolution

/-- For constant rate `κ`, the integrating-factor solution is
`e^{-κ(t-t₀)} r₀ + ∫_{t₀}^t e^{-κ(t-s)} f(s) ds`, the integral oriented. The identity
holds for all `t₀, t` and every `f`. -/
theorem scalarLinearSolution_const_eq_exp_mul_add_integral
    (κ : ℝ) (f : ℝ → ℝ) (t₀ r₀ t : ℝ) :
    scalarLinearSolution (fun _ ↦ κ) f t₀ r₀ t =
      Real.exp (-κ * (t - t₀)) * r₀ +
        ∫ s in t₀..t, Real.exp (-κ * (t - s)) * f s := by
  unfold scalarLinearSolution
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [show -((t - t₀) * κ) = -κ * (t - t₀) by cas,
    mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← mul_assoc, ← Real.exp_add]
  rw [show -κ * (t - t₀) + (s - t₀) * κ = -κ * (t - s) by cas]

/-- If `r` and `f` are continuous on `[t₀, t₁]` and `r' = -κ r + f` on `(t₀, t₁)`,
then `r(t₁)` is the integrating-factor solution with initial value `r(t₀)`. -/
theorem eq_scalarLinearSolution_const_of_hasDerivAt
    {r f : ℝ → ℝ} {κ t₀ t₁ : ℝ}
    (htime : t₀ ≤ t₁) (hr : ContinuousOn r (Icc t₀ t₁))
    (hf : ContinuousOn f (Icc t₀ t₁))
    (hd : ∀ t ∈ Ioo t₀ t₁, HasDerivAt r (-κ * r t + f t) t) :
    r t₁ = scalarLinearSolution (fun _ ↦ κ) f t₀ (r t₀) t₁ := by
  rw [scalarLinearSolution_const_eq_exp_mul_add_integral]
  have he (s : ℝ) : exp (s • (1 : ℝ →L[ℝ] ℝ)) =
      Real.exp s • (1 : ℝ →L[ℝ] ℝ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ] using
      (algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := ℝ →L[ℝ] ℝ) s).symm
  have h := eq_exp_apply_add_integral_of_hasDerivAt
    ((-κ) • (1 : ℝ →L[ℝ] ℝ)) htime hr hf (fun t ht ↦ by
      simpa only [smul_apply, one_apply_eq_self, smul_eq_mul] using hd t ht)
  simpa only [smul_smul, he, smul_apply, one_apply_eq_self, smul_eq_mul,
    mul_comm] using h

end PDE.Analysis.Evolution
