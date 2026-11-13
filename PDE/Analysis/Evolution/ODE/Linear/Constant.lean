/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Variation of constants for bounded autonomous linear equations

A solution of `u' = Au + f` satisfies the exponential integral formula.
Only interior derivatives and closed-interval continuity are needed, so the
initial endpoint does not require an extension of the solution across it.
-/

@[expose] public noncomputable section

open MeasureTheory NormedSpace Set

namespace PDE.Analysis.Evolution

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]

/-- Rational scalars on bounded endomorphisms, used by the exponential series. -/
local instance normedAlgebraRatLinearEndomorphism : NormedAlgebra ℚ (E →L[𝕜] E) :=
  NormedAlgebra.restrictScalars ℚ 𝕜 (E →L[𝕜] E)

/-- The integrating factor cancels the homogeneous part of a linear
differential equation, also for complex operators and real time. -/
theorem hasDerivAt_exp_sub_apply (A : E →L[𝕜] E) {u : ℝ → E} {g : E} {t : ℝ}
    (hu : HasDerivAt u (A (u t) + g) t) (b : ℝ) :
    HasDerivAt (fun s : ℝ ↦ exp ((b - s) • A) (u s))
      (exp ((b - t) • A) g) t := by
  have he : HasDerivAt (fun s : ℝ ↦ exp ((b - s) • A))
      (-(exp ((b - t) • A) * A)) t := by
    have hc : HasDerivAt (fun s : ℝ ↦ ((b - s : ℝ) : 𝕜)) (-1 : 𝕜) t := by
      simpa [Function.comp_def] using
        (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).const_sub b)
    simpa only [Function.comp_def, ← RCLike.real_smul_eq_coe_smul (K := 𝕜),
      neg_smul, one_smul] using
      (hasDerivAt_exp_smul_const A ((b - t : ℝ) : 𝕜)).scomp t hc
  have hr : HasDerivAt
      (fun s : ℝ ↦ (exp ((b - s) • A)).restrictScalars ℝ)
      ((-(exp ((b - t) • A) * A)).restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL 𝕜 E E ℝ ℝ).hasFDerivAt.comp_hasDerivAt t he
  apply (hr.clm_apply hu).congr_deriv
  change -(exp ((b - t) • A) (A (u t))) +
    exp ((b - t) • A) (A (u t) + g) = exp ((b - t) • A) g
  rw [map_add, neg_add_cancel_left]

/-- Variation of constants: if `u` and `f` are continuous on `[a, b]` and
`u' = A u + f` on `(a, b)`, then `u(b) = e^{(b-a)A} u(a) + ∫ₐᵇ e^{(b-s)A} f(s) ds`. -/
theorem eq_exp_apply_add_integral_of_hasDerivAt
    (A : E →L[𝕜] E) {u f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt u (A (u t) + f t) t) :
    u b = exp ((b - a) • A) (u a) +
      ∫ s in a..b, exp ((b - s) • A) (f s) := by
  have he : Continuous (fun s : ℝ ↦ exp ((b - s) • A)) :=
    exp_continuous.comp ((continuous_const.sub continuous_id).smul continuous_const)
  have huc : ContinuousOn (fun s : ℝ ↦ exp ((b - s) • A) (u s)) (Icc a b) :=
    he.continuousOn.clm_apply hu
  have hfc : ContinuousOn (fun s : ℝ ↦ exp ((b - s) • A) (f s)) (Icc a b) :=
    he.continuousOn.clm_apply hf
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab huc
    (fun t ht ↦ hasDerivAt_exp_sub_apply A (hd t ht) b)
    (hfc.intervalIntegrable_of_Icc hab)
  simpa only [sub_self, zero_smul, exp_zero, one_apply_eq_self] using
    (eq_add_of_sub_eq h.symm).trans (add_comm _ _)

end PDE.Analysis.Evolution
