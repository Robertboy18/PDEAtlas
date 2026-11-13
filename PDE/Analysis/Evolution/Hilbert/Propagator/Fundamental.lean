/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Hilbert.Propagator.Envelope
public import PDE.Analysis.Evolution.ODE.Linear.Fundamental

/-!
# Norm bounds for constructed Hilbert-space propagators

A quadratic-form estimate on the time-dependent coefficient controls the operator norm
of its two-time propagator. The compact-interval endpoint applies this estimate to the
fundamental paths constructed by Picard iteration, so no propagator or inverse is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The homogeneous propagator is bounded by the exponential of the integrated
quadratic-form bound, even when that bound is negative. -/
theorem FundamentalSolution.norm_propagator_le_exp_integral
    {B : ℝ → H →L[ℝ] H} {t₀ : ℝ} (S : FundamentalSolution B t₀)
    {s t : ℝ} (hst : s ≤ t) {growth : ℝ → ℝ}
    (hg : ContinuousOn growth (Icc s t))
    (hB : ∀ r ∈ Ico s t, ∀ x : H, ⟪x, B r x⟫ ≤ growth r * ‖x‖ ^ 2) :
    ‖S.propagator t s‖ ≤ Real.exp (∫ r in s..t, growth r) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le
  intro x
  have hu : Continuous (fun r ↦ S.propagator r s x) :=
    (S.continuous_propagator.comp
      (continuous_id.prodMk continuous_const)).clm_apply continuous_const
  have hd (r : ℝ) (_hr : r ∈ Ico s t) :
      HasDerivWithinAt (fun r ↦ S.propagator r s x)
        (B r (S.propagator r s x) + (0 : H)) (Ici r) r := by
    simpa only [mul_apply_eq_comp, add_zero, map_zero] using
      ((S.hasDerivAt_propagator r s).clm_apply (hasDerivAt_const r x)).hasDerivWithinAt
  have h := norm_le_exp_integral_mul B hg hu.continuousOn
    (f := fun _ ↦ (0 : H)) continuousOn_const hd hB t ⟨hst, le_rfl⟩
  simpa only [S.propagator_self, one_apply_eq_self, norm_zero, mul_zero,
    intervalIntegral.integral_zero, add_zero] using h

/-- Raw continuous compact-interval coefficients produce a propagator with the
quadratic-form exponential bound. There is no dimension or interval-length restriction. -/
theorem norm_fundamentalSolutionOn_propagator_le [CompleteSpace H]
    {a b : ℝ} (B : C(Icc a b, H →L[ℝ] H)) (t₀ s t : Icc a b) (hst : s ≤ t)
    {growth : ℝ → ℝ} (hg : ContinuousOn growth (Icc a b))
    (hB : ∀ r : Icc a b, ∀ x : H, ⟪x, B r x⟫ ≤ growth r * ‖x‖ ^ 2) :
    ‖(fundamentalSolutionOn B t₀).propagator t s‖ ≤
      Real.exp (∫ r in s.1..t.1, growth r) := by
  apply FundamentalSolution.norm_propagator_le_exp_integral _ hst
    (hg.mono (Icc_subset_Icc s.2.1 t.2.2))
  intro r hr x
  have hrI : r ∈ Icc a b := ⟨s.2.1.trans hr.1, hr.2.le.trans t.2.2⟩
  simpa only [IccExtend_of_mem _ B hrI] using hB ⟨r, hrI⟩ x

end PDE.Analysis.Evolution
