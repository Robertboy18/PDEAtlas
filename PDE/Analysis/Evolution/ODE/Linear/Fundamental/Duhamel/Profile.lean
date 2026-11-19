/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Duhamel

/-!
# Propagator bounds for a forced evolution

Bounds on the propagator and forcing transfer to the variation-of-constants
solution with their time dependence retained in the integral. In particular,
`‖U(t,s)‖ ≤ C g(t) / g(s)` and `‖f(s)‖ ≤ D g(s)` give a relative-profile bound.
The profile `g` need only be positive.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution.FundamentalSolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {B : ℝ → E →L[ℝ] E} {t₀ : ℝ} (S : FundamentalSolution B t₀)

/-- Propagator and forcing envelopes give an integral bound on the constructed
solution. Keeping both envelopes inside the integral preserves decay estimates. -/
theorem norm_solution_le_integral {f : ℝ → E} {a t : ℝ} (hat : a ≤ t)
    (hf : ContinuousOn f (Icc a t)) (x : E) {C ε : ℝ → ℝ}
    (hS : ∀ s ∈ Icc a t, ‖S.propagator t s‖ ≤ C s)
    (hfbound : ∀ s ∈ Icc a t, ‖f s‖ ≤ ε s)
    (hbound : IntervalIntegrable (fun s ↦ C s * ε s) volume a t) :
    ‖S.solution f a x t‖ ≤ C a * ‖x‖ + ∫ s in a..t, C s * ε s := by
  have hinit : ‖S.propagator t a x‖ ≤ C a * ‖x‖ :=
    ((S.propagator t a).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hS a ⟨le_rfl, hat⟩) (norm_nonneg _))
  have hint : ‖∫ s in a..t, S.propagator t s (f s)‖ ≤
      ∫ s in a..t, C s * ε s := by
    apply intervalIntegral.norm_integral_le_of_norm_le hat _ hbound
    refine Filter.Eventually.of_forall fun s hs ↦ ?_
    have hs' : s ∈ Icc a t := ⟨hs.1.le, hs.2⟩
    exact ((S.propagator t s).le_opNorm _).trans
      (mul_le_mul (hS s hs') (hfbound s hs') (norm_nonneg _)
        ((norm_nonneg _).trans (hS s hs')))
  have hq : IntervalIntegrable (fun s ↦ S.backward s (f s)) volume a t :=
    (S.continuous_backward.continuousOn.clm_apply hf).intervalIntegrable_of_Icc hat
  have heq : S.solution f a x t =
      S.propagator t a x + ∫ s in a..t, S.propagator t s (f s) := by
    simp only [solution, propagator, mul_apply_eq_comp, map_add]
    rw [(S.forward t).intervalIntegral_comp_comm hq]
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add hinit hint)

/-- A relative propagator profile controls the same constructed forced solution.
The forcing need only be continuous on the integration interval. -/
theorem norm_solution_le_profile {f : ℝ → E} {a t : ℝ} (hat : a ≤ t)
    (hf : ContinuousOn f (Icc a t)) (x : E) {g : ℝ → ℝ}
    (hg : ∀ s ∈ Icc a t, 0 < g s) (hga : g a = 1) {C D : ℝ}
    (hS : ∀ s ∈ Icc a t, ‖S.propagator t s‖ ≤ C * g t / g s)
    (hfbound : ∀ s ∈ Icc a t, ‖f s‖ ≤ D * g s) :
    ‖S.solution f a x t‖ ≤ C * g t * (‖x‖ + (t - a) * D) := by
  have hprod (s : ℝ) (hs : s ∈ Icc a t) :
      (C * g t / g s) * (D * g s) = C * g t * D := by
    field_simp [(hg s hs).ne']
  have hbound : IntervalIntegrable (fun s ↦ (C * g t / g s) * (D * g s)) volume a t :=
    intervalIntegrable_const.congr fun s hs ↦ by
      rw [uIoc_of_le hat] at hs
      exact (hprod s ⟨hs.1.le, hs.2⟩).symm
  have hint : (∫ s in a..t, (C * g t / g s) * (D * g s)) = C * g t * D * (t - a) := by
    rw [intervalIntegral.integral_congr (fun s hs ↦ hprod s (by
      rwa [uIcc_of_le hat] at hs))]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have h := S.norm_solution_le_integral hat hf x hS hfbound hbound
  rw [hga, div_one, hint] at h
  exact h.trans_eq (by ring)

end PDE.Analysis.Evolution.FundamentalSolution
