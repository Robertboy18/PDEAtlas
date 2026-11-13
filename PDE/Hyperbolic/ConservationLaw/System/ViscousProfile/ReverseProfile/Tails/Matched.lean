/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Gate.Moments.Fixed

import PDE.Analysis.Evolution.ODE.Linear.Scalar.Constant
import CAS.ExactTactic

/-!
# The matched scalar candidate on the prescribed clock's late tail

One selected signed gate is normalized by the base lower weight. Its candidate is
exactly the supplied fast state times the scalar integrating-factor
solution with zero initial value. The time-integral identification is a hypothesis, given by the
branch-localization step.

The family equation supplies the fast derivative. Small support removes
forcing on the late interval, and the selected base moment fixes the tail value.
The conclusion concerns the scalar candidate, before any coupled-field agreement.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open PDE.Analysis.Evolution
open scoped BigOperators ContDiff

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- Tail propagation for the scalar formula. The anchor may lie anywhere
in the closed interval. The proof uses forward uniqueness from its left endpoint. -/
private theorem scalar_candidate_tail_of_forcing_zero
    {X Z b : ℝ → ℝ} {r τ H : ℝ}
    (hX : Continuous X) (hZ : Continuous Z) (hb : Continuous b)
    (hτ : τ ∈ Icc r H)
    (hfast : ∀ t ∈ Ioo r H, HasDerivAt Z (2 * Z t) t)
    (hzero : ∀ t ∈ Icc r H, b (X t) = 0) :
    let xhat : ℝ → ℝ := fun t ↦
      Z t * scalarLinearSolution (fun _ ↦ 4) (fun s ↦ b (X s)) 0 0 t
    ∀ t ∈ Icc r H, xhat t = xhat τ * Real.exp (2 * (τ - t)) := by
  dsimp only
  let R : ℝ → ℝ := scalarLinearSolution (fun _ ↦ 4) (fun s ↦ b (X s)) 0 0
  let xhat : ℝ → ℝ := fun t ↦ Z t * R t
  have hR (t : ℝ) : HasDerivAt R (b (X t) - 4 * R t) t :=
    hasDerivAt_scalarLinearSolution continuous_const (hb.comp hX) 0 0 t
  have hRcont : Continuous R :=
    continuous_iff_continuousAt.mpr (fun t ↦ (hR t).continuousAt)
  have hode (t : ℝ) (ht : t ∈ Ioo r H) :
      HasDerivAt xhat (-2 * xhat t + 0) t := by
    refine ((hfast t ht).fun_mul (hR t)).congr_deriv ?_
    rw [hzero t ⟨ht.1.le, ht.2.le⟩]
    ring
  have hdecay (t : ℝ) (ht : t ∈ Icc r H) :
      xhat t = Real.exp (-2 * (t - r)) * xhat r := by
    have heq := eq_scalarLinearSolution_const_of_hasDerivAt
      (r := xhat) (f := fun _ ↦ 0) (κ := 2) ht.1
      (hZ.mul hRcont).continuousOn continuousOn_const
      (fun s hs ↦ hode s ⟨hs.1, hs.2.trans_le ht.2⟩)
    rw [scalarLinearSolution_const_eq_exp_mul_add_integral] at heq
    simpa only [mul_zero, intervalIntegral.integral_zero, add_zero] using heq
  intro t ht
  change xhat t = xhat τ * Real.exp (2 * (τ - t))
  rw [hdecay t ht, hdecay τ hτ, mul_right_comm, ← Real.exp_add]
  ring_nf

/-- A fixed signed selection with normalized base moment one has the matched
late tail along the same supplied family. The integral hypothesis is the conclusion of branch
localization for this gate and these event maps. Only the base slice is matched. The full prescribed
family equation is retained on its original time slab. -/
theorem prescribed_clock_selected_matched_tail
    {F : ℝ × (ℝ × ℝ) → ℝ × ℝ} {L Bhit : ℝ × ℝ → ℝ}
    {N : Set (ℝ × ℝ)} {A B τ0 rDown H : ℝ}
    (hF : Continuous F) (hN : IsOpen N) (hbase : (0, 0) ∈ N)
    (hL : ContDiffOn ℝ ∞ L N) (hBhit : ContDiffOn ℝ ∞ Bhit N)
    (hode : ∀ p ∈ N, ∀ t ∈ Icc (-1 : ℝ) (τ0 + 1),
      HasDerivAt (fun s ↦ F (s, p)) (prescribedSpeedField A B (p.1, F (t, p))) t)
    (hLbase : L (0, 0) = τ0) (hrDown : 0 ≤ rDown) (hrτ : rDown < τ0)
    (hH : H ∈ Ioo τ0 (τ0 + 1))
    (hlate : ∀ t ∈ Icc rDown H, (F (t, (0, 0))).1 < 20501 / 100)
    (β : Fin 3 → ℝ → ℝ) (c v : Fin 3 → ℝ)
    (hβsmooth : ∀ j, ContDiff ℝ ∞ (β j))
    (hβcompact : ∀ j, HasCompactSupport (β j))
    (hβsupport : ∀ j, tsupport (β j) ⊆ Ioo (20501 / 100 : ℝ) (20509 / 100))
    (hβint :
      let D0 := parameterizedClockPassageData L Bhit (0, 0)
      ∀ j i : Fin 3, Integrable (fun y ↦ β j y * (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i))
    (hc :
      let D0 := parameterizedClockPassageData L Bhit (0, 0)
      (fun i : Fin 3 ↦ ∫ y, (∑ j, c j * β j y) *
        (![1, D0.R y, D0.Q y] : Fin 3 → ℝ) i) = v)
    (hv : v 0 + v 1 = 1) :
    let D0 := parameterizedClockPassageData L Bhit (0, 0)
    let b : ℝ → ℝ := (Ioo (205 : ℝ) (2051 / 10)).indicator
      (fun y ↦ (∑ j, c j * β j y) / D0.wMinus y)
    let xhat : ℝ → ℝ := fun t ↦ (F (t, (0, 0))).2 *
      scalarLinearSolution (fun _ ↦ 4) (fun s ↦ b ((F (s, (0, 0))).1)) 0 0 t
    (∫ t in (0 : ℝ)..L (0, 0),
      b ((F (t, (0, 0))).1) * Real.exp (-4 * (L (0, 0) - t))) =
        prescribedClockWeightMoment b L Bhit (0, 0) →
    EqOn xhat (fun t ↦ (F (τ0, (0, 0))).2 * Real.exp (2 * (τ0 - t)))
      (Icc rDown H) := by
  dsimp only
  intro hIntegral
  let D0 := parameterizedClockPassageData L Bhit (0, 0)
  let b : ℝ → ℝ := (Ioo (205 : ℝ) (2051 / 10)).indicator
    (fun y ↦ (∑ j, c j * β j y) / D0.wMinus y)
  let X : ℝ → ℝ := fun t ↦ (F (t, (0, 0))).1
  let Z : ℝ → ℝ := fun t ↦ (F (t, (0, 0))).2
  let xhat : ℝ → ℝ := fun t ↦
    Z t * scalarLinearSolution (fun _ ↦ 4) (fun s ↦ b (X s)) 0 0 t
  obtain ⟨hb, _hbcompact, _hbsupport, hbsmall, _hwb, _hInt, hmoment, _hμ, _ha⟩ :=
    prescribed_clock_fixed_gate_of_selected_moments L Bhit hN hbase hL hBhit
      β c v hβsmooth hβcompact hβsupport hβint hc
  have hmatch : prescribedClockWeightMoment b L Bhit (0, 0) = 1 := hmoment.trans hv
  change (∫ t in (0 : ℝ)..L (0, 0), b (X t) * Real.exp (-4 * (L (0, 0) - t))) =
    prescribedClockWeightMoment b L Bhit (0, 0) at hIntegral
  rw [hLbase] at hIntegral
  have hterminal : scalarLinearSolution (fun _ ↦ 4) (fun s ↦ b (X s)) 0 0 τ0 = 1 := by
    rw [scalarLinearSolution_const_eq_exp_mul_add_integral]
    simp only [mul_zero, zero_add]
    exact (intervalIntegral.integral_congr fun _ _ ↦ mul_comm _ _).trans (hIntegral.trans hmatch)
  have hxterminal : xhat τ0 = Z τ0 := by simp only [xhat, hterminal, mul_one]
  have hX : Continuous X := (hF.comp (continuous_id.prodMk continuous_const)).fst
  have hZ : Continuous Z := (hF.comp (continuous_id.prodMk continuous_const)).snd
  have hfast (t : ℝ) (ht : t ∈ Ioo rDown H) : HasDerivAt Z (2 * Z t) t :=
    hasDerivAt_prescribed_base_fast hbase hode
      ⟨(show (-1 : ℝ) ≤ rDown by linarith).trans ht.1.le, ht.2.le.trans hH.2.le⟩
  have hzero (t : ℝ) (ht : t ∈ Icc rDown H) : b (X t) = 0 := Function.notMem_support.mp fun hn ↦
    (not_lt_of_ge (hlate t ht).le) (hbsmall (subset_tsupport b hn)).1
  have htail := scalar_candidate_tail_of_forcing_zero hX hZ hb.continuous
    ⟨hrτ.le, hH.1.le⟩ hfast hzero
  intro t ht
  change xhat t = Z τ0 * Real.exp (2 * (τ0 - t))
  rw [← hxterminal]
  exact htail t ht

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
