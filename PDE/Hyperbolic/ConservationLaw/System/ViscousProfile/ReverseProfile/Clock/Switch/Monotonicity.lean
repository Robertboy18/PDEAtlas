/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.FastLogCosh

/-!
# Squared-state monotonicity of the fast clock

For every admissible log-cosh parameter, the fast equation and the
lower bound `1 + t ≤ Z t` imply that the squared fast state is strictly increasing
on nonnegative times. Both clock branches can use this fact independently
of any middle-coordinate trajectory or prescribed lower equation.
-/

@[expose] public noncomputable section

open Set
open PDE.Analysis

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.ClockSwitch

/-- The fast clock has strictly increasing squared states on nonnegative times,
for every admissible parameter. -/
theorem strictMonoOn_fast_clock_sq {δ : ℝ} {Z : ℝ → ℝ} (hδ : |δ| < 1 / 4)
    (hZ : ∀ t, HasDerivAt Z (fastLogCosh δ (Z t)) t) (hZlower : ∀ t, 0 ≤ t → 1 + t ≤ Z t) :
    StrictMonoOn (fun t ↦ Z t ^ 2) (Ici 0) := by
  have hk : StrictMono (fastLogCosh δ) :=
    strictMono_of_deriv_pos fun z ↦ by
      linarith only [seven_fourths_lt_deriv_fastLogCosh hδ z]
  have hkzero : fastLogCosh δ 0 = 0 := by simp [fastLogCosh]
  have hZd : Differentiable ℝ Z := fun t ↦ (hZ t).differentiableAt
  have hmono : StrictMonoOn Z (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ)) hZd.continuous.continuousOn fun t ht ↦ ?_
    have ht0 : 0 ≤ t := interior_subset ht
    have hz0 : 0 < Z t := by linarith only [hZlower t ht0, ht0]
    rw [(hZ t).deriv, ← hkzero]
    exact hk hz0
  intro s hs t ht hst
  have horder := hmono hs ht hst
  have hs0 : 0 ≤ Z s := by linarith only [hZlower s hs, show 0 ≤ s from hs]
  have ht0 : 0 ≤ Z t := by linarith only [hZlower t ht, show 0 ≤ t from ht]
  exact (sq_lt_sq₀ hs0 ht0).2 horder

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.ClockSwitch
