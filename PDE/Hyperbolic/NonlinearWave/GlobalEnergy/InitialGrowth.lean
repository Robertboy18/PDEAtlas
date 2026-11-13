/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Deriv.RightGrowth
public import PDE.Hyperbolic.Models.Wave.Equation
import PDE.FDeriv.SpaceTime

/-!
# Reaction growth detected by an initial velocity

A positive initial velocity at zero displacement forces linear growth of the
reaction on the positive side. Only the forward equation is used.
-/

@[expose] public noncomputable section

open Filter Set PDE PDE.Common
open scoped Topology

namespace WaveEquation

/-- A positive velocity at zero initial displacement forces a right-sided
linear reaction bound. The equation is required only on the right time germ. -/
theorem isBigO_reaction_right_of_pos_initial_velocity {n : ℕ} {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {x : ℝ^n} (hfzero : f 0 = 0) (hu : ContDiffAt ℝ 3 u (timeSpaceCons 0 x))
    (hwave : ∀ᶠ t in 𝓝[≥] (0 : ℝ),
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hzero : u (timeSpaceCons 0 x) = 0) (hvel : 0 < (∂[0] u) (timeSpaceCons 0 x)) :
    f =O[𝓝[≥] 0] (fun z : ℝ ↦ z) := by
  have hsecond (i : Fin (n + 1)) : ContDiffAt ℝ 1 (∂[i] (∂[i] u)) (timeSpaceCons 0 x) :=
    (hu.partialDeriv i (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)).partialDeriv i le_rfl
  have hop : ContDiffAt ℝ 1 (waveOperator u) (timeSpaceCons 0 x) :=
    (hsecond 0).sub (ContDiffAt.sum fun i _ ↦ hsecond i.succ)
  have hpath : ContDiff ℝ 1 (fun t ↦ timeSpaceCons t x) :=
    (contDiff_timeSpaceCons_uncurry n).comp (contDiff_id.prodMk contDiff_const)
  refine PDE.Analysis.isBigO_right_of_comp_of_deriv_pos
    ((hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).comp 0 hpath.contDiffAt) hzero ?_ hfzero ?_
  · change 0 < deriv (fun t ↦ u (timeSpaceCons t x)) 0
    rw [← partialDeriv_timeSpaceCons_eq_deriv u x 0
      (hu.differentiableAt (by norm_num))]
    exact hvel
  · have hd := ((hop.neg.comp 0 hpath.contDiffAt).differentiableAt
      one_ne_zero).differentiableWithinAt (s := Ici 0)
    apply hd.congr_of_eventuallyEq
    · exact hwave.mono fun t ht ↦ eq_neg_of_add_eq_zero_right ht
    · simpa only [Function.comp_apply] using
        eq_neg_of_add_eq_zero_right (hwave.self_of_nhdsWithin (show (0 : ℝ) ∈ Ici 0 from le_rfl))

end WaveEquation
