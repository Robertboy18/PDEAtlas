/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental

import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Duhamel.Identification

/-!
# Independence of the propagator from the fundamental solution

Two supplied fundamental solutions of the same operator equation induce the
same propagator on a closed interval, even when normalized at different times.
The proof applies oriented Duhamel identification to a homogeneous column.
-/

@[expose] public section

open Set

namespace PDE.Analysis.Evolution.FundamentalSolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A : ℝ → E →L[ℝ] E} {s₀ t₀ a b : ℝ}

/-- Fundamental solutions with possibly different normalization times induce the
same propagator between any two points of their common closed interval. The
coefficient need not be continuous. -/
theorem propagator_eq_on_Icc
    (S : FundamentalSolution A s₀ (Icc a b))
    (T : FundamentalSolution A t₀ (Icc a b))
    {c t : ℝ} (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    S.propagator t c = T.propagator t c := by
  apply ContinuousLinearMap.ext
  intro x
  have hcolumn (s : ℝ) (hs : s ∈ Icc a b) :
      HasDerivWithinAt (fun u ↦ T.propagator u c x)
        (A s (T.propagator s c x)) (Icc a b) s := by
    simpa only [mul_apply_eq_comp, map_zero, add_zero] using
      (T.hasDerivWithinAt_propagator hs c).clm_apply
        (hasDerivWithinAt_const s (Icc a b) x)
  have h := S.eq_propagator_add_integral_of_hasDerivWithinAt
    (z := fun s ↦ T.propagator s c x) (r := fun _ ↦ (0 : E))
    (fun s hs ↦ (hcolumn s hs).continuousWithinAt)
    continuousOn_const
    (fun s hs ↦ by
      simpa only [add_zero] using hcolumn s (Ioo_subset_Icc_self hs))
    hc ht
  simpa only [T.propagator_self_of_mem hc, one_apply_eq_self,
    map_zero, intervalIntegral.integral_zero, add_zero] using h.symm

end PDE.Analysis.Evolution.FundamentalSolution
