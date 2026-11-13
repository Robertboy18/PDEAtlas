/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Interval

/-!
# Classical trajectories from an arbitrary time anchor

A solution of a forced linear equation equals the propagator formula
through its value at any time in the closed interval. The integral retains its
orientation, so the same result applies to a right endpoint anchor. Continuity
at the endpoints and the differential equation in the interior suffice.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution.FundamentalSolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A : ℝ → E →L[ℝ] E} {t₀ a b : ℝ}

/-- A classical trajectory has Duhamel's formula through any anchor in its closed
interval, in either time direction. The same supplied fundamental solution is
used throughout. Its normalization time need not equal the data anchor. -/
theorem eq_propagator_add_integral_of_hasDerivWithinAt
    (S : FundamentalSolution A t₀ (Icc a b)) {z r : ℝ → E}
    (hz : ContinuousOn z (Icc a b)) (hr : ContinuousOn r (Icc a b))
    (hode : ∀ s ∈ Ioo a b,
      HasDerivWithinAt z (A s (z s) + r s) (Icc a b) s)
    {c t : ℝ} (hc : c ∈ Icc a b) (ht : t ∈ Icc a b) :
    z t = S.propagator t c (z c) + ∫ s in c..t, S.propagator t s (r s) := by
  have hsub : uIcc c t ⊆ Icc a b := uIcc_subset_Icc hc ht
  have hq : ContinuousOn (fun s ↦ S.backward s (r s)) (uIcc c t) :=
    (S.continuousOn_backward.clm_apply hr).mono hsub
  have hv : ContinuousOn (fun s ↦ S.backward s (z s)) (uIcc c t) :=
    (S.continuousOn_backward.clm_apply hz).mono hsub
  -- Every interior point between the data and evaluation times is inside the slab.
  have hvd (s : ℝ) (hs : s ∈ Ioo (min c t) (max c t)) :
      HasDerivAt (fun u ↦ S.backward u (z u)) (S.backward s (r s)) s := by
    have hs' : s ∈ Ioo a b :=
      ⟨lt_of_le_of_lt (le_min hc.1 ht.1) hs.1,
        lt_of_lt_of_le hs.2 (max_le hc.2 ht.2)⟩
    have hzd := (hode s hs').hasDerivAt (Icc_mem_nhds hs'.1 hs'.2)
    have hbd := (S.backward_hasDerivWithinAt s (Ioo_subset_Icc_self hs')).hasDerivAt
      (Icc_mem_nhds hs'.1 hs'.2)
    simpa only [neg_apply, mul_apply_eq_comp, map_add, neg_add_cancel_left] using
      hbd.clm_apply hzd
  have hint :
      ∫ s in c..t, S.backward s (r s) =
        S.backward t (z t) - S.backward c (z c) :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right hv
      (fun s hs ↦ (hvd s hs).hasDerivWithinAt) hq.intervalIntegrable
  calc
    z t = S.forward t (S.backward t (z t)) := by
      rw [← mul_apply_eq_comp, S.forward_mul_backward t ht]
      rfl
    _ = S.solution r c (z c) t := by
      rw [solution, hint, add_comm (S.backward c (z c)), sub_add_cancel]
    _ = S.propagator t c (z c) + ∫ s in c..t, S.propagator t s (r s) :=
      S.solution_eq_propagator_add_integral_on hr hc ht (z c)

end PDE.Analysis.Evolution.FundamentalSolution
