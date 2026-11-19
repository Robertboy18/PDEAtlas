/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.JointContinuity

/-!
# Joint continuity of a gaining kernel

A kernel from a weaker space to a Banach space is jointly continuous at positive
times if, after any fixed positive gaining step, it evolves by a strongly
continuous semigroup. No continuity in operator norm is required.
-/

@[expose] public section

open Filter Set Topology

namespace PDE.Analysis.Evolution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A positive gaining step followed by a strongly continuous semigroup gives
joint continuity in the lag and input vector. -/
theorem continuousOn_kernel_apply_of_semigroup_factor
    (T : StronglyContinuousSemigroup E) (K : ℝ → F →L[ℝ] E)
    (hfactor : ∀ c r, 0 < c → c < r → ∀ u, K r u = T (r - c).toNNReal (K c u)) :
    ContinuousOn (fun p : ℝ × F ↦ K p.1 p.2) (Ioi 0 ×ˢ univ) := by
  intro p hp
  let c := p.1 / 2
  have hc : 0 < c := half_pos hp.1
  have hcp : c < p.1 := half_lt_self hp.1
  have hcont : Continuous (fun q : ℝ × F ↦ T (q.1 - c).toNNReal (K c q.2)) :=
    T.continuous_apply.comp
      ((continuous_real_toNNReal.comp (continuous_fst.sub continuous_const)).prodMk
        ((K c).continuous.comp continuous_snd))
  apply ContinuousAt.continuousWithinAt
  apply hcont.continuousAt.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.eventually (lt_mem_nhds hcp)] with q hq
  exact hfactor c q.1 hc hq q.2

end PDE.Analysis.Evolution
