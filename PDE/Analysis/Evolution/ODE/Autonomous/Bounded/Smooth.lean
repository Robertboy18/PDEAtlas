/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Bounded.Flow
public import PDE.Analysis.ODE.SmoothDependence.RegularityTransfer

/-!
# Smooth global flows of bounded autonomous fields

A bounded smooth vector field on a finite-dimensional real normed space generates
one flow for all real times. Its dependence on time and initial state is jointly
smooth: on each finite open time interval, regularity transfers to the global
flow from local solution families. The bounded-flow construction supplies the
flow laws and the ordinary time derivative.
-/

@[expose] public noncomputable section

open Metric Set
open scoped ContDiff NNReal Topology

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A globally bounded smooth autonomous vector field on a finite-dimensional
real normed space generates a flow that is jointly smooth in time and initial
state. Every trajectory has ordinary time derivative equal to the vector field
along that trajectory, for all real times. -/
theorem exists_contDiff_infty_flow_hasDerivAt_of_bounded
    {F : E → E} (hF : ContDiff ℝ ∞ F) {M : ℝ≥0}
    (hbound : ∀ x, ‖F x‖ ≤ M) :
    ∃ Φ : Flow ℝ E,
      ContDiff ℝ ∞ (fun p : ℝ × E ↦ Φ p.1 p.2) ∧
      ∀ x t, HasDerivAt (fun s ↦ Φ s x) (F (Φ t x)) t := by
  have hF₁ : ContDiff ℝ 1 F := hF.of_le (by simp)
  have hLip (R : ℝ) (_hR : 0 < R) :
      ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R) :=
    hF₁.contDiffOn.exists_lipschitzOnWith one_ne_zero
      (convex_closedBall 0 R) (isCompact_closedBall 0 R)
  obtain ⟨Φ, hΦ⟩ := exists_flow_hasDerivAt_of_bounded hbound hLip
  have hflow : ContDiff ℝ ∞ (fun p : E × ℝ ↦ Φ p.2 p.1) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    have hT : 0 < |p.2| + 1 :=
      add_pos_of_nonneg_of_pos (abs_nonneg p.2) zero_lt_one
    have ht : p.2 ∈ Ioo (-(|p.2| + 1)) (|p.2| + 1) :=
      abs_lt.mp (lt_add_one |p.2|)
    have hreg : ContDiffOn ℝ ∞ (fun q : E × ℝ ↦ Φ q.2 q.1)
        (univ ×ˢ Ioo (-(|p.2| + 1)) (|p.2| + 1)) :=
      PDE.Analysis.ODE.contDiffOn_infty_of_solution_family F hF
        (fun q : E × ℝ ↦ Φ q.2 q.1) univ isOpen_univ hT
        (fun q _ ↦ Φ.map_zero_apply q) (fun q _ t _ ↦ hΦ q t)
    exact hreg.contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ p.1, ht⟩)
  have hswap : ContDiff ℝ ∞ (fun p : ℝ × E ↦ (p.2, p.1)) :=
    contDiff_snd.prodMk contDiff_fst
  exact ⟨Φ, hflow.comp hswap, hΦ⟩

end PDE.Analysis.Evolution
