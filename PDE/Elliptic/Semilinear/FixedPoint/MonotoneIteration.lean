/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.FixedPoint.Contraction
import PDE.Analysis.Order.MonotoneIteration

/-!
# Monotone iteration for semilinear variational equations

Let `B` be coercive and let `N u` be a nonlinear dual load. The weak equation

`B u v + N u v = ell v`

is equivalent to the fixed-point equation

`u = semilinearPicardMap B hB N ell u`.

Limits of lower and upper Picard iterates are the least and greatest weak
solutions in an invariant order interval, and these extremal solutions exist
when the corresponding orbit is contained in a compact set. The order and
monotonicity hypotheses remain
explicit; Hilbert-space completeness alone does not imply convergence of a
monotone orbit.
-/

@[expose] public section

noncomputable section

open Filter Function Set
open scoped Topology

namespace SobolevSpace.Weak

open PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

/-- Continuity of the nonlinear load implies continuity of the semilinear
Picard map. -/
theorem continuous_semilinearPicardMap
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) (hN : Continuous N)
    (ell : StrongDual ℝ V) :
    Continuous (semilinearPicardMap B hB N ell) := by
  change Continuous (fun u ↦ solveCLM (V := V) B hB (ell - N u))
  have hload : Continuous (fun u ↦ ell - N u) :=
    continuous_const.sub hN
  exact (solveCLM (V := V) B hB).continuous.comp hload

/-- The limit of the lower Picard iterates is the least semilinear weak
solution in the invariant interval. -/
theorem isLeast_semilinear_weak_solution_Icc_of_tendsto_iterate
    [PartialOrder V] [OrderClosedTopology V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) (hN : Continuous N)
    (ell : StrongDual ℝ V)
    {lower upper u : V} (hlowerupper : lower ≤ upper)
    (hmono : Monotone (semilinearPicardMap B hB N ell))
    (hlower : lower ≤ semilinearPicardMap B hB N ell lower)
    (hupper : semilinearPicardMap B hB N ell upper ≤ upper)
    (hu : Tendsto
      (fun n : ℕ ↦ (semilinearPicardMap B hB N ell)^[n] lower)
      atTop (𝓝 u)) :
    IsLeast
      {w | w ∈ Icc lower upper ∧ ∀ v, B w v + N w v = ell v}
      u := by
  have hleast :=
    PDE.OrderInterval.isLeast_fixedPoint_Icc_of_tendsto_iterate
      (semilinearPicardMap B hB N ell) hmono
      hlowerupper hlower hupper
      (continuous_semilinearPicardMap B hB N hN ell).continuousAt hu
  refine ⟨⟨hleast.1.1, ?_⟩, ?_⟩
  · exact
      (isFixedPt_semilinearPicardMap_iff B hB N ell u).mp
        hleast.1.2
  · intro w hw
    apply hleast.2
    exact
      ⟨hw.1,
        (isFixedPt_semilinearPicardMap_iff B hB N ell w).mpr hw.2⟩

/-- The limit of the upper Picard iterates is the greatest semilinear weak
solution in the invariant interval. -/
theorem isGreatest_semilinear_weak_solution_Icc_of_tendsto_iterate
    [PartialOrder V] [OrderClosedTopology V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) (hN : Continuous N)
    (ell : StrongDual ℝ V)
    {lower upper u : V} (hlowerupper : lower ≤ upper)
    (hmono : Monotone (semilinearPicardMap B hB N ell))
    (hlower : lower ≤ semilinearPicardMap B hB N ell lower)
    (hupper : semilinearPicardMap B hB N ell upper ≤ upper)
    (hu : Tendsto
      (fun n : ℕ ↦ (semilinearPicardMap B hB N ell)^[n] upper)
      atTop (𝓝 u)) :
    IsGreatest
      {w | w ∈ Icc lower upper ∧ ∀ v, B w v + N w v = ell v}
      u := by
  have hgreatest :=
    PDE.OrderInterval.isGreatest_fixedPoint_Icc_of_tendsto_iterate
      (semilinearPicardMap B hB N ell) hmono
      hlowerupper hlower hupper
      (continuous_semilinearPicardMap B hB N hN ell).continuousAt hu
  refine ⟨⟨hgreatest.1.1, ?_⟩, ?_⟩
  · exact
      (isFixedPt_semilinearPicardMap_iff B hB N ell u).mp
        hgreatest.1.2
  · intro w hw
    apply hgreatest.2
    exact
      ⟨hw.1,
        (isFixedPt_semilinearPicardMap_iff B hB N ell w).mpr hw.2⟩

/-- Compactness of the lower Picard orbit produces the least semilinear weak
solution in the invariant interval. -/
theorem exists_least_semilinear_weak_solution_Icc_of_compact_iterates
    [PartialOrder V] [OrderClosedTopology V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) (hN : Continuous N)
    (ell : StrongDual ℝ V)
    {lower upper : V} (hlowerupper : lower ≤ upper)
    (hmono : Monotone (semilinearPicardMap B hB N ell))
    (hlower : lower ≤ semilinearPicardMap B hB N ell lower)
    (hupper : semilinearPicardMap B hB N ell upper ≤ upper)
    {K : Set V} (hK : IsCompact K)
    (hiterates :
      ∀ n : ℕ, (semilinearPicardMap B hB N ell)^[n] lower ∈ K) :
    ∃ u ∈ K,
      IsLeast
        {w | w ∈ Icc lower upper ∧ ∀ v, B w v + N w v = ell v}
        u := by
  obtain ⟨u, huK, hu⟩ :=
    PDE.OrderInterval.exists_tendsto_of_monotone_of_isCompact
      (hmono.monotone_iterate_of_le_map hlower) hK hiterates
  exact
    ⟨u, huK,
      isLeast_semilinear_weak_solution_Icc_of_tendsto_iterate
        B hB N hN ell hlowerupper hmono hlower hupper hu⟩

/-- Compactness of the upper Picard orbit produces the greatest semilinear
weak solution in the invariant interval. -/
theorem exists_greatest_semilinear_weak_solution_Icc_of_compact_iterates
    [PartialOrder V] [OrderClosedTopology V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : IsCoercive B)
    (N : V → StrongDual ℝ V) (hN : Continuous N)
    (ell : StrongDual ℝ V)
    {lower upper : V} (hlowerupper : lower ≤ upper)
    (hmono : Monotone (semilinearPicardMap B hB N ell))
    (hlower : lower ≤ semilinearPicardMap B hB N ell lower)
    (hupper : semilinearPicardMap B hB N ell upper ≤ upper)
    {K : Set V} (hK : IsCompact K)
    (hiterates :
      ∀ n : ℕ, (semilinearPicardMap B hB N ell)^[n] upper ∈ K) :
    ∃ u ∈ K,
      IsGreatest
        {w | w ∈ Icc lower upper ∧ ∀ v, B w v + N w v = ell v}
        u := by
  obtain ⟨u, huK, hu⟩ :=
    PDE.OrderInterval.exists_tendsto_of_antitone_of_isCompact
      (hmono.antitone_iterate_of_map_le hupper) hK hiterates
  exact
    ⟨u, huK,
      isGreatest_semilinear_weak_solution_Icc_of_tendsto_iterate
        B hB N hN ell hlowerupper hmono hlower hupper hu⟩

end SobolevSpace.Weak
