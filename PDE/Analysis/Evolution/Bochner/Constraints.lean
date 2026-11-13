/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.WeakConstraints
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Linear constraints on Bochner L² trajectories

A continuous linear spatial constraint lifts pointwise to a continuous linear
map on Bochner `L²`. Its kernel is the corresponding almost-everywhere
constraint, so the constrained trajectories form a weakly closed set, weak
limits of constrained sequences stay constrained, and bounded constrained sets
are weakly compact.

The results apply uniformly to divergence-free, zero-mean, trace,
conservation, and other continuous linear side conditions.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal BoundedContinuousFunction

namespace PDE.Analysis.Evolution

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every member of a family of spatial linear constraints holds almost
everywhere along a Bochner trajectory. -/
def SatisfiesBochnerConstraints {J : Type*}
    (A : J → E →L[ℝ] F) (u : Lp E 2 μ) : Prop :=
  ∀ j, ∀ᵐ t ∂μ, A j (u t) = 0

/-- A lifted continuous linear map vanishes in Bochner `L²` exactly when its
pointwise values vanish almost everywhere. -/
theorem compLpL_eq_zero_iff_ae
    (A : E →L[ℝ] F) (u : Lp E 2 μ) :
    A.compLpL 2 μ u = 0 ↔ ∀ᵐ t ∂μ, A (u t) = 0 := by
  constructor
  · intro h
    filter_upwards [A.coeFn_compLpL u, Lp.coeFn_zero F 2 μ] with t hA hzero
    have ht :
        (A.compLpL 2 μ u : α → F) t =
          (0 : Lp F 2 μ) t := by
      rw [h]
    rw [hA, hzero] at ht
    exact ht
  · intro h
    apply Lp.ext
    filter_upwards [
      A.coeFn_compLpL u, Lp.coeFn_zero F 2 μ, h] with t hA hzero ht
    rw [hA, hzero]
    exact ht

/-- Almost-everywhere satisfaction of a family of spatial constraints is
equivalent to simultaneous vanishing of all lifted Bochner maps. -/
theorem satisfiesBochnerConstraints_iff_compLpL_eq_zero
    {J : Type*} (A : J → E →L[ℝ] F) (u : Lp E 2 μ) :
    SatisfiesBochnerConstraints A u ↔
      ∀ j, (A j).compLpL 2 μ u = 0 := by
  simp only [SatisfiesBochnerConstraints, compLpL_eq_zero_iff_ae]

/-- The weak-space set of Bochner trajectories satisfying every spatial
linear constraint almost everywhere. -/
def bochnerWeakConstraintSet {J : Type*}
    (A : J → E →L[ℝ] F) :
    Set (WeakSpace ℝ (Lp E 2 μ)) :=
  weakConstraintSet fun j ↦ (A j).compLpL 2 μ

/-- Membership in the Bochner weak constraint set is exactly the
almost-everywhere spatial constraint. -/
@[simp]
theorem toWeakSpace_mem_bochnerWeakConstraintSet
    {J : Type*} (A : J → E →L[ℝ] F) (u : Lp E 2 μ) :
    toWeakSpace ℝ (Lp E 2 μ) u ∈ bochnerWeakConstraintSet A ↔
      SatisfiesBochnerConstraints A u := by
  rw [bochnerWeakConstraintSet, toWeakSpace_mem_weakConstraintSet]
  exact (satisfiesBochnerConstraints_iff_compLpL_eq_zero A u).symm

/-- Almost-everywhere spatial linear constraints cut out a weakly closed
subset of Bochner `L²`. -/
theorem isClosed_bochnerWeakConstraintSet
    {J : Type*} (A : J → E →L[ℝ] F) :
    IsClosed (bochnerWeakConstraintSet (μ := μ) A) := by
  exact isClosed_weakConstraintSet fun j ↦ (A j).compLpL 2 μ

/-- Almost-everywhere spatial linear constraints are preserved by weak
Bochner `L²` limits. -/
theorem satisfiesBochnerConstraints_of_tendsto_weak
    {J ι : Type*} {l : Filter ι} [l.NeBot]
    (A : J → E →L[ℝ] F)
    {u : ι → Lp E 2 μ} {uLimit : Lp E 2 μ}
    (hu : Filter.Tendsto
      (fun i ↦ toWeakSpace ℝ (Lp E 2 μ) (u i)) l
      (nhds (toWeakSpace ℝ (Lp E 2 μ) uLimit)))
    (hA : ∀ᶠ i in l, SatisfiesBochnerConstraints A (u i)) :
    SatisfiesBochnerConstraints A uLimit := by
  have hLifted :
      ∀ᶠ i in l, ∀ j, (A j).compLpL 2 μ (u i) = 0 :=
    hA.mono fun i hi ↦
      (satisfiesBochnerConstraints_iff_compLpL_eq_zero A (u i)).1 hi
  have hLimit :
      ∀ j, (A j).compLpL 2 μ uLimit = 0 :=
    constraints_eq_zero_of_tendsto_weak
      (fun j ↦ (A j).compLpL 2 μ) hu hLifted
  exact
    (satisfiesBochnerConstraints_iff_compLpL_eq_zero A uLimit).2 hLimit

/-- Intersecting a weakly closed, norm-bounded Bochner `L²` set with
almost-everywhere spatial linear constraints preserves weak compactness. -/
theorem WeakCompactness.isCompact_inter_bochnerWeakConstraintSet
    {H K J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (A : J → H →L[ℝ] K)
    {S : Set (WeakSpace ℝ (Lp H 2 μ))}
    (hSclosed : IsClosed S)
    (hSbounded :
      Bornology.IsBounded
        ((toWeakSpace ℝ (Lp H 2 μ)) ⁻¹' S)) :
    IsCompact (S ∩ bochnerWeakConstraintSet (μ := μ) A) := by
  exact
    PDE.Analysis.WeakCompactness.isCompact_inter_weakConstraintSet
      (fun j ↦ (A j).compLpL 2 μ) hSclosed hSbounded

end PDE.Analysis.Evolution
