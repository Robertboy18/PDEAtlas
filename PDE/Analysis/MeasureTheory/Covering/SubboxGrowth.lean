/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
public import Mathlib.Analysis.BoxIntegral.Partition.Measure

/-!
# Measure growth by subbox induction

When a child box has high density of `E`, suppose its parent lies in `F`.
If `E` and the complement of `F` are locally separated, Mathlib's subbox
induction gives the measure-growth inequality directly. At a terminal box,
either the box lies in `F` or it misses `E`; at a split, either a dense child
puts the parent in `F`, or the child inequalities add.

The separation holds for two distinct levels of a continuous function.
The box family may carry any property preserved by center splitting, so the
result applies to cubes.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open BoxIntegral BoxIntegral.Prepartition MeasureTheory Set
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- A dense child forces its parent into `F`; center splitting then converts
an initial density bound into a measure comparison with `F`. -/
theorem measure_restrict_le_mul_of_subbox_parent
    (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ]
    (I : Box ι) {E F : Set (ι → ℝ)} {δ : ℝ} (hδ : 0 ≤ δ)
    (P : Box ι → Prop) (hPI : P I)
    (hPsplit : ∀ J ≤ I, P J → ∀ Q ∈ splitCenter J, P Q)
    (hparent : ∀ J ≤ I, P J → ∀ Q ∈ splitCenter J,
      δ * μ.real Q < (μ.restrict E).real Q → (J : Set (ι → ℝ)) ⊆ F)
    (hseparation : ∀ z ∈ I.Icc, ∃ U ∈ 𝓝[I.Icc] z, U ⊆ F ∨ Disjoint U E)
    (hsmall : (μ.restrict E).real I ≤ δ * μ.real I) :
    (μ.restrict E).real I ≤ δ * (μ.restrict F).real I := by
  classical
  have hsum (ν : Measure (ι → ℝ)) [IsLocallyFiniteMeasure ν] (J : Box ι) :
      ∑ Q ∈ (splitCenter J).boxes, ν.real Q = ν.real J :=
    ν.toBoxAdditive.sum_partition_boxes le_top (isPartition_splitCenter J)
  have hfull (J : Box ι) (hJ : (J : Set (ι → ℝ)) ⊆ F) :
      (μ.restrict F).real J = μ.real J := by
    simp only [measureReal_def, Measure.restrict_apply J.measurableSet_coe,
      inter_eq_left.mpr hJ]
  apply I.subbox_induction_on (p := fun J ↦ P J →
    (μ.restrict E).real J ≤ δ * μ.real J →
      (μ.restrict E).real J ≤ δ * (μ.restrict F).real J) ?_ ?_ hPI hsmall
  · intro J hJI hchildren hPJ hJsmall
    by_cases hdense : ∃ Q ∈ splitCenter J, δ * μ.real Q < (μ.restrict E).real Q
    · obtain ⟨Q, hQ, hdensity⟩ := hdense
      rw [hfull J (hparent J hJI hPJ Q hQ hdensity)]
      exact hJsmall
    · rw [← hsum (μ.restrict E) J, ← hsum (μ.restrict F) J, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro Q hQ
      have hQmem : Q ∈ splitCenter J := hQ
      exact hchildren Q hQmem (hPsplit J hJI hPJ Q hQmem)
        (le_of_not_gt (fun h ↦ hdense ⟨Q, hQmem, h⟩))
  · intro z hz
    obtain ⟨U, hU, hUF | hUE⟩ := hseparation z hz
    · refine ⟨U, hU, ?_⟩
      intro J _ _ _ hJU _ _ hJsmall
      rw [hfull J (Box.coe_subset_Icc.trans (hJU.trans hUF))]
      exact hJsmall
    · refine ⟨U, hU, ?_⟩
      intro J _ _ _ hJU _ _ _
      have hdisjoint : Disjoint (J : Set (ι → ℝ)) E :=
        hUE.mono_left (Box.coe_subset_Icc.trans hJU)
      rw [measureReal_def, Measure.restrict_apply J.measurableSet_coe,
        hdisjoint.inter_eq, measure_empty, ENNReal.toReal_zero]
      exact mul_nonneg hδ ENNReal.toReal_nonneg

omit [Fintype ι] in
/-- Distinct superlevels of a continuous function are locally separated on a
closed box. This supplies the terminal neighborhoods in subbox measure growth. -/
theorem superlevel_subbox_separation
    (I : Box ι) {u : (ι → ℝ) → ℝ} (hu : ContinuousOn u I.Icc)
    {s t : ℝ} (hst : s < t) :
    ∀ z ∈ I.Icc, ∃ U ∈ 𝓝[I.Icc] z,
      U ⊆ {x | s < u x} ∨ Disjoint U {x | t < u x} := by
  intro z hz
  by_cases hs : s < u z
  · have hmem : {x | s < u x} ∈ 𝓝[I.Icc] z :=
      hu z hz (Ioi_mem_nhds hs)
    exact ⟨{x | s < u x}, hmem, Or.inl Subset.rfl⟩
  · have ht : u z < t := (le_of_not_gt hs).trans_lt hst
    have hmem : {x | u x < t} ∈ 𝓝[I.Icc] z :=
      hu z hz (Iio_mem_nhds ht)
    refine ⟨{x | u x < t}, hmem, Or.inr ?_⟩
    apply disjoint_left.mpr
    intro x hx hxt
    have hx' : u x < t := hx
    have hxt' : t < u x := hxt
    exact (lt_irrefl (u x)) (lt_trans hx' hxt')

end PDE.Analysis
