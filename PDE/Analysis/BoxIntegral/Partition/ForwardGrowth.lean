/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.BoxIntegral.Box.ForwardExtension
public import PDE.Analysis.BoxIntegral.Partition.Stopping
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Measure growth from a finite forward cover

A prepartition covering the part of a set inside a box converts density bounds
on its disjoint members into a bound by the volume of their union. If their
forward extensions lie in a second set, the forward-cover estimate gives a
measure comparison without requiring the extensions to remain in the root box.
-/

@[expose] public noncomputable section

namespace BoxIntegral.Prepartition

open Set MeasureTheory
open scoped ENNReal Topology

variable {ι : Type*} [Finite ι]

/-- A cover by disjoint subboxes of density at most `δ` bounds the measure of
`E` inside the root box by `δ` times the measure of the cover. -/
theorem measure_restrict_le_mul_iUnion
    (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ]
    {I : Box ι} (π : Prepartition I) {E : Set (ι → ℝ)} {δ : ℝ}
    (hcover : E ∩ (I : Set (ι → ℝ)) ⊆ π.iUnion)
    (hsmall : ∀ J ∈ π, (μ.restrict E).real J ≤ δ * μ.real J) :
    (μ.restrict E).real I ≤ δ * μ.real π.iUnion := by
  have hmeas : MeasurableSet π.iUnion :=
    π.boxes.finite_toSet.measurableSet_biUnion fun J _ ↦ J.measurableSet_coe
  have hfinite : μ (π.iUnion ∩ E) ≠ ∞ :=
    (measure_mono (inter_subset_left.trans π.iUnion_subset) |>.trans_lt
      (I.measure_coe_lt_top μ)).ne
  calc
    (μ.restrict E).real I ≤ (μ.restrict E).real π.iUnion := by
      rw [measureReal_restrict_apply I.measurableSet_coe,
        measureReal_restrict_apply hmeas]
      exact measureReal_mono
        (fun _ hx ↦ ⟨hcover ⟨hx.2, hx.1⟩, hx.2⟩) hfinite
    _ = ∑ J ∈ π.boxes, (μ.restrict E).real J := π.measure_iUnion_toReal _
    _ ≤ ∑ J ∈ π.boxes, δ * μ.real J :=
      Finset.sum_le_sum fun J hJ ↦ hsmall J hJ
    _ = δ * μ.real π.iUnion := by
      rw [← Finset.mul_sum, π.measure_iUnion_toReal]

/-- Density bounds on a finite stopping cover, followed by inclusion of each
forward extension in `F`, give a measure-growth inequality. The second set may
extend beyond the original box; only its finite volume is required. -/
theorem volume_restrict_le_mul_of_forward_cover
    {n : ℕ} {I : Box (Fin (n + 1))} (π : Prepartition I)
    (j : Fin (n + 1)) {E F : Set (Fin (n + 1) → ℝ)} {δ lag m : ℝ}
    (hδ : 0 ≤ δ) (hlag : 0 ≤ lag) (hm : 0 < m) (hF : volume F ≠ ∞)
    (hcover : E ∩ (I : Set (Fin (n + 1) → ℝ)) ⊆ π.iUnion)
    (hsmall : ∀ J ∈ π,
      (volume.restrict E).real J ≤ δ * volume.real (J : Set (Fin (n + 1) → ℝ)))
    (hforward : ∀ J ∈ π,
      (J.forwardExtension j lag m hm : Set (Fin (n + 1) → ℝ)) ⊆ F) :
    (volume.restrict E).real I ≤ δ * (1 + (lag + 1) / m) * volume.real F := by
  have hvolume := Box.volume_real_biUnion_le_forwardExtension π.boxes id j hlag hm
  have hsubset : (⋃ J ∈ π.boxes,
      (J.forwardExtension j lag m hm : Set (Fin (n + 1) → ℝ))) ⊆ F :=
    iUnion₂_subset fun J hJ ↦ hforward J hJ
  calc
    (volume.restrict E).real I ≤ δ * volume.real π.iUnion :=
      π.measure_restrict_le_mul_iUnion volume hcover hsmall
    _ ≤ δ * ((1 + (lag + 1) / m) *
        volume.real (⋃ J ∈ π.boxes,
          (J.forwardExtension j lag m hm : Set (Fin (n + 1) → ℝ)))) :=
      mul_le_mul_of_nonneg_left hvolume hδ
    _ ≤ δ * ((1 + (lag + 1) / m) * volume.real F) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (measureReal_mono hsubset hF) (by positivity)) hδ
    _ = _ := (mul_assoc _ _ _).symm

omit [Finite ι] in
/-- Continuous levels admit a finite forward stopping cover when a dense child
forces the forward extension of its parent into the lower level. The surrounding
set contains the extensions; continuity supplies the local stopping rule. -/
theorem exists_forward_superlevel_cover [Fintype ι] [DecidableEq ι]
    (I : Box ι) (j : ι)
    (division : ι → ℝ) (hdivision : ∀ i, 1 < division i)
    (split : ∀ J : Box ι, Prepartition J)
    (hpartition : ∀ J, (split J).IsPartition)
    (hside : ∀ J K, K ∈ split J → ∀ i,
      K.upper i - K.lower i = (J.upper i - J.lower i) / division i)
    (P : Box ι → Prop) (hPI : P I)
    (hPsplit : ∀ J ≤ I, P J → ∀ K ∈ split J, P K)
    {A : Set (ι → ℝ)} (hIA : I.Icc ⊆ A)
    {u : (ι → ℝ) → ℝ} (hu : ContinuousOn u A)
    {s t δ lag m : ℝ} (hst : s < t) (hlag : 0 ≤ lag) (hm : 0 < m)
    (hA : ∀ J ≤ I, P J →
      (J.forwardExtension j lag m hm : Set (ι → ℝ)) ⊆ A)
    (hparent : ∀ J ≤ I, P J → ∀ K ∈ split J,
      δ * volume.real (K : Set (ι → ℝ)) < (volume.restrict {x | t < u x}).real K →
        (J.forwardExtension j lag m hm : Set (ι → ℝ)) ⊆ {x | s < u x})
    (hsmall : (volume.restrict {x | t < u x}).real I ≤
      δ * volume.real (I : Set (ι → ℝ))) :
    ∃ π : Prepartition I, {x | t < u x} ∩ (I : Set (ι → ℝ)) ⊆ π.iUnion ∧
      ∀ J ∈ π, P J ∧
        (volume.restrict {x | t < u x}).real J ≤
          δ * volume.real (J : Set (ι → ℝ)) ∧
        (J.forwardExtension j lag m hm : Set (ι → ℝ)) ⊆ {x | s < u x} := by
  refine exists_stopping_cover I division hdivision split hpartition hside
    {x | t < u x} P
    (fun J ↦ (volume.restrict {x | t < u x}).real J ≤
      δ * volume.real (J : Set (ι → ℝ)))
    (fun J ↦ (J.forwardExtension j lag m hm : Set (ι → ℝ)) ⊆ {x | s < u x})
    hPI hPsplit (fun J hJI hPJ K hK h ↦ hparent J hJI hPJ K hK (lt_of_not_ge h))
    ?_ hsmall
  intro z hz
  by_cases hs : s < u z
  · have hnhds := hu z (hIA hz) (Ioi_mem_nhds hs)
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhdsWithin_iff.mp hnhds
    let C := 1 + 2 * (lag + m)
    have hC : 0 < C := by dsimp only [C]; positivity
    refine ⟨Metric.ball z (ε / C),
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z (div_pos hε hC)), ?_⟩
    intro J hJI _ _ hJU _ hPJ
    left
    intro x hx
    have hxball := J.forwardExtension_subset_ball j hlag hm (div_pos hε hC) hJU hx
    change x ∈ Metric.ball z (C * (ε / C)) at hxball
    rw [mul_div_cancel₀ _ hC.ne'] at hxball
    exact hεu ⟨hxball, hA J hJI hPJ hx⟩
  · have hzt : u z < t := (le_of_not_gt hs).trans_lt hst
    have hnhds := hu z (hIA hz) (Iio_mem_nhds hzt)
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhdsWithin_iff.mp hnhds
    refine ⟨Metric.ball z ε, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hε),
      ?_⟩
    intro J hJI _ _ hJU _ _
    right
    apply disjoint_left.mpr
    intro x hx hxt
    have hxu : u x < t :=
      hεu ⟨hJU (Box.coe_subset_Icc hx),
        hIA ((Box.le_iff_Icc.mp hJI) (Box.coe_subset_Icc hx))⟩
    exact (not_lt_of_ge hxu.le) hxt

omit [Finite ι] in
/-- Local stopping covers on the members of a finite partition combine into
one forward cover. The ambient box need not have the shape required by the
subdivision invariant; only its partition members must have that shape. -/
theorem exists_forward_superlevel_cover_of_partition [Fintype ι] [DecidableEq ι]
    {I : Box ι} (π : Prepartition I) (hπ : π.IsPartition) (j : ι)
    (division : ι → ℝ) (hdivision : ∀ i, 1 < division i)
    (split : ∀ J : Box ι, Prepartition J)
    (hpartition : ∀ J, (split J).IsPartition)
    (hside : ∀ J K, K ∈ split J → ∀ i,
      K.upper i - K.lower i = (J.upper i - J.lower i) / division i)
    (P : Box ι → Prop) (hPπ : ∀ J ∈ π, P J)
    (hPsplit : ∀ J ≤ I, P J → ∀ K ∈ split J, P K)
    {A : Set (ι → ℝ)} (hIA : I.Icc ⊆ A)
    {u : (ι → ℝ) → ℝ} (hu : ContinuousOn u A)
    {s t δ lag m : ℝ} (hst : s < t) (hlag : 0 ≤ lag) (hm : 0 < m)
    (hA : ∀ J ≤ I, P J →
      (J.forwardExtension j lag m hm : Set (ι → ℝ)) ⊆ A)
    (hparent : ∀ J ≤ I, P J → ∀ K ∈ split J,
      δ * volume.real (K : Set (ι → ℝ)) < (volume.restrict {x | t < u x}).real K →
        (J.forwardExtension j lag m hm : Set (ι → ℝ)) ⊆ {x | s < u x})
    (hsmall : ∀ J ∈ π, (volume.restrict {x | t < u x}).real J ≤
      δ * volume.real (J : Set (ι → ℝ))) :
    ∃ ρ : Prepartition I, {x | t < u x} ∩ (I : Set (ι → ℝ)) ⊆ ρ.iUnion ∧
      ∀ J ∈ ρ, P J ∧
        (volume.restrict {x | t < u x}).real J ≤
          δ * volume.real (J : Set (ι → ℝ)) ∧
        (J.forwardExtension j lag m hm : Set (ι → ℝ)) ⊆ {x | s < u x} := by
  classical
  have hlocal (J : Box ι) :
      ∃ ρ : Prepartition J, J ∈ π →
        {x | t < u x} ∩ (J : Set (ι → ℝ)) ⊆ ρ.iUnion ∧
          ∀ K ∈ ρ, P K ∧
            (volume.restrict {x | t < u x}).real K ≤
              δ * volume.real (K : Set (ι → ℝ)) ∧
            (K.forwardExtension j lag m hm : Set (ι → ℝ)) ⊆ {x | s < u x} := by
    by_cases hJ : J ∈ π
    · obtain ⟨ρ, hρ⟩ := exists_forward_superlevel_cover J j division hdivision split
        hpartition hside P (hPπ J hJ)
        (fun K hK ↦ hPsplit K (hK.trans (π.le_of_mem hJ)))
        ((Box.le_iff_Icc.mp (π.le_of_mem hJ)).trans hIA) hu hst hlag hm
        (fun K hK ↦ hA K (hK.trans (π.le_of_mem hJ)))
        (fun K hK ↦ hparent K (hK.trans (π.le_of_mem hJ))) (hsmall J hJ)
      exact ⟨ρ, fun _ ↦ hρ⟩
    · exact ⟨⊥, fun h ↦ (hJ h).elim⟩
  choose ρ hρ using hlocal
  refine ⟨π.biUnion ρ, ?_, ?_⟩
  · intro x hx
    obtain ⟨J, hJ, hxJ⟩ := hπ x hx.2
    obtain ⟨K, hK, hxK⟩ := (ρ J).mem_iUnion.mp ((hρ J hJ).1 ⟨hx.1, hxJ⟩)
    exact (π.biUnion ρ).mem_iUnion.mpr ⟨K, π.mem_biUnion.mpr ⟨J, hJ, hK⟩, hxK⟩
  · intro K hK
    obtain ⟨J, hJ, hKJ⟩ := π.mem_biUnion.mp hK
    exact (hρ J hJ).2 K hKJ

end BoxIntegral.Prepartition
