/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Function.Gluing
public import PDE.Analysis.Topology.Covering.AdditiveCocycle
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Gluing local functions modulo constants

On a simply connected open domain, local measurable functions on a countable
connected open cover can be made compatible by additive constants whenever their
differences are constant almost everywhere on overlaps.

Positivity of the measure on open sets turns the almost everywhere overlap
identities into an exact cocycle of constants. The covering-space argument removes
that cocycle, and countable measurable gluing then gives a single representative.
-/

@[expose] public noncomputable section

open Set TopologicalSpace Topology

namespace MeasureTheory

variable {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [Countable ι]

/-- Local real functions with constant differences on overlaps glue after adding
constants on a simply connected open domain. The functions themselves need not be
continuous. -/
theorem exists_aestronglyMeasurable_add_constants
    {μ : Measure X} [μ.IsOpenPosMeasure] {Ω : Set X}
    [SimplyConnectedSpace Ω] [LocallyPathConnectedSpace Ω]
    (hΩ : IsOpen Ω) (U : ι → Set X) (hopen : ∀ i, IsOpen (U i))
    (hconn : ∀ i, IsPreconnected (U i)) (hsub : ∀ i, U i ⊆ Ω)
    (hcover : Ω ⊆ ⋃ i, U i)
    (f : ι → X → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) (μ.restrict (U i)))
    (hpair : ∀ i j, ∃ c : ℝ,
      (fun x ↦ f i x - f j x) =ᵐ[μ.restrict (U i ∩ U j)] fun _ ↦ c) :
    ∃ a : ι → ℝ, ∃ g : X → ℝ, AEStronglyMeasurable g (μ.restrict Ω) ∧
      ∀ i, g =ᵐ[μ.restrict (U i)] fun x ↦ f i x + a i := by
  classical
  choose d hd using hpair
  let c (i j : ι) : ℝ := if i = j then 0 else d i j
  have hc (i j : ι) :
      (fun x ↦ f i x - f j x) =ᵐ[μ.restrict (U i ∩ U j)] fun _ ↦ c i j := by
    by_cases hij : i = j
    · subst j
      simp [c]
    · simpa only [c, ite_eq_right hij] using hd i j
  let V (i : ι) : Set Ω := Subtype.val ⁻¹' U i
  have hVconn (i : ι) : IsPreconnected (V i) :=
    (hconn i).preimage_of_isOpenMap Subtype.val_injective hΩ.isOpenMap_subtype_val
      (by simpa only [Subtype.range_val] using hsub i)
  have hVcover (x : Ω) : ∃ i, x ∈ V i := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover x.property)
    exact ⟨i, hi⟩
  have hcocycle (i j k : ι) (x : Ω) (hx : x ∈ V i ∩ V j ∩ V k) :
      c i j + c j k = c i k := by
    let W := U i ∩ U j ∩ U k
    have hW : IsOpen W := ((hopen i).inter (hopen j)).inter (hopen k)
    have hWne : W.Nonempty := ⟨x.val, hx⟩
    have ha : ∀ᵐ y ∂μ.restrict W, c i j + c j k = c i k := by
      filter_upwards
        [ae_restrict_of_ae_restrict_of_subset
          (show W ⊆ U i ∩ U j from inter_subset_left) (hc i j),
        ae_restrict_of_ae_restrict_of_subset
          (show W ⊆ U j ∩ U k from fun _ hy ↦ ⟨hy.1.2, hy.2⟩) (hc j k),
        ae_restrict_of_ae_restrict_of_subset
          (show W ⊆ U i ∩ U k from fun _ hy ↦ ⟨hy.1.1, hy.2⟩) (hc i k)]
        with y hij hjk hik
      linarith
    obtain ⟨_, _, heq⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae (hW.measure_pos μ hWne).ne' ha
    exact heq
  obtain ⟨a, ha⟩ := Topology.exists_sub_eq_of_additive_cocycle
    V (fun i ↦ (hopen i).preimage continuous_subtype_val) hVconn hVcover c
    (fun i ↦ by simp [c]) hcocycle
  have hcompatible (i j : ι) :
      (fun x ↦ f i x + a i) =ᵐ[μ.restrict (U i ∩ U j)] fun x ↦ f j x + a j := by
    by_cases hne : (U i ∩ U j).Nonempty
    · obtain ⟨x, hx⟩ := hne
      have heq : a j - a i = c i j :=
        ha i j ⟨⟨x, hsub i hx.1⟩, hx⟩
      filter_upwards [hc i j] with x hx
      linarith
    · simp only [Set.not_nonempty_iff_eq_empty.mp hne, Measure.restrict_empty,
        ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  obtain ⟨g, hg, hgf⟩ := exists_aestronglyMeasurable_of_ae_eq_on_intersections U
    (fun i ↦ (hopen i).measurableSet) (fun i x ↦ f i x + a i)
    (fun i ↦ (hf i).add_const (a i)) hcompatible
  exact ⟨a, g, hg.mono_measure (Measure.restrict_mono hcover le_rfl), hgf⟩

end MeasureTheory
