/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.BanachReflexivity.DualMeasure
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Bounded variation of the dual measure for a reflexive target

Reflexivity supplies a unit-ball vector attaining each dual norm. For a finite disjoint
family of sets, testing the Bochner functional against these vectors on their respective
sets controls the sum of the dual norms by a single Lp norm. Taking the supremum over
partitions gives a finite variation measure, with the same local measure-power bound.
-/

@[expose] public noncomputable section

open Set Filter Function
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Lp

private theorem variation_le_of_partition_bound {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] (m : VectorMeasure α E) {s : Set α} (hs : MeasurableSet s)
    {C : ℝ≥0∞} (hbound : ∀ P : Finset (Set α),
      (∀ t ∈ P, t ⊆ s) → ((P : Set (Set α)).PairwiseDisjoint id) →
      (∀ t ∈ P, MeasurableSet t) → (∑ t ∈ P, ‖m t‖ₑ) ≤ C) :
    VectorMeasure.variation (V := E) m s ≤ C := by
  by_contra h
  obtain ⟨P, hPs, hdisj, hmeas, hlt⟩ :=
    VectorMeasure.exists_lt_sum_of_lt_variation (V := E) m hs (lt_of_not_ge h)
  exact not_lt_of_ge (hbound P hPs hdisj hmeas) hlt

variable {α F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem exists_norming_vector
    (hF : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ F))
    (ℓ : StrongDual ℝ F) : ∃ c : F, ‖c‖ ≤ 1 ∧ ℓ c = ‖ℓ‖ := by
  obtain ⟨H, hHnorm, hH⟩ := exists_dual_vector'' ℝ ℓ
  obtain ⟨c, hc⟩ := hF H
  refine ⟨c, ?_, ?_⟩
  · have hnorm := (NormedSpace.inclusionInDoubleDualLi ℝ (E := F)).norm_map c
    change ‖NormedSpace.inclusionInDoubleDual ℝ F c‖ = ‖c‖ at hnorm
    rwa [← hc, hnorm] at hHnorm
  · change NormedSpace.inclusionInDoubleDual ℝ F c ℓ = _
    simpa only [hc, NormedSpace.dual_def, RCLike.ofReal_real_eq_id, id_eq] using hH

omit [NormedSpace ℝ F] [Fact (1 ≤ p)] in
private theorem norm_sum_indicator_le {ι : Type*} [Fintype ι]
    {s : Set α} (hs : MeasurableSet s) (t : ι → Set α)
    (ht : ∀ i, MeasurableSet (t i)) (hts : ∀ i, t i ⊆ s)
    (hdisj : Pairwise (Disjoint on t)) (c : ι → F) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ‖∑ i, indicatorConstLp p (ht i) (measure_ne_top μ _) (c i)‖ ≤
      μ.real s ^ (1 / p.toReal) := by
  classical
  let v (i : ι) := indicatorConstLp p (ht i) (measure_ne_top μ _) (c i)
  have hae (i : ι) : (v i : α → F) =ᵐ[μ] (t i).indicator (fun _ ↦ c i) :=
    indicatorConstLp_coeFn
  have hbound : ‖∑ i, v i‖ ≤ ‖indicatorConstLp p hs (measure_ne_top μ _) (1 : ℝ)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_finsetSum Finset.univ v, ae_all_iff.mpr hae,
      indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := measure_ne_top μ s)
        (c := (1 : ℝ))] with x hsum hx hind
    rw [hsum, hind]
    simp only [Finset.sum_apply]
    simp_rw [hx]
    by_cases hex : ∃ i, x ∈ t i
    · obtain ⟨i, hi⟩ := hex
      have hother : ∀ j, j ≠ i → x ∉ t j := by
        intro j hji hj
        exact Set.disjoint_left.mp (hdisj hji) hj hi
      rw [Finset.sum_eq_single i]
      · simpa only [Set.indicator_of_mem hi, Set.indicator_of_mem (hts i hi),
          norm_one] using hc i
      · intro j _ hji
        exact Set.indicator_of_notMem (hother j hji) _
      · simp
    · have hxnot : ∀ i, x ∉ t i := by simpa using hex
      have hz : ∑ i, (t i).indicator (fun _ ↦ c i) x = (0 : F) := by
        apply Finset.sum_eq_zero
        intro i _
        exact Set.indicator_of_notMem (hxnot i) _
      rw [hz, _root_.norm_zero]
      exact norm_nonneg _
  exact hbound.trans (by simpa only [norm_one, one_mul] using
    (norm_indicatorConstLp_le (p := p) (hs := hs) (hμs := measure_ne_top μ s)
      (c := (1 : ℝ))))

/-- Reflexivity controls the sum of the dual-measure norms on any finite disjoint family
by the measure of a containing measurable set. -/
theorem sum_norm_dualVectorMeasure_le
    (hF : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ F))
    (hp : p ≠ ∞) (Λ : StrongDual ℝ (Lp F p μ))
    {ι : Type*} [Fintype ι] {s : Set α} (hs : MeasurableSet s) (t : ι → Set α)
    (ht : ∀ i, MeasurableSet (t i)) (hts : ∀ i, t i ⊆ s)
    (hdisj : Pairwise (Disjoint on t)) :
    ∑ i, ‖dualVectorMeasure hp Λ (t i)‖ ≤ ‖Λ‖ * μ.real s ^ (1 / p.toReal) := by
  classical
  choose c hc hnorm using fun i ↦ exists_norming_vector hF (dualVectorMeasure hp Λ (t i))
  calc
    ∑ i, ‖dualVectorMeasure hp Λ (t i)‖ =
        Λ (∑ i, indicatorConstLp p (ht i) (measure_ne_top μ _) (c i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hnorm i, dualVectorMeasure_apply hp Λ (ht i)]
    _ ≤ ‖Λ (∑ i, indicatorConstLp p (ht i) (measure_ne_top μ _) (c i))‖ := le_abs_self _
    _ ≤ ‖Λ‖ * ‖∑ i, indicatorConstLp p (ht i) (measure_ne_top μ _) (c i)‖ := Λ.le_opNorm _
    _ ≤ ‖Λ‖ * μ.real s ^ (1 / p.toReal) :=
      mul_le_mul_of_nonneg_left (norm_sum_indicator_le hs t ht hts hdisj c hc) (norm_nonneg Λ)

private theorem sum_enorm_dualVectorMeasure_le
    (hF : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ F))
    (hp : p ≠ ∞) (Λ : StrongDual ℝ (Lp F p μ)) {s : Set α} (hs : MeasurableSet s)
    (P : Finset (Set α)) (hPs : ∀ t ∈ P, t ⊆ s)
    (hdisj : ((P : Set (Set α)).PairwiseDisjoint id))
    (hmeas : ∀ t ∈ P, MeasurableSet t) :
    (∑ t ∈ P, ‖dualVectorMeasure hp Λ t‖ₑ) ≤
      ENNReal.ofReal (‖Λ‖ * μ.real s ^ (1 / p.toReal)) := by
  classical
  have hbound := sum_norm_dualVectorMeasure_le hF hp Λ hs
    (fun t : P ↦ (t : Set α)) (fun t ↦ hmeas t t.property)
    (fun t ↦ hPs t t.property) (fun i j hij ↦
      hdisj i.property j.property (fun heq ↦ hij (Subtype.ext heq)))
  have hsum : (∑ t ∈ P, ‖dualVectorMeasure hp Λ t‖ₑ) =
      ENNReal.ofReal (∑ t : P, ‖dualVectorMeasure hp Λ (t : Set α)‖) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)]
    simp only [ofReal_norm, Finset.univ_eq_attach]
    exact (Finset.sum_attach P (fun t ↦ ‖dualVectorMeasure hp Λ t‖ₑ)).symm
  rw [hsum]
  exact ENNReal.ofReal_le_ofReal hbound

/-- The variation of the dual-valued measure has the same local measure-power bound. -/
theorem variation_dualVectorMeasure_le
    (hF : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ F))
    (hp : p ≠ ∞) (Λ : StrongDual ℝ (Lp F p μ)) {s : Set α} (hs : MeasurableSet s) :
    VectorMeasure.variation (V := StrongDual ℝ F) (dualVectorMeasure hp Λ) s ≤
      ENNReal.ofReal (‖Λ‖ * μ.real s ^ (1 / p.toReal)) := by
  exact variation_le_of_partition_bound (dualVectorMeasure hp Λ) hs
    (sum_enorm_dualVectorMeasure_le hF hp Λ hs)

/-- In particular, this dual-valued measure has finite total variation. -/
theorem isFiniteMeasure_variation_dualVectorMeasure
    (hF : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ F))
    (hp : p ≠ ∞) (Λ : StrongDual ℝ (Lp F p μ)) :
    IsFiniteMeasure (VectorMeasure.variation (V := StrongDual ℝ F) (dualVectorMeasure hp Λ)) :=
  ⟨(variation_dualVectorMeasure_le hF hp Λ MeasurableSet.univ).trans_lt
    ENNReal.ofReal_lt_top⟩

end MeasureTheory.Lp
