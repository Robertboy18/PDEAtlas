/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

/-!
# Signed measures associated to real `Lp` functionals

For a finite measure and `1 ≤ p < ∞`, a continuous linear functional on real `Lp` defines
a signed measure by evaluation on indicators. Countable additivity follows from unconditional
convergence of disjoint indicator sums in `Lp`, using continuity of measure on the remainders
of finite unions. Absolute continuity then gives a measurable integrable Radon–Nikodym density
representing the functional on every measurable-set indicator.

This indicator representation includes `p = 1`.
-/

@[expose] public section

open Set Filter Function
open scoped ENNReal NNReal Topology symmDiff

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
variable {p : ℝ≥0∞}

section Indicators

variable {ι E : Type*} [NormedAddCommGroup E] {s : ι → Set α}

/-- The indicator of a finite disjoint union is the sum of its indicators in `Lp`. -/
theorem indicatorConstLp_biUnion_finset (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Disjoint on s)) (t : Finset ι) (c : E) :
    indicatorConstLp p (t.measurableSet_biUnion fun i _ ↦ hs i)
        (measure_ne_top μ _) c =
      ∑ i ∈ t, indicatorConstLp p (hs i) (measure_ne_top μ _) c := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi iht =>
    have hdisj' : Disjoint (s i) (⋃ j ∈ t, s j) := by
      refine Set.disjoint_iUnion₂_right.mpr fun j hj ↦ ?_
      exact hdisj (by rintro rfl; exact hi hj)
    simpa only [Finset.set_biUnion_insert, Finset.sum_insert hi, iht] using
      (indicatorConstLp_disjoint_union (p := p) (hs i)
        (t.measurableSet_biUnion fun j _ ↦ hs j)
        (measure_ne_top μ _) (measure_ne_top μ _) hdisj' c)

/-- For a finite measure and finite `p ≥ 1`, indicators of a countable disjoint family
sum unconditionally in `Lp` to the indicator of their union. -/
theorem hasSum_indicatorConstLp [Countable ι] [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hs : ∀ i, MeasurableSet (s i)) (hdisj : Pairwise (Disjoint on s)) (c : E) :
    HasSum (fun i ↦ indicatorConstLp p (hs i) (measure_ne_top μ _) c)
      (indicatorConstLp p (MeasurableSet.iUnion hs) (measure_ne_top μ _) c) := by
  classical
  let t : Finset ι → Set α := fun F ↦ ⋃ i ∈ F, s i
  have ht (F : Finset ι) : MeasurableSet (t F) :=
    F.measurableSet_biUnion fun i _ ↦ hs i
  have hsubset (F : Finset ι) : t F ⊆ ⋃ i, s i := by
    exact Set.iUnion₂_subset fun i _ ↦ Set.subset_iUnion s i
  have hmono : Monotone t := by
    intro F G hFG x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
    exact Set.mem_iUnion₂.mpr ⟨i, hFG hi, hxi⟩
  have hrem : Antitone (fun F : Finset ι ↦ (⋃ i, s i) \ t F) := by
    intro F G hFG
    exact Set.sdiff_subset_sdiff_right (hmono hFG)
  have hempty : (⋂ F : Finset ι, (⋃ i, s i) \ t F) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hx ∅).1
    exact (Set.mem_iInter.mp hx {i}).2 (by simpa [t] using hxi)
  have hlim : Tendsto (fun F : Finset ι ↦ μ (t F ∆ ⋃ i, s i)) atTop (𝓝 0) := by
    simp_rw [symmDiff_of_le (hsubset _)]
    simpa only [Function.comp_def, hempty, measure_empty] using
      (tendsto_measure_iInter_atTop
        (fun F ↦ ((MeasurableSet.iUnion hs).diff (ht F)).nullMeasurableSet)
        hrem ⟨∅, measure_ne_top μ _⟩)
  have hLp := tendsto_indicatorConstLp_set (p := p) (μ := μ) (c := c)
    (hs := MeasurableSet.iUnion hs) (hμs := measure_ne_top μ _)
    (ht := ht) (hμt := fun F ↦ measure_ne_top μ (t F)) hp hlim
  change Tendsto (fun F : Finset ι ↦
      ∑ i ∈ F, indicatorConstLp p (hs i) (measure_ne_top μ _) c) atTop
    (𝓝 (indicatorConstLp p (MeasurableSet.iUnion hs) (measure_ne_top μ _) c))
  simpa only [t, indicatorConstLp_biUnion_finset hs hdisj] using hLp

end Indicators

namespace Lp

variable [Fact (1 ≤ p)]

/-- The signed measure obtained by applying a bounded real `Lp` functional to indicators.
The finite-exponent hypothesis ensures countable additivity in the `Lp` norm. -/
noncomputable def dualSignedMeasure (hp : p ≠ ∞) (Λ : Lp ℝ p μ →L[ℝ] ℝ) :
    SignedMeasure α := by
  classical
  exact
    { measureOf' := fun s ↦
        if hs : MeasurableSet s then
          Λ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ))
        else 0
      empty' := by simp
      not_measurable' := by
        intro s hs
        exact dite_eq_right hs
      m_iUnion' := by
        intro s hs hdisj
        simpa only [dite_eq_left (MeasurableSet.iUnion hs), dite_eq_left (hs _)] using
          Λ.hasSum (hasSum_indicatorConstLp (μ := μ) hp hs hdisj (1 : ℝ)) }

/-- On measurable sets, the induced signed measure is evaluation on the indicator. -/
@[simp]
theorem dualSignedMeasure_apply (hp : p ≠ ∞) (Λ : Lp ℝ p μ →L[ℝ] ℝ)
    {s : Set α} (hs : MeasurableSet s) :
    dualSignedMeasure hp Λ s =
      Λ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ)) := by
  classical
  simp only [dualSignedMeasure, VectorMeasure.coe_mk, dite_eq_left hs]

/-- Null sets have zero indicators in `Lp`, so the induced signed measure is absolutely
continuous with respect to the original measure. -/
theorem dualSignedMeasure_absolutelyContinuous (hp : p ≠ ∞)
    (Λ : Lp ℝ p μ →L[ℝ] ℝ) :
    dualSignedMeasure hp Λ ≪ᵥ μ.toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun s hs hzero ↦ ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hzero
  have hLp : indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ) = 0 := by
    simpa only [indicatorConstLp_empty] using
      (indicatorConstLp_inj (p := p) hs (measure_ne_top μ s)
        MeasurableSet.empty (measure_ne_top μ ∅) (c := (1 : ℝ)) one_ne_zero).2
        (ae_eq_empty.mpr hzero)
  rw [dualSignedMeasure_apply hp Λ hs, hLp, map_zero]

/-- Every bounded functional on real `Lp` over a finite measure, with `1 ≤ p < ∞`,
has a measurable integrable density representing its values on measurable-set indicators. -/
theorem exists_integrable_dualDensity (hp : p ≠ ∞) (Λ : Lp ℝ p μ →L[ℝ] ℝ) :
    ∃ g : α → ℝ, Measurable g ∧ Integrable g μ ∧
      ∀ (s : Set α) (hs : MeasurableSet s),
        Λ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ)) = ∫ x in s, g x ∂μ := by
  let ν := dualSignedMeasure hp Λ
  have hν : μ.withDensityᵥ (ν.rnDeriv μ) = ν :=
    ν.withDensityᵥ_rnDeriv_eq μ (dualSignedMeasure_absolutelyContinuous hp Λ)
  refine ⟨ν.rnDeriv μ, ν.measurable_rnDeriv μ, ν.integrable_rnDeriv μ, ?_⟩
  intro s hs
  calc
    Λ (indicatorConstLp p hs (measure_ne_top μ s) (1 : ℝ)) = ν s :=
      (dualSignedMeasure_apply hp Λ hs).symm
    _ = μ.withDensityᵥ (ν.rnDeriv μ) s := by rw [hν]
    _ = ∫ x in s, ν.rnDeriv μ x ∂μ :=
      withDensityᵥ_apply (ν.integrable_rnDeriv μ) hs

end Lp

end MeasureTheory
