/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import PDE.Analysis.MeasureTheory.Lp.SectionNorm

/-!
# Mixed norms from a finite spatial cover

Restricted spatial norms control the full norm when the sets cover the support.
A finite sum then glues mixed-norm membership for jointly measurable fields.
Actual section membership is supplied before comparing the real-valued norms.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

/-- A finite measurable cover of the support bounds the full spatial norm by the sum
of the restricted norms. Section membership precedes the comparison of real norms. -/
theorem lpNorm_le_sum_restrict_of_support_cover
    {X ι : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (a : Finset ι) (U : ι → Set X)
    (hU : ∀ i ∈ a, MeasurableSet (U i))
    (hmem : ∀ i ∈ a, MemLp f p (ν.restrict (U i)))
    (hcover : Function.support f ⊆ ⋃ i ∈ a, U i) :
    lpNorm f p ν ≤ ∑ i ∈ a, lpNorm f p (ν.restrict (U i)) := by
  classical
  let g : ι → X → ℝ := fun i ↦ (U i).indicator (fun x ↦ ‖f x‖)
  have hg (i : ι) (hi : i ∈ a) : MemLp (g i) p ν :=
    (memLp_indicator_iff_restrict (hU i hi).nullMeasurableSet).mpr (hmem i hi).norm
  have hdom (x : X) : ‖f x‖ ≤ ∑ i ∈ a, g i x := by
    by_cases hx : f x = 0
    · simp only [hx, norm_zero]
      exact Finset.sum_nonneg (fun i _ ↦ indicator_nonneg (fun _ _ ↦ norm_nonneg _) x)
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hcover hx)
      calc
        ‖f x‖ = g i x := (indicator_of_mem hxi (fun x ↦ ‖f x‖)).symm
        _ ≤ ∑ j ∈ a, g j x := Finset.single_le_sum
          (fun j _ ↦ indicator_nonneg (fun _ _ ↦ norm_nonneg _) x) hi
  calc
    lpNorm f p ν ≤ lpNorm (fun x ↦ ∑ i ∈ a, g i x) p ν :=
      lpNorm_mono_real (memLp_finsetSum a hg) hdom
    _ ≤ ∑ i ∈ a, lpNorm (g i) p ν := by
      have hfun : (fun x ↦ ∑ i ∈ a, g i x) = ∑ i ∈ a, g i := by
        funext x
        simp only [Finset.sum_apply]
      rw [hfun]
      exact lpNorm_sum_le hg hp
    _ = ∑ i ∈ a, lpNorm f p (ν.restrict (U i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      change (eLpNorm ((U i).indicator (fun x ↦ ‖f x‖)) p ν).toReal = _
      rw [eLpNorm_indicator_eq_eLpNorm_restrict (hU i hi).nullMeasurableSet,
        eLpNorm_norm _ (hmem i hi).aestronglyMeasurable]
      rfl

/-- Finite spatial localization glues actual mixed norms of a jointly measurable field. -/
theorem memLp_lpNorm_of_finite_support_cover
    {A X ι : Type*} [MeasurableSpace A] [MeasurableSpace X]
    {μ : Measure A} {ν : Measure X} [SFinite ν]
    {f : A × X → ℝ} (hf : Measurable f) {p q : ℝ≥0∞}
    (hp : 1 ≤ p) (hptop : p ≠ ∞) (a : Finset ι) (U : ι → Set X)
    (hU : ∀ i ∈ a, MeasurableSet (U i))
    (hsection : ∀ᵐ t ∂μ, ∀ i ∈ a, MemLp (fun x ↦ f (t, x)) p (ν.restrict (U i)))
    (hcover : ∀ᵐ t ∂μ, Function.support (fun x ↦ f (t, x)) ⊆ ⋃ i ∈ a, U i)
    (hlocal : ∀ i ∈ a, MemLp (fun t ↦ lpNorm (fun x ↦ f (t, x)) p
      (ν.restrict (U i))) q μ) :
    MemLp (fun t ↦ lpNorm (fun x ↦ f (t, x)) p ν) q μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  apply (memLp_finsetSum a hlocal).mono'
    ((hf.eLpNorm_prod_right hp0 hptop).ennreal_toReal.aestronglyMeasurable)
  filter_upwards [hsection, hcover] with t ht hc
  change ‖lpNorm (fun x ↦ f (t, x)) p ν‖ ≤ _
  rw [Real.norm_of_nonneg lpNorm_nonneg]
  exact lpNorm_le_sum_restrict_of_support_cover hp a U hU ht hc

end MeasureTheory
