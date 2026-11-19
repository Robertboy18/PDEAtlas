/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Covering.IntervalExpansion

/-!
# Measure comparison with forward time extensions

A finite union of measurable products is compared with the union obtained by
moving and lengthening its time intervals. Applying the one-dimensional interval
estimate to each spatial fibre and integrating preserves the same constant.
No disjointness of the products or finiteness of the spatial measure is required.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Analysis

/-- Forward extension of time intervals controls the measure of the original product
cover. The measure on the spatial factor is arbitrary, including infinite measures. -/
theorem measure_prod_biUnion_Ioc_le_forward
    {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset ι) (S : ι → Set X) (hS : ∀ i ∈ s, MeasurableSet (S i))
    (a b : ι → ℝ) (hab : ∀ i ∈ s, a i ≤ b i)
    {lag m : ℝ} (hlag : 0 ≤ lag) (hm : 0 < m) :
    (μ.prod volume) (⋃ i ∈ s, S i ×ˢ Ioc (a i) (b i)) ≤
      ENNReal.ofReal (1 + (lag + 1) / m) *
        (μ.prod volume) (⋃ i ∈ s, S i ×ˢ
          Ioc (b i + lag * (b i - a i)) (b i + (lag + m) * (b i - a i))) := by
  classical
  have hmeas (c d : ι → ℝ) : MeasurableSet (⋃ i ∈ s, S i ×ˢ Ioc (c i) (d i)) :=
    s.finite_toSet.measurableSet_biUnion fun i hi ↦ (hS i hi).prod measurableSet_Ioc
  rw [Measure.prod_apply (hmeas a b), Measure.prod_apply (hmeas _ _),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  have hfibre (c d : ι → ℝ) :
      Prod.mk x ⁻¹' (⋃ i ∈ s, S i ×ˢ Ioc (c i) (d i)) =
        ⋃ i ∈ s.filter (fun i ↦ x ∈ S i), Ioc (c i) (d i) := by
    ext t
    simp only [mem_preimage, mem_iUnion, mem_prod, Finset.mem_filter]
    aesop
  dsimp only
  rw [hfibre a b,
    hfibre (fun i ↦ b i + lag * (b i - a i))
      (fun i ↦ b i + (lag + m) * (b i - a i))]
  exact volume_biUnion_Ioc_le_forward _ a b
    (fun i hi ↦ hab i (Finset.mem_filter.mp hi).1) hlag hm

end PDE.Analysis
