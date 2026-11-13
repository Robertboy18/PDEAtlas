/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Distribution.Schwartz.Density
public import PDE.Analysis.MeasureTheory.Lp.TensorDensity

/-!
# Compact Schwartz tensors in mixed Lebesgue spaces

Finite compact Schwartz tensors are dense in mixed `Lp` at finite normed exponents.
Their quotient classes have explicit Schwartz-valued sections almost everywhere,
and their quotient norm is exactly the mixed seminorm of these sections.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal SchwartzMap

namespace SchwartzMap

variable {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  (μ : Measure D) [μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ]
  (ν : Measure E) [ν.HasTemperateGrowth] [IsFiniteMeasureOnCompacts ν]

/-- Finite linear combinations of compact Schwartz tensors as mixed Lebesgue classes. -/
noncomputable def compactTensorLpLinearMap :
    (({w : 𝓢(D, ℝ) // HasCompactSupport (w : D → ℝ)} ×
      {f : 𝓢(E, F) // HasCompactSupport (f : E → F)}) →₀ ℝ) →ₗ[ℝ]
        Lp (Lp F q ν) p μ :=
  Finsupp.linearCombination ℝ fun z ↦
    ((ContinuousLinearMap.lsmul ℝ ℝ).flip (z.2.1.toLp q ν)).compLp (z.1.1.toLp p μ)

/-- Compact Schwartz tensors have dense span at all finite normed mixed exponents. -/
theorem denseRange_compactTensorLpLinearMap (hp : p ≠ ∞) (hq : q ≠ ∞) :
    DenseRange (compactTensorLpLinearMap (F := F) p q μ ν) := by
  have hs : Dense ((fun f : 𝓢(E, F) ↦ f.toLp q ν) ''
      {f : 𝓢(E, F) | HasCompactSupport (f : E → F)}) :=
    (denseRange_toLpCLM (F := F) (μ := ν) hq).dense_image
      continuous_toLp dense_hasCompactSupport
  have ht : Dense ((fun w : 𝓢(D, ℝ) ↦ w.toLp p μ) ''
      {w : 𝓢(D, ℝ) | HasCompactSupport (w : D → ℝ)}) :=
    (denseRange_toLpCLM (F := ℝ) (μ := μ) hp).dense_image
      continuous_toLp dense_hasCompactSupport
  have h := Lp.dense_span_smul_tensors hp hs ht
  change Dense (LinearMap.range (compactTensorLpLinearMap (F := F) p q μ ν) :
    Set (Lp (Lp F q ν) p μ))
  rw [compactTensorLpLinearMap, Finsupp.range_linearCombination]
  have he : Set.range (fun z :
      {w : 𝓢(D, ℝ) // HasCompactSupport (w : D → ℝ)} ×
      {f : 𝓢(E, F) // HasCompactSupport (f : E → F)} ↦
      ((ContinuousLinearMap.lsmul ℝ ℝ).flip (z.2.1.toLp q ν)).compLp (z.1.1.toLp p μ)) =
      {u : Lp (Lp F q ν) p μ | ∃ v ∈ (fun f : 𝓢(E, F) ↦ f.toLp q ν) ''
        {f : 𝓢(E, F) | HasCompactSupport (f : E → F)},
        ∃ a ∈ (fun w : 𝓢(D, ℝ) ↦ w.toLp p μ) ''
          {w : 𝓢(D, ℝ) | HasCompactSupport (w : D → ℝ)},
          ((ContinuousLinearMap.lsmul ℝ ℝ).flip v).compLp a = u} := by
    ext u
    constructor
    · rintro ⟨⟨w, f⟩, rfl⟩
      exact ⟨f.1.toLp q ν, ⟨f.1, f.2, rfl⟩, w.1.toLp p μ, ⟨w.1, w.2, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨f, hf, rfl⟩, a, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨(⟨w, hw⟩, ⟨f, hf⟩), rfl⟩
  simpa only [he] using h

/-- The actual Schwartz-valued section of a finite sum of compact tensors. -/
noncomputable def compactTensorSchwartzLinearMap :
    (({w : 𝓢(D, ℝ) // HasCompactSupport (w : D → ℝ)} ×
      {f : 𝓢(E, F) // HasCompactSupport (f : E → F)}) →₀ ℝ) →ₗ[ℝ]
        (D → 𝓢(E, F)) :=
  Finsupp.linearCombination ℝ fun z t ↦ z.1.1 t • z.2.1

omit [FiniteDimensional ℝ D] [Fact (1 ≤ p)]
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] in
/-- The finite tensor quotient map has the actual Schwartz section almost everywhere. -/
theorem compactTensorLpLinearMap_ae_eq
    (a : ({w : 𝓢(D, ℝ) // HasCompactSupport (w : D → ℝ)} ×
      {f : 𝓢(E, F) // HasCompactSupport (f : E → F)}) →₀ ℝ) :
    (compactTensorLpLinearMap (F := F) p q μ ν a : D → Lp F q ν) =ᵐ[μ]
      fun t ↦ (compactTensorSchwartzLinearMap a t).toLp q ν := by
  let T := fun z : {w : 𝓢(D, ℝ) // HasCompactSupport (w : D → ℝ)} ×
      {f : 𝓢(E, F) // HasCompactSupport (f : E → F)} ↦
    ((ContinuousLinearMap.lsmul ℝ ℝ).flip (z.2.1.toLp q ν)).compLp (z.1.1.toLp p μ)
  have htensor (z) : (T z : D → Lp F q ν) =ᵐ[μ]
      fun t ↦ z.1.1 t • z.2.1.toLp q ν := by
    filter_upwards [((ContinuousLinearMap.lsmul ℝ ℝ).flip (z.2.1.toLp q ν)).coeFn_compLp
      (z.1.1.toLp p μ), z.1.1.coeFn_toLp p μ] with t hT hw
    simpa only [T, hw, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply] using hT
  have hsum : (Finsupp.linearCombination ℝ T a : D → Lp F q ν) =ᵐ[μ]
      Finsupp.linearCombination ℝ (fun z t ↦ z.1.1 t • z.2.1.toLp q ν) a :=
    (Lp.coeFn_linearCombination a T).trans <|
      eventuallyEq_sum fun z _ ↦ (htensor z).const_smul (a z)
  apply hsum.trans
  filter_upwards with t
  let L := toLpCLM ℝ F q ν
  simp only [compactTensorSchwartzLinearMap, Finsupp.linearCombination_apply,
    Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
  change (∑ z ∈ a.support, a z • (z.1.1 t • L z.2.1)) =
    L (∑ z ∈ a.support, a z • (z.1.1 t • z.2.1))
  simp only [map_sum, map_smul]

omit [FiniteDimensional ℝ D] [Fact (1 ≤ p)]
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] in
/-- The quotient norm agrees exactly with the raw mixed norm of the tensor sum. -/
theorem norm_compactTensorLpLinearMap
    (a : ({w : 𝓢(D, ℝ) // HasCompactSupport (w : D → ℝ)} ×
      {f : 𝓢(E, F) // HasCompactSupport (f : E → F)}) →₀ ℝ) :
    ‖compactTensorLpLinearMap (F := F) p q μ ν a‖ =
      (eLpNorm (fun t ↦ eLpNorm (compactTensorSchwartzLinearMap a t) q ν) p μ).toReal := by
  rw [Lp.norm_def]
  congr 1
  rw [← eLpNorm_enorm _ (Lp.aestronglyMeasurable _)]
  apply eLpNorm_congr_ae
  filter_upwards [compactTensorLpLinearMap_ae_eq p q μ ν a] with t ht
  rw [ht, Lp.enorm_def]
  exact eLpNorm_congr_ae ((compactTensorSchwartzLinearMap a t).coeFn_toLp q ν)

end SchwartzMap
