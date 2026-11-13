/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Mixed integrability of compact Schwartz families

Continuous compactly supported families of Schwartz functions have finite mixed
Lebesgue norm. The proof passes through Mathlib's continuous map to spatial `Lp`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace SchwartzMap

variable {α E F : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [OpensMeasurableSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [SecondCountableTopologyEither E F] {ν : Measure E} [ν.HasTemperateGrowth]

/-- A continuous compactly supported family of Schwartz functions has finite mixed
Lebesgue norm for any outer exponent and any normed spatial exponent. -/
theorem memLp_eLpNorm_of_continuous_hasCompactSupport {p q : ℝ≥0∞} [Fact (1 ≤ q)]
    {f : α → 𝓢(E, F)} (hf : Continuous f) (hfc : HasCompactSupport f) :
    MemLp (fun t ↦ eLpNorm (f t) q ν) p μ := by
  let L := toLpCLM ℝ F q ν
  have h : MemLp (fun t ↦ L (f t)) p μ :=
    (L.continuous.comp hf).memLp_of_hasCompactSupport (hfc.comp_left L.map_zero)
  have he (t : α) : ‖L (f t)‖ₑ = eLpNorm (f t) q ν := by
    rw [Lp.enorm_def]
    exact eLpNorm_congr_ae ((f t).coeFn_toLp q ν)
  simpa only [he] using h.enorm

/-- Finite time-weighted sums of Schwartz functions have finite mixed norm when
the scalar weights are continuous and compactly supported. -/
theorem memLp_eLpNorm_finset_smul {p q : ℝ≥0∞} [Fact (1 ≤ q)]
    {ι : Type*} (a : Finset ι) (w : ι → α → ℝ) (f : ι → 𝓢(E, F))
    (hw : ∀ i ∈ a, Continuous (w i)) (hwc : ∀ i ∈ a, HasCompactSupport (w i)) :
    MemLp (fun t ↦ eLpNorm (∑ i ∈ a, w i t • f i) q ν) p μ := by
  have hf : Continuous (fun t ↦ ∑ i ∈ a, w i t • f i) :=
    continuous_finsetSum a fun i hi ↦ (hw i hi).smul continuous_const
  have hfc : HasCompactSupport (fun t ↦ ∑ i ∈ a, w i t • f i) := by
    have hterms (i : ι) (hi : i ∈ a) :
        HasCompactSupport (fun t ↦ w i t • f i) :=
      (hwc i hi).smul_right (f' := fun _ ↦ f i)
    have he : (∑ i ∈ a, fun t ↦ w i t • f i) = (fun t ↦ ∑ i ∈ a, w i t • f i) := by
      funext t
      simp only [Finset.sum_apply]
    rw [← he]
    exact HasCompactSupport.finset_sum (s := a) (f := fun i t ↦ w i t • f i) hterms
  have h := memLp_eLpNorm_of_continuous_hasCompactSupport
    (μ := μ) (ν := ν) (p := p) (q := q) hf hfc
  have he (t : α) : ((∑ i ∈ a, w i t • f i : 𝓢(E, F)) : E → F) =
      ∑ i ∈ a, ((w i t • f i : 𝓢(E, F)) : E → F) := by
    funext x
    simp only [sum_apply, Finset.sum_apply]
  simpa only [he] using h

end SchwartzMap
