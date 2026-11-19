/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Criteria for local integrability

An almost-everywhere strongly measurable function with a uniform norm bound
is locally integrable with respect to a locally finite measure.  A
pointwise measurable version is included for Borel-valued functions.
Pullback by a product projection preserves local integrability when the
measure on the omitted factor is locally finite.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace MeasureTheory

variable {X E : Type*} [MeasurableSpace X] [TopologicalSpace X]
variable [NormedAddCommGroup E] {μ : Measure X} [IsLocallyFiniteMeasure μ]

/-- An almost-everywhere strongly measurable function with a uniform norm bound is locally
integrable. -/
theorem locallyIntegrable_of_aestronglyMeasurable_norm_le_const
    {f : X → E} {C : ℝ}
    (hf : AEStronglyMeasurable f μ) (hC : 0 ≤ C)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    LocallyIntegrable f μ := by
  refine (locallyIntegrable_const (μ := μ) C).mono hf ?_
  filter_upwards [hbound] with x hx
  simpa only [Real.norm_of_nonneg hC] using hx

/-- A measurable function with a pointwise uniform norm bound is locally integrable. -/
theorem locallyIntegrable_of_measurable_norm_le_const
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : X → E} {C : ℝ}
    (hf : Measurable f) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖f x‖ ≤ C) :
    LocallyIntegrable f μ :=
  locallyIntegrable_of_aestronglyMeasurable_norm_le_const
    hf.aestronglyMeasurable hC (Filter.Eventually.of_forall hbound)

/-- A locally integrable function remains locally integrable after adding
an independent variable carrying a locally finite measure. -/
theorem LocallyIntegrable.comp_snd
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    {ν : Measure Y} [SFinite μ] [SFinite ν] {f : Y → E}
    (hf : LocallyIntegrable f ν) :
    LocallyIntegrable (fun p : X × Y ↦ f p.2) (μ.prod ν) := by
  intro p
  obtain ⟨U, hU, hμU⟩ := μ.finiteAt_nhds p.1
  obtain ⟨V, hV, hfV⟩ := hf p.2
  let : IsFiniteMeasure (μ.restrict U) := isFiniteMeasure_restrict.mpr hμU.ne
  refine ⟨U ×ˢ V, prod_mem_nhds hU hV, ?_⟩
  rw [IntegrableOn, ← Measure.prod_restrict]
  exact hfV.comp_snd (μ.restrict U)

omit [IsLocallyFiniteMeasure μ] in
/-- The corresponding projection result for the first product coordinate. -/
theorem LocallyIntegrable.comp_fst
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    {ν : Measure Y} [SFinite μ] [SFinite ν] [IsLocallyFiniteMeasure ν] {f : X → E}
    (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun p : X × Y ↦ f p.1) (μ.prod ν) := by
  intro p
  obtain ⟨U, hU, hfU⟩ := hf p.1
  obtain ⟨V, hV, hνV⟩ := ν.finiteAt_nhds p.2
  let : IsFiniteMeasure (ν.restrict V) := isFiniteMeasure_restrict.mpr hνV.ne
  refine ⟨U ×ˢ V, prod_mem_nhds hU hV, ?_⟩
  rw [IntegrableOn, ← Measure.prod_restrict]
  exact hfU.comp_fst (ν.restrict V)

omit [IsLocallyFiniteMeasure μ] in
/-- Integration in one variable against a continuous compactly supported
weight preserves local integrability in the other variable. No global
integrability of the original field is required. -/
theorem LocallyIntegrable.integral_smul_left
    {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]
    [LocallyCompactSpace X] [T2Space X]
    [LocallyCompactSpace Y] [T2Space Y]
    [OpensMeasurableSpace (X × Y)]
    [NormedSpace ℝ E]
    {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X × Y → E} (hf : LocallyIntegrable f (μ.prod ν))
    {ψ : X → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    LocallyIntegrable (fun y ↦ ∫ x, ψ x • f (x, y) ∂μ) ν := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi := (hf.continuous_smul (hψ.comp continuous_fst)).integrableOn_isCompact
    (hc.prod hK)
  rw [IntegrableOn, ← Measure.prod_restrict] at hi
  have heq (y : Y) : (∫ x in tsupport ψ, ψ x • f (x, y) ∂μ) =
      ∫ x, ψ x • f (x, y) ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
  simpa only [IntegrableOn, Function.comp_apply, heq] using hi.integral_prod_right

end MeasureTheory
