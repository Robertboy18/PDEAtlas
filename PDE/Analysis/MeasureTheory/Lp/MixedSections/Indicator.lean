/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.MixedSections
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Moving spatial restrictions of mixed Lp sections

A measurable subset of a product restricts each spatial section of a Bochner
L1Lp field. The mixed-section reconstruction `exists_mixedLp_sections` produces the
restricted class. Its norm is exactly the integral of the spatial Lp norms on the varying
sections of the subset, without a time-dependent measure in the Bochner space.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal

namespace MeasureTheory

/-- A measurable moving spatial restriction of a jointly represented L1Lp field
has a Bochner class whose norm is exactly the integral of restricted section norms. -/
theorem exists_L1_sections_indicator {α β E : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure α} {ν : Measure β} [SFinite ν] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] [SeparableSpace (Lp E p ν)] (hptop : p ≠ ∞)
    (f : Lp (Lp E p ν) 1 μ) {U : α × β → E} (hU : Measurable U)
    (hsection : ∀ᵐ t ∂μ, (fun x ↦ U (t, x)) =ᵐ[ν] (f t : β → E))
    {S : Set (α × β)} (hS : MeasurableSet S) :
    ∃ g : Lp (Lp E p ν) 1 μ,
      (∀ᵐ t ∂μ, (fun x ↦ S.indicator U (t, x)) =ᵐ[ν] (g t : β → E)) ∧
      ‖g‖ = ∫ t, lpNorm (fun x ↦ U (t, x)) p (ν.restrict {x | (t, x) ∈ S}) ∂μ := by
  classical
  have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))
  have hV : Measurable (S.indicator U) := hU.indicator hS
  have hsec (t : α) : MeasurableSet {x | (t, x) ∈ S} :=
    hS.preimage measurable_prodMk_left
  have heq (t : α) : (fun x ↦ S.indicator U (t, x)) =
      {x | (t, x) ∈ S}.indicator (fun x ↦ U (t, x)) := by
    funext x
    simp only [indicator_apply, mem_ofPred_eq]
  have hfin : MemLp (fun t ↦ eLpNorm (fun x ↦ S.indicator U (t, x)) p ν) 1 μ := by
    apply (Lp.memLp f).of_le_enorm
      (hV.eLpNorm_prod_right hp0 hptop).aestronglyMeasurable
    filter_upwards [hsection] with t ht
    simp only [enorm_eq_self]
    rw [heq t, Lp.enorm_def]
    exact (eLpNorm_indicator_le _ (hsec t).nullMeasurableSet).trans_eq (eLpNorm_congr_ae ht)
  obtain ⟨g, hg, _⟩ := exists_mixedLp_sections hptop (by norm_num) hV hfin
  refine ⟨g, hg, ?_⟩
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [hg] with t ht
  rw [Lp.norm_def, ← eLpNorm_congr_ae ht, heq t,
    eLpNorm_indicator_eq_eLpNorm_restrict (hsec t).nullMeasurableSet]
  rfl

end MeasureTheory
