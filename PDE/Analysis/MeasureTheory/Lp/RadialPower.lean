/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Lᵖ integrability of radial powers

On a bounded set in a finite-dimensional real normed space, `‖x-z‖^a` belongs
to a finite `Lᵖ` space when `-a * p < dim`. The centre may lie on the boundary.
We translate Mathlib's local integrability theorem and restrict it to the compact
closure; neither regularity nor connectedness of the set is needed.
-/

@[expose] public section

open Function Set
open scoped ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A radial power belongs to every finite Lᵖ space allowed by the dimensional
integrability criterion, on any bounded set and about any centre. -/
theorem memLp_norm_sub_rpow_of_isBounded
    (hd : 1 ≤ Module.finrank ℝ E) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ∞) {a : ℝ}
    (ha : -a * p.toReal < (Module.finrank ℝ E : ℝ))
    (z : E) {s : Set E} (hs : Bornology.IsBounded s) :
    MemLp (fun x ↦ ‖x - z‖ ^ a) p (μ.restrict s) := by
  have hm : Measurable (fun x : E ↦ ‖x‖ ^ a) := by fun_prop
  have hlocal : LocallyIntegrable (fun x : E ↦ ‖x‖ ^ (a * p.toReal)) μ := by
    apply locallyIntegrable_of_norm_le_rpow hd ha (C := 1)
    · apply Filter.Eventually.of_forall
      intro x
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
      rw [show -(-a * p.toReal) = a * p.toReal by ring]
    · exact (measurable_norm.pow_const (a * p.toReal)).aestronglyMeasurable
  have hshift : LocallyIntegrable (fun x : E ↦ ‖x - z‖ ^ (a * p.toReal)) μ := by
    have h := (locallyIntegrable_map_homeomorph (Homeomorph.addRight (-z))
      (f := fun x : E ↦ ‖x‖ ^ (a * p.toReal)) (μ := μ)).mp
    simpa only [Homeomorph.coe_addRight, map_add_right_eq_self, comp_def, sub_eq_add_neg]
      using h (by simpa only [Homeomorph.coe_addRight, map_add_right_eq_self] using hlocal)
  apply (integrable_norm_rpow_iff
    (hm.comp (measurable_id.sub_const z)).aestronglyMeasurable.restrict hp hp').mp
  change Integrable (fun x : E ↦ ‖‖x - z‖ ^ a‖ ^ p.toReal) (μ.restrict s)
  simpa only [IntegrableOn, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg _)] using
    (hshift.integrableOn_isCompact hs.isCompact_closure).mono_set subset_closure

end MeasureTheory
