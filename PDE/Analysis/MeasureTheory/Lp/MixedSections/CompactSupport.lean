/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.SectionReconstruction
import PDE.Analysis.MeasureTheory.Lp.Continuous

/-!
# Compactly supported continuous forcing as an L1L2 field

A continuous field on a finite time interval with common compact spatial support
has an actual Bochner L1L2 class. Its norm equals the integral of its physical
spatial L2 norms. The construction uses product L2 section reconstruction and
the finite measure of the time interval; no measurability outside the cylinder
is assumed.
-/

@[expose] public section

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal

namespace MeasureTheory

/-- Continuous fields with common compact spatial support on a closed finite
interval determine actual L1L2 forcing classes, with their exact physical norm. -/
theorem exists_L1_L2_sections_of_continuousOn_compact_support
    {X E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [T2Space X]
    [NormedAddCommGroup E]
    {ν : Measure X} [SFinite ν] [IsFiniteMeasureOnCompacts ν]
    [SeparableSpace (Lp E 2 ν)] {a b : ℝ} {F : ℝ × X → E} {K : Set X}
    (hK : IsCompact K) (hF : ContinuousOn F (Icc a b ×ˢ K))
    (hzero : ∀ t ∈ Icc a b, ∀ x, x ∉ K → F (t, x) = 0) :
    ∃ f : Lp (Lp E 2 ν) 1 (volume.restrict (Icc a b)),
      (∀ᵐ t ∂volume.restrict (Icc a b),
        (fun x ↦ F (t, x)) =ᵐ[ν] (f t : X → E)) ∧
      ‖f‖ = ∫ t in Icc a b, lpNorm (fun x ↦ F (t, x)) 2 ν := by
  classical
  let C := Icc a b ×ˢ K
  have hC : IsCompact C := isCompact_Icc.prod hK
  have hmeas : MeasurableSet C := hC.isClosed.measurableSet
  let V := C.indicator F
  have hV : MemLp V 2 (volume.prod ν) :=
    (memLp_indicator_iff_restrict hmeas.nullMeasurableSet).mpr
      (hF.memLp_of_subset_isCompact hC hmeas Subset.rfl)
  have hV' : MemLp V 2 ((volume.restrict (Icc a b)).prod ν) :=
    hV.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  obtain ⟨v, hv, _⟩ := hV'.exists_L2_sections
  have h1 : MemLp (fun t ↦ v t) 1 (volume.restrict (Icc a b)) :=
    (Lp.memLp v).mono_exponent (by norm_num)
  let f := h1.toLp (fun t ↦ v t)
  have hf : ∀ᵐ t ∂volume.restrict (Icc a b),
      (fun x ↦ F (t, x)) =ᵐ[ν] (f t : X → E) := by
    filter_upwards [hv, h1.coeFn_toLp, ae_restrict_mem measurableSet_Icc] with t ht hft htab
    rw [hft]
    filter_upwards [ht] with x hx
    rw [← hx]
    by_cases hxK : x ∈ K
    · exact (indicator_of_mem (show (t, x) ∈ C from ⟨htab, hxK⟩) F).symm
    · rw [hzero t htab x hxK]
      exact (indicator_of_notMem (show (t, x) ∉ C from fun h ↦ hxK h.2) F).symm
  refine ⟨f, hf, ?_⟩
  rw [L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [hf] with t ht
  rw [Lp.norm_def, ← eLpNorm_congr_ae ht]
  rfl

end MeasureTheory
