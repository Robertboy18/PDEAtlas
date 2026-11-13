/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Analysis.MeasureTheory.Lp.JointRepresentative.Mixed

/-!
# Local integrability of mixed Lebesgue representatives

A mixed Lebesgue class with both exponents at least one is integrable against
any product of finite submeasures. Hölder exponent comparison and Tonelli give
this directly for its actual jointly measurable representative, including
infinite exponents. Consequently, s-finite measures finite on compact sets give
local integrability without an additional integrability hypothesis.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Lp

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [_root_.SecondCountableTopology E] {μ : Measure α} {ν : Measure β}
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A mixed Lp class is integrable against a product of finite submeasures.
This derives the local integrability of its actual jointly measurable representative. -/
theorem integrable_jointRepresentative_of_finite_submeasures
    (u : Lp (Lp E p ν) q μ) (μ' : Measure α) (ν' : Measure β)
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν'] (hμ : μ' ≤ μ) (hν : ν' ≤ ν) :
    Integrable (jointRepresentative u) (μ'.prod ν') := by
  have hU := (measurable_jointRepresentative u).stronglyMeasurable.aestronglyMeasurable
    (μ := μ'.prod ν')
  have hpow : 0 ≤ 1 - 1 / p.toReal := by
    by_cases hp : p = ∞
    · simp [hp]
    · have hp1 : 1 ≤ p.toReal := by
        simpa only [ENNReal.toReal_one] using
          ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
      exact sub_nonneg.mpr (by
        simpa only [div_one] using one_div_le_one_div_of_le (by norm_num) hp1)
  let C : ℝ≥0∞ := (ν' univ) ^ (1 - 1 / p.toReal)
  have hC : C < ∞ := ENNReal.rpow_lt_top_of_nonneg hpow (measure_ne_top ν' univ)
  have hslice (t : α) :
      (∫⁻ x, ‖jointRepresentative u (t, x)‖ₑ ∂ν') ≤ ‖u t‖ₑ * C := by
    have hm : AEStronglyMeasurable (fun x ↦ jointRepresentative u (t, x)) ν' :=
      ((measurable_jointRepresentative u).comp
        (measurable_const.prodMk measurable_id)).stronglyMeasurable.aestronglyMeasurable
    rw [← eLpNorm_one_eq_lintegral_enorm hm]
    calc
      _ ≤ eLpNorm (fun x ↦ jointRepresentative u (t, x)) p ν' * C := by
        simpa only [ENNReal.toReal_one, div_one] using
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (Fact.out : 1 ≤ p) hm
      _ ≤ eLpNorm (fun x ↦ jointRepresentative u (t, x)) p ν * C :=
        mul_le_mul (eLpNorm_mono_measure _ hν) le_rfl bot_le bot_le
      _ = _ := by
        rw [eLpNorm_congr_ae (jointRepresentative_section u t), ← Lp.enorm_def]
  have hi : Integrable (fun t ↦ u t) μ' :=
    ((Lp.memLp u).mono_measure hμ).integrable (Fact.out : 1 ≤ q)
  refine ⟨hU, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hU.enorm]
  calc
    _ ≤ ∫⁻ t, ‖u t‖ₑ * C ∂μ' := lintegral_mono hslice
    _ = (∫⁻ t, ‖u t‖ₑ ∂μ') * C :=
      lintegral_mul_const'' C hi.aestronglyMeasurable.enorm
    _ < ∞ := ENNReal.mul_lt_top
      (hasFiniteIntegral_iff_enorm.mp hi.hasFiniteIntegral) hC

/-- Finite measure rectangles give integrability of the joint representative. -/
theorem integrableOn_jointRepresentative_prod [SFinite μ] [SFinite ν]
    (u : Lp (Lp E p ν) q μ) {A : Set α} {B : Set β}
    (hA : μ A ≠ ∞) (hB : ν B ≠ ∞) :
    IntegrableOn (jointRepresentative u) (A ×ˢ B) (μ.prod ν) := by
  let : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hA
  let : IsFiniteMeasure (ν.restrict B) := isFiniteMeasure_restrict.mpr hB
  rw [IntegrableOn, ← Measure.prod_restrict]
  exact integrable_jointRepresentative_of_finite_submeasures u _ _
    Measure.restrict_le_self Measure.restrict_le_self

/-- Mixed normed Lebesgue classes have locally integrable joint representatives
when both measures are finite on compact sets. -/
theorem locallyIntegrable_jointRepresentative [SFinite μ] [SFinite ν]
    [TopologicalSpace α] [TopologicalSpace β]
    [LocallyCompactSpace α] [LocallyCompactSpace β]
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (u : Lp (Lp E p ν) q μ) :
    LocallyIntegrable (jointRepresentative u) (μ.prod ν) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi := integrableOn_jointRepresentative_prod u
    (hK.image continuous_fst).measure_ne_top (hK.image continuous_snd).measure_ne_top
  exact hi.mono_set (fun z hz ↦ ⟨⟨z, hz, rfl⟩, ⟨z, hz, rfl⟩⟩)

end MeasureTheory.Lp
