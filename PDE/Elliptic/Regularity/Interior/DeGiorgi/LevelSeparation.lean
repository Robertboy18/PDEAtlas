/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.C1DomainTruncation
import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.FiniteExponent

/-!
# Separation of Sobolev level sets

The measures below and above two levels are controlled by the weak gradient
between those levels. Apply mean-subtracted `L¹` Poincaré to the interval
truncation. Its derivative vanishes outside the intermediate strip.
This is the level-separation estimate used in the De Giorgi oscillation argument.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev ENNReal

namespace SobolevSpace.GraphSpace

private theorem measure_product_le_mean_deviation
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {A B : Set X} (v : X → ℝ) (a b m : ℝ)
    (hA : ∀ᵐ x ∂μ.restrict A, v x = a)
    (hB : ∀ᵐ x ∂μ.restrict B, v x = b)
    (hv : Integrable (fun x ↦ ‖v x - m‖) μ) :
    (b - a) * μ.real A * μ.real B ≤
      2 * μ.real univ * ∫ x, ‖v x - m‖ ∂μ := by
  have hI {S : Set X} {c : ℝ} (hS : ∀ᵐ x ∂μ.restrict S, v x = c) :
      μ.real S * ‖c - m‖ ≤ ∫ x, ‖v x - m‖ ∂μ := by
    rw [← smul_eq_mul, ← setIntegral_const,
      ← integral_congr_ae (hS.mono fun _ hx ↦ congrArg (fun y ↦ ‖y - m‖) hx)]
    exact setIntegral_le_integral hv (.of_forall fun _ ↦ norm_nonneg _)
  have hIA := hI hA
  have hIB := hI hB
  have hAu := measureReal_mono (μ := μ) (subset_univ A)
  have hBu := measureReal_mono (μ := μ) (subset_univ B)
  have : (0 : ℝ) ≤ ∫ x, ‖v x - m‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  calc
    _ ≤ (‖a - m‖ + ‖b - m‖) * μ.real A * μ.real B := by
      gcongr
      simp only [Real.norm_eq_abs]
      linarith [le_abs_self (b - m), neg_abs_le (a - m)]
    _ = μ.real B * (μ.real A * ‖a - m‖) + μ.real A * (μ.real B * ‖b - m‖) := by ring
    _ ≤ μ.real univ * (∫ x, ‖v x - m‖ ∂μ) + μ.real univ * (∫ x, ‖v x - m‖ ∂μ) := by gcongr
    _ = _ := by ring

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}
variable [hΩ : Boundary.C1ExtensionAtlas n Ω]

/-- On a connected `C¹` extension domain, the product of the measures below
and above two levels is bounded by the `L¹` weak gradient in the intervening
strip, divided by the distance between the levels. The constant is chosen
before the levels and the arbitrary `W¹¹` element. -/
theorem exists_level_separation_le_strip_gradient (hconn : IsConnected Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : W^{1,1}(Ω)) (a b : ℝ), a ≤ b →
      (b - a) *
        (domainMeasure n Ω).real {x | wkpBaseCoordinateCLM U x ≤ a} *
        (domainMeasure n Ω).real {x | b ≤ wkpBaseCoordinateCLM U x} ≤
      C * ∑ i, ∫ x in {x | a < wkpBaseCoordinateCLM U x ∧ wkpBaseCoordinateCLM U x < b},
        ‖wkpCoordinateCLM (singleDerivIndex n i) U x‖ ∂domainMeasure n Ω := by
  obtain ⟨P, hP, hPoincare⟩ := exists_norm_subtractMean_le_one_of_c1Domain hconn
  let μ := domainMeasure n Ω
  refine ⟨2 * (μ.real univ + 1) * P, by positivity, ?_⟩
  intro U a b hab
  let V : W^{1,1}(Ω) := intervalTruncationOn (by norm_num) hab U
  let m : ℝ := ⨍ x, wkpBaseCoordinateCLM V x ∂μ
  let E := {x | a < wkpBaseCoordinateCLM U x ∧ wkpBaseCoordinateCLM U x < b}
  have hU := (Lp.stronglyMeasurable (wkpBaseCoordinateCLM U)).measurable
  have hE : MeasurableSet E := (measurableSet_lt measurable_const hU).inter
    (measurableSet_lt hU measurable_const)
  have hVbase : (wkpBaseCoordinateCLM V : ℝ^n → ℝ) =ᵐ[μ]
      fun x ↦ min b (max a (wkpBaseCoordinateCLM U x)) := by
    have h := intervalTruncationOn_base_ae (by norm_num) hab U
    change (wkpBaseCoordinateCLM V : ℝ^n → ℝ) =ᵐ[μ]
      fun x ↦ PDE.Analysis.Calculus.intervalTruncation a b (wkpBaseCoordinateCLM U x) at h
    simpa only [PDE.Analysis.Calculus.intervalTruncation_eq_min_max hab] using h
  have hA : ∀ᵐ x ∂μ.restrict {x | wkpBaseCoordinateCLM U x ≤ a},
      wkpBaseCoordinateCLM V x = a := by
    filter_upwards [hVbase.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (measurableSet_le hU measurable_const)] with x hx hax
    rw [hx, max_eq_left hax, min_eq_right hab]
  have hB : ∀ᵐ x ∂μ.restrict {x | b ≤ wkpBaseCoordinateCLM U x},
      wkpBaseCoordinateCLM V x = b := by
    filter_upwards [hVbase.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem (measurableSet_le measurable_const hU)] with x hx hbx
    rw [hx, max_eq_right (hab.trans hbx), min_eq_left hbx]
  have hint : Integrable (fun x ↦ ‖wkpBaseCoordinateCLM V x - m‖) μ :=
    ((memLp_one_iff_integrable.mp (Lp.memLp (wkpBaseCoordinateCLM V))).sub
      (integrable_const m)).norm
  have hmean : (∫ x, ‖wkpBaseCoordinateCLM V x - m‖ ∂μ) ≤ P * ‖∇ V‖ :=
    ((integral_congr_ae ((subtractMean_base_ae V).fun_comp norm)).symm.trans
      (L1.norm_eq_integral_norm _).symm).trans_le
        ((wkpBaseCoordinateCLM_norm_le _).trans (hPoincare V))
  have hD (i : Fin n) :
      ‖wkpCoordinateCLM (singleDerivIndex n i) V‖ =
        ∫ x in E, ‖wkpCoordinateCLM (singleDerivIndex n i) U x‖ ∂μ := by
    rw [L1.norm_eq_integral_norm, ← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards [intervalTruncationOn_derivative_indicator_ae (by norm_num) hab U i]
      with x hx
    change wkpCoordinateCLM (singleDerivIndex n i) V x =
      if x ∈ E then wkpCoordinateCLM (singleDerivIndex n i) U x else 0 at hx
    rw [hx]
    by_cases hxE : x ∈ E <;> simp [hxE]
  have hgrad : ‖∇ V‖ ≤ ∑ i, ∫ x in E, ‖wkpCoordinateCLM (singleDerivIndex n i) U x‖ ∂μ :=
    (wkpGradientCLM_norm_le_sum V).trans_eq (Finset.sum_congr rfl fun i _ ↦ hD i)
  have hJ := hmean.trans (mul_le_mul_of_nonneg_left hgrad hP.le)
  have hI0 : 0 ≤ ∫ x, ‖wkpBaseCoordinateCLM V x - m‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  refine (measure_product_le_mean_deviation μ _ a b m hA hB hint).trans ?_
  nlinarith [mul_nonneg (measureReal_nonneg (μ := μ) (s := univ)) (sub_nonneg.2 hJ)]

end SobolevSpace.GraphSpace
