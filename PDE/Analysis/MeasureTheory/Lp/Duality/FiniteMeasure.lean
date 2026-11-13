/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.Duality

/-!
# Exact scalar dual representation over finite measures

An integrable density representing an `L¹` functional on indicators is essentially
bounded by the operator norm. Upper and lower bounds on every set integral give
the pointwise bound almost everywhere. The indicator extension then
identifies the functional with Mathlib's integral pairing against an `L∞` element.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ENNReal NNReal

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Hölder's inequality bounds the norm of scalar integral pairing by the density norm. -/
theorem norm_lpPairing_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (g : Lp ℝ q μ) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro f
  rw [ContinuousLinearMap.lpPairing_eq_integral,
    ← integral_congr_ae ((ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) g f),
    ← L1.integral_eq_integral]
  exact (L1.norm_integral_le _).trans (by
    simpa using (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le (r := 1) g f)

variable [IsFiniteMeasure μ]

/-- A density representing an `L¹` functional on indicators is bounded almost everywhere
by its operator norm. The density is only assumed integrable before this estimate. -/
theorem norm_ae_le_opNorm_of_indicator_eq_one
    (Λ : StrongDual ℝ (Lp ℝ 1 μ)) {g : α → ℝ} (hg : Integrable g μ)
    (hset : ∀ (s : Set α) (hs : MeasurableSet s),
      Λ (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ)) = ∫ x in s, g x ∂μ) :
    ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖Λ‖ := by
  have hbound (s : Set α) (hs : MeasurableSet s) :
      ‖∫ x in s, g x ∂μ‖ ≤ ‖Λ‖ * μ.real s := by
    rw [← hset s hs]
    simpa only [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top, norm_one,
      ENNReal.toReal_one, div_one, Real.rpow_one, one_mul] using
      Λ.le_opNorm (indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ))
  have hupper : g ≤ᵐ[μ] fun _ ↦ ‖Λ‖ := by
    apply ae_le_of_forall_setIntegral_le hg (integrable_const _)
    intro s hs _
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using
      (le_abs_self (∫ x in s, g x ∂μ)).trans (hbound s hs)
  have hlower : (fun _ ↦ -‖Λ‖) ≤ᵐ[μ] g := by
    apply ae_le_of_forall_setIntegral_le (integrable_const _) hg
    intro s hs _
    have h := (neg_le_abs (∫ x in s, g x ∂μ)).trans (hbound s hs)
    simpa only [setIntegral_const, smul_eq_mul, mul_neg, neg_mul, neg_neg, mul_comm] using
      neg_le_neg h
  filter_upwards [hupper, hlower] with x hu hl
  exact abs_le.mpr ⟨hl, hu⟩

/-- Every scalar `L¹` functional on a finite measure is represented by an `L∞` density
with exactly the operator norm. -/
theorem exists_dualDensity_one (Λ : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∃ g : Lp ℝ ∞ μ, ‖g‖ = ‖Λ‖ ∧
      Λ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ 1 g := by
  obtain ⟨g, _, hg, hset⟩ := exists_integrable_dualDensity ENNReal.one_ne_top Λ
  have hbound := norm_ae_le_opNorm_of_indicator_eq_one Λ hg hset
  have hgq := memLp_top_of_bound hg.aestronglyMeasurable ‖Λ‖ hbound
  have hrepr := eq_lpPairing_of_indicator_eq ENNReal.one_ne_top Λ hg hgq hset
  refine ⟨hgq.toLp g, le_antisymm ?_ ?_, hrepr⟩
  · rw [Lp.norm_toLp, eLpNorm_exponent_top hg.aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (eLpNormEssSup_le_of_ae_bound hbound)).trans_eq
      (ENNReal.toReal_ofReal (norm_nonneg Λ))
  · rw [hrepr]
    exact norm_lpPairing_le _

/-- Every scalar `Lp` functional on a finite measure, for `1 ≤ p < ∞`, has a conjugate
density with exactly its operator norm. This includes `p = 1` and `q = ∞`. -/
theorem exists_dualDensity_norm_eq_of_finite {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    (hp : p ≠ ∞) (Λ : StrongDual ℝ (Lp ℝ p μ)) :
    ∃ g : Lp ℝ q μ, ‖g‖ = ‖Λ‖ ∧
      Λ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p g := by
  by_cases hq : q = ∞
  · subst q
    have hpone : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).mp rfl
    subst p
    exact exists_dualDensity_one Λ
  · obtain ⟨g, hnorm, hg⟩ := exists_dualDensity hp hq Λ
    have hrepr : Λ = (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ q p g := by
      ext f
      rw [hg, ContinuousLinearMap.lpPairing_eq_integral]
      simp only [ContinuousLinearMap.mul_apply', mul_comm]
    exact ⟨g, le_antisymm hnorm (hrepr ▸ norm_lpPairing_le g), hrepr⟩

end MeasureTheory.Lp
