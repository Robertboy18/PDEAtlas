/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Comparing finite `PiLp` norms at different exponents

On a finite index set `ι` with `q ≤ p`, the `ℓ^q` norm is controlled by the
`ℓ^p` norm at the cost of the cardinality factor `(card ι)^(1/q - 1/p)`:

  `‖y‖_q ≤ (card ι)^(1/q - 1/p) · ‖x‖_p` whenever `‖y i‖ ≤ ‖x i‖` for all `i`.

This is Hölder's inequality on the finite measure space `(ι, count)`, and the
constant is attained by constant vectors. The proof identifies a finite `PiLp`
norm with the `Lᵖ` seminorm of the coordinate norms for counting measure and
applies Mathlib's comparison `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`.
The statement allows different coordinate types `β` and `γ` for `x` and `y`,
so it applies to operators bounded coordinatewise between two `PiLp` spaces.

## Main results

* `eLpNorm_coordinate_norm_count_eq_enorm`: for `x : PiLp p β`,
  `eLpNorm (fun i ↦ ‖x i‖) p count = ‖x‖ₑ`, including `p = ∞`.
* `norm_le_card_rpow_mul_of_coordinate_norm_le`: the exponent comparison
  with explicit cardinality factor, for `1 ≤ q ≤ p ≤ ∞`.
-/

@[expose] public section

noncomputable section


open MeasureTheory
open scoped ENNReal

namespace PiLp

/-- A finite `ℓᵖ` norm is bounded by the sum of coordinate norms for every
`1 ≤ p ≤ ∞`. -/
theorem norm_le_sum_norm {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)] (v : PiLp p β) :
    ‖v‖ ≤ ∑ i, ‖v i‖ := by
  classical
  have hv : v = ∑ i, PiLp.single p i (v i) := by
    ext i
    simp
  calc
    ‖v‖ = ‖∑ i, PiLp.single p i (v i)‖ := congrArg norm hv
    _ ≤ ∑ i, ‖PiLp.single p i (v i)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ := by simp


/-- For exponents `1 ≤ q ≤ p`, the reciprocal gap `1 / q - 1 / p` is nonnegative. -/
theorem exponentGap_nonneg
    {p q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hpq : q ≤ p) :
    0 ≤ 1 / q.toReal - 1 / p.toReal := by
  rw [sub_nonneg]
  by_cases hpTop : p = ∞
  · simp [hpTop]
  have hqTop : q ≠ ∞ :=
    ne_top_of_le_ne_top hpTop hpq
  have hqZero : q ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hqPos : 0 < q.toReal :=
    ENNReal.toReal_pos hqZero hqTop
  exact one_div_le_one_div_of_le hqPos
    (ENNReal.toReal_mono hpTop hpq)

/-- The `Lᵖ` seminorm of the coordinate norms for counting measure equals
the extended norm of a finite `PiLp` vector. -/
theorem eLpNorm_coordinate_norm_count_eq_enorm
    {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {β : ι → Type*} [∀ i, NormedAddCommGroup (β i)]
    (x : PiLp p β) :
    eLpNorm (fun i ↦ ‖x i‖) p Measure.count = ‖x‖ₑ := by
  have hxMeas :
      AEStronglyMeasurable (fun i ↦ ‖x i‖) Measure.count :=
    (measurable_of_countable _).aestronglyMeasurable
  rcases p.dichotomy with rfl | hp
  · rw [eLpNorm_exponent_top hxMeas, eLpNormEssSup_count,
      enorm_eq_nnnorm, PiLp.nnnorm_eq_ciSup]
    simp only [enorm_eq_nnnorm, nnnorm_norm]
    exact
      (ENNReal.coe_iSup
        (Set.finite_range fun i ↦ ‖x i‖₊).bddAbove).symm
  · have hpTop : p ≠ ∞ := by
      intro h
      rw [h, ENNReal.toReal_top] at hp
      linarith
    have hpZero : p ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
    rw [eLpNorm_eq_eLpNorm' hpZero hpTop hxMeas, enorm_eq_nnnorm,
      PiLp.nnnorm_eq_sum hpTop]
    simp only [eLpNorm', lintegral_count, enorm_eq_nnnorm]
    rw [tsum_fintype,
      ENNReal.coe_rpow_of_nonneg _ (by positivity),
      ENNReal.ofNNReal_finsetSum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [ENNReal.coe_rpow_of_nonneg]

/-- Compare finite `PiLp` norms at exponents `q ≤ p` from a uniform
coordinate estimate. The loss is the sharp finite-dimensional cardinality
factor. -/
theorem norm_le_card_rpow_mul_of_coordinate_norm_le
    {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {β γ : ι → Type*}
    [∀ i, NormedAddCommGroup (β i)]
    [∀ i, NormedAddCommGroup (γ i)]
    (hpq : q ≤ p) (c : ℝ) (hc : 0 ≤ c)
    (x : PiLp p β) (y : PiLp q γ)
    (hxy : ∀ i, ‖y i‖ ≤ c * ‖x i‖) :
    ‖y‖ ≤
      ((Fintype.card ι : ℝ≥0∞) ^
          (1 / q.toReal - 1 / p.toReal)).toReal *
        c * ‖x‖ := by
  have hxMeas :
      AEStronglyMeasurable (fun i ↦ ‖x i‖) Measure.count :=
    (measurable_of_countable _).aestronglyMeasurable
  have houter :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hxMeas
  have hpoint :
      eLpNorm (fun i ↦ ‖y i‖) q Measure.count ≤
        eLpNorm (fun i ↦ c * ‖x i‖) q Measure.count := by
    apply eLpNorm_mono
      (measurable_of_countable (fun i ↦ ‖y i‖)).aestronglyMeasurable
    intro i
    simpa [Real.norm_of_nonneg hc,
      Real.norm_of_nonneg (mul_nonneg hc (norm_nonneg _))]
      using hxy i
  have hscale :
      eLpNorm (fun i ↦ c * ‖x i‖) q Measure.count =
        ENNReal.ofReal c *
          eLpNorm (fun i ↦ ‖x i‖) q Measure.count := by
    change
      eLpNorm (c • fun i ↦ ‖x i‖) q Measure.count =
        ENNReal.ofReal c *
          eLpNorm (fun i ↦ ‖x i‖) q Measure.count
    simpa [Real.enorm_eq_ofReal hc] using
      (eLpNorm_const_smul c (fun i ↦ ‖x i‖) q Measure.count)
  have hraw :
      ‖y‖ₑ ≤
        ENNReal.ofReal c *
          (‖x‖ₑ *
            (Fintype.card ι : ℝ≥0∞) ^
              (1 / q.toReal - 1 / p.toReal)) := by
    rw [← eLpNorm_coordinate_norm_count_eq_enorm y,
      ← eLpNorm_coordinate_norm_count_eq_enorm x]
    calc
      eLpNorm (fun i ↦ ‖y i‖) q Measure.count
          ≤ eLpNorm (fun i ↦ c * ‖x i‖) q Measure.count :=
        hpoint
      _ = ENNReal.ofReal c *
          eLpNorm (fun i ↦ ‖x i‖) q Measure.count :=
        hscale
      _ ≤ ENNReal.ofReal c *
          (eLpNorm (fun i ↦ ‖x i‖) p Measure.count *
            Measure.count Set.univ ^
              (1 / q.toReal - 1 / p.toReal)) := by
        gcongr
      _ = ENNReal.ofReal c *
          (eLpNorm (fun i ↦ ‖x i‖) p Measure.count *
            (Fintype.card ι : ℝ≥0∞) ^
              (1 / q.toReal - 1 / p.toReal)) := by
        rw [Measure.count_univ, ENat.card_eq_coe_fintype_card]
        rfl
  have hfinite :
      ENNReal.ofReal c *
          (‖x‖ₑ *
            (Fintype.card ι : ℝ≥0∞) ^
              (1 / q.toReal - 1 / p.toReal)) ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top enorm_ne_top
        (ENNReal.rpow_ne_top_of_nonneg
          (exponentGap_nonneg hpq) ENNReal.coe_ne_top))
  have hreal := ENNReal.toReal_mono hfinite hraw
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc,
    toReal_enorm, mul_assoc, mul_left_comm, mul_comm] using hreal

end PiLp
