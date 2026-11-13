/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
import CAS.ExactTactic

/-!
# Lebesgue points in finite `Lᵖ`

Scalar Lebesgue differentiation applied to distances from a countable dense set gives
vanishing mean `p`-th power oscillation. The exceptional set is chosen before the center
value is substituted; no continuity of the function is required.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace IsUnifLocDoublingMeasure

private theorem norm_sub_rpow_le {E : Type*} [NormedAddCommGroup E]
    (a b c : E) {q : ℝ} (hq : 0 ≤ q) :
    ‖a - b‖ ^ q ≤ 2 ^ q * (‖a - c‖ ^ q + ‖b - c‖ ^ q) := by
  calc
    ‖a - b‖ ^ q ≤ (‖a - c‖ + ‖b - c‖) ^ q := by
      gcongr
      simpa only [dist_eq_norm] using dist_triangle_right a b c
    _ ≤ (2 * max ‖a - c‖ ‖b - c‖) ^ q := by
      gcongr
      linarith [le_max_left ‖a - c‖ ‖b - c‖, le_max_right ‖a - c‖ ‖b - c‖]
    _ = 2 ^ q * max (‖a - c‖ ^ q) (‖b - c‖ ^ q) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.rpow_max (norm_nonneg _) (norm_nonneg _) hq]
    _ ≤ _ := by
      gcongr
      exact max_le_add_of_nonneg (by positivity) (by positivity)

/-- A locally `Lᵖ` function, for `0 < p < ∞`, has vanishing mean `p`-th power oscillation
at almost every point. The measure is locally finite and uniformly locally doubling. -/
theorem ae_tendsto_average_norm_sub_rpow
    {α E : Type*} [MetricSpace α] [ProperSpace α]
    [MeasurableSpace α] [BorelSpace α] [NormedAddCommGroup E] [SecondCountableTopology E]
    (μ : Measure α) [IsLocallyFiniteMeasure μ] [IsUnifLocDoublingMeasure μ]
    [μ.IsOpenPosMeasure] {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp_top : p ≠ ∞)
    {f : α → E} (hf : ∀ K : Set α, IsCompact K → MemLp f p (μ.restrict K)) :
    ∀ᵐ x ∂μ, Tendsto
      (fun r : ℝ ↦ ⨍ y in closedBall x r, ‖f y - f x‖ ^ p.toReal ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp_top
  have hlocal (c : E) : LocallyIntegrable (fun y ↦ ‖f y - c‖ ^ p.toReal) μ := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact ((hf K hK).sub (memLp_const c)).integrable_norm_rpow hp₀ hp_top
  obtain ⟨s, hs, hdense⟩ := TopologicalSpace.exists_countable_dense E
  have hall : ∀ᵐ x ∂μ, ∀ c ∈ s, Tendsto
      (fun r : ℝ ↦ ⨍ y in closedBall x r, ‖f y - c‖ ^ p.toReal ∂μ)
      (𝓝[>] 0) (𝓝 (‖f x - c‖ ^ p.toReal)) := by
    rw [ae_ball_iff hs]
    intro c _
    filter_upwards [ae_tendsto_average μ (hlocal c) 1] with x hx
    apply hx (fun _ ↦ x) id tendsto_id
    filter_upwards [self_mem_nhdsWithin] with r hr
    simpa only [one_mul, mem_closedBall, dist_self, id_eq] using le_of_lt hr
  filter_upwards [hall] with x hx
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A : ℝ := 2 ^ p.toReal
  have hA : 0 < A := Real.rpow_pos_of_pos (by norm_num) _
  have hcont : Continuous (fun c : E ↦ ‖f x - c‖ ^ p.toReal) :=
    (continuous_const.sub continuous_id).norm.rpow_const (fun _ ↦ Or.inr hp.le)
  obtain ⟨c, hc, hclose⟩ := hdense.exists_mem_open
    (isOpen_lt hcont continuous_const)
    (show ({c : E | ‖f x - c‖ ^ p.toReal < ε / (4 * A)} : Set E).Nonempty from
      ⟨f x, by simpa only [mem_ofPred_eq, sub_self, norm_zero, Real.zero_rpow hp.ne'] using
        div_pos hε (by positivity : 0 < 4 * A)⟩)
  have hsmall := (tendsto_order.mp (hx c hc)).2 (ε / (2 * A))
    (hclose.trans (by
      exact div_lt_div_of_pos_left hε (by positivity) (by linarith)))
  filter_upwards [hsmall, self_mem_nhdsWithin] with r hr hrpos
  have hfinite : μ (closedBall x r) ≠ ∞ := (isCompact_closedBall x r).measure_lt_top.ne
  have hpos : μ (closedBall x r) ≠ 0 := (measure_closedBall_pos μ x hrpos).ne'
  have hint c : IntegrableOn (fun y ↦ ‖f y - c‖ ^ p.toReal) (closedBall x r) μ :=
    (hlocal c).integrableOn_isCompact (isCompact_closedBall x r)
  have hbound :
      (⨍ y in closedBall x r, ‖f y - f x‖ ^ p.toReal ∂μ) ≤
        A * ((⨍ y in closedBall x r, ‖f y - c‖ ^ p.toReal ∂μ) +
          ‖f x - c‖ ^ p.toReal) := by
    rw [← setAverage_const hpos hfinite (‖f x - c‖ ^ p.toReal),
      ← average_add (hint c) (integrableOn_const hfinite), ← average_const_mul]
    simp only [average_eq, smul_eq_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply integral_mono (hint (f x)) (((hint c).add (integrableOn_const hfinite)).const_mul A)
    intro y
    exact norm_sub_rpow_le (f y) (f x) c hp.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (average_nonneg (fun _ ↦ by positivity))]
  apply hbound.trans_lt
  have hc' : ‖f x - c‖ ^ p.toReal < ε / (2 * A) :=
    hclose.trans (div_lt_div_of_pos_left hε (by positivity) (by linarith))
  calc
    A * ((⨍ y in closedBall x r, ‖f y - c‖ ^ p.toReal ∂μ) +
        ‖f x - c‖ ^ p.toReal) < A * (ε / (2 * A) + ε / (2 * A)) := by gcongr
    _ = ε := by cas using hA.ne'

end IsUnifLocDoublingMeasure
