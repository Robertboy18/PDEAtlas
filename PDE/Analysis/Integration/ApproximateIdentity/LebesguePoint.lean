/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Integration.ApproximateIdentity.PoissonBound
public import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Vector Poisson kernels at Lebesgue points

A vector kernel with the Poisson size bound and a convergent vector mass recovers a scalar
L¹ density at its Lebesgue points. Only an upper bound on the measure of small balls is needed.
For a hypersurface in dimension `d + 1`, the measure is its actual surface measure and the
mass limit is the outward normal.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace PDE.Analysis

variable {X E : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {x : X} {d : ℕ}

private theorem poisson_weight_le {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) (d : ℕ) :
    t / (t + r) ^ (d + 1) ≤ 1 / t ^ d := by
  calc
    t / (t + r) ^ (d + 1) ≤ t / t ^ (d + 1) :=
      div_le_div_of_nonneg_left ht.le (by positivity)
        (pow_le_pow_left₀ ht.le (by linarith) (d + 1))
    _ = 1 / t ^ d := by rw [pow_succ]; field_simp

omit [BorelSpace X] in
/-- The Poisson size bound makes each positive-height kernel bounded, so multiplication
by any scalar L¹ density is Bochner integrable. -/
theorem integrable_smul_of_poisson_bound {q : X → ℝ} {K : X → E} {C t : ℝ}
    (hq : Integrable q μ) (hK : AEStronglyMeasurable K μ) (hC : 0 ≤ C) (ht : 0 < t)
    (hbound : ∀ᵐ y ∂μ, ‖K y‖ ≤ C * t / (t + dist y x) ^ (d + 1)) :
    Integrable (fun y ↦ q y • K y) μ := by
  apply hq.smul_bdd (C * (1 / t ^ d)) hK
  filter_upwards [hbound] with y hy
  calc
    ‖K y‖ ≤ C * (t / (t + dist y x) ^ (d + 1)) := by simpa [mul_div_assoc] using hy
    _ ≤ C * (1 / t ^ d) := mul_le_mul_of_nonneg_left (poisson_weight_le ht dist_nonneg d) hC

omit [BorelSpace X] in
/-- Upper growth of small balls converts the ordinary Lebesgue-point average into the
power-normalized integral used by the dyadic Poisson estimate. -/
theorem tendsto_ball_integral_div_pow_of_average {f : X → ℝ} {A : ℝ}
    (hf0 : ∀ y, 0 ≤ f y)
    (hfinite : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (closedBall x r) ≠ ∞)
    (hgrowth : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ.real (closedBall x r) ≤ A * r ^ d)
    (hlim : Tendsto (fun r : ℝ ↦ ⨍ y in closedBall x r, f y ∂μ) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun r : ℝ ↦ (∫ y in closedBall x r, f y ∂μ) / r ^ d)
      (𝓝[>] 0) (𝓝 0) := by
  have hupper := hlim.const_mul A
  simp only [mul_zero] at hupper
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : 0 < r := hr
    exact div_nonneg (integral_nonneg hf0) (by positivity)
  · filter_upwards [self_mem_nhdsWithin, hfinite, hgrowth] with r hr hfin hg
    have hr0 : 0 < r := hr
    rw [← measure_smul_setAverage f hfin, smul_eq_mul]
    calc
      μ.real (closedBall x r) * (⨍ y in closedBall x r, f y ∂μ) / r ^ d ≤
          (A * r ^ d) * (⨍ y in closedBall x r, f y ∂μ) / r ^ d := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hg (average_nonneg hf0)) (by positivity)
      _ = A * (⨍ y in closedBall x r, f y ∂μ) := by field_simp

/-- A vector Poisson kernel has vanishing weighted error at a point where the
power-normalized L¹ error on balls vanishes. -/
theorem tendsto_integral_smul_sub_of_poisson_bound [IsFiniteMeasure μ]
    {q : X → ℝ} {a C : ℝ} {K : ℝ → X → E}
    (hq : Integrable q μ) (hC : 0 ≤ C)
    (hK : ∀ᶠ t in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (K t) μ)
    (hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ y ∂μ,
      ‖K t y‖ ≤ C * t / (t + dist y x) ^ (d + 1))
    (hlim : Tendsto (fun r : ℝ ↦ (∫ y in closedBall x r, ‖q y - a‖ ∂μ) / r ^ d)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t : ℝ ↦ ∫ y, (q y - a) • K t y ∂μ) (𝓝[>] 0) (𝓝 0) := by
  have herr : Integrable (fun y ↦ ‖q y - a‖) μ := (hq.sub (integrable_const a)).norm
  have hscalar := (tendsto_integral_poisson_weight herr (fun y ↦ norm_nonneg _) hlim).const_mul C
  simp only [mul_zero] at hscalar
  apply squeeze_zero_norm' ?_ hscalar
  filter_upwards [self_mem_nhdsWithin, hK, hbound] with t ht hKt hbt
  have ht0 : 0 < t := ht
  have hw : AEStronglyMeasurable (fun y ↦ t / (t + dist y x) ^ (d + 1)) μ := by
    apply Continuous.aestronglyMeasurable
    exact continuous_const.div
      ((continuous_const.add (continuous_id.dist continuous_const)).pow (d + 1))
      (fun y ↦ ne_of_gt (pow_pos (by positivity) _))
  have hwi : Integrable (fun y ↦ t / (t + dist y x) ^ (d + 1) * ‖q y - a‖) μ := by
    apply herr.bdd_mul (c := 1 / t ^ d) hw
    filter_upwards with y
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ t / (t + dist y x) ^ (d + 1))]
    exact poisson_weight_le ht0 dist_nonneg d
  have hprod := integrable_smul_of_poisson_bound (hq.sub (integrable_const a))
    hKt hC ht0 hbt
  calc
    ‖∫ y, (q y - a) • K t y ∂μ‖ ≤ ∫ y, ‖(q y - a) • K t y‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, C * (t / (t + dist y x) ^ (d + 1) * ‖q y - a‖) ∂μ := by
      apply integral_mono_ae hprod.norm (hwi.const_mul C)
      filter_upwards [hbt] with y hy
      rw [norm_smul]
      calc
        ‖q y - a‖ * ‖K t y‖ ≤ ‖q y - a‖ *
            (C * t / (t + dist y x) ^ (d + 1)) := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
        _ = _ := by ring
    _ = C * ∫ y, t / (t + dist y x) ^ (d + 1) * ‖q y - a‖ ∂μ := integral_const_mul _ _

/-- A vector kernel with a Poisson bound recovers a scalar L¹ density at an ordinary
Lebesgue point, multiplied by the kernel's vector mass limit. -/
theorem tendsto_integral_smul_of_poisson_bound [IsFiniteMeasure μ]
    {q : X → ℝ} {a A C : ℝ} {K : ℝ → X → E} {v : E}
    (hq : Integrable q μ) (hC : 0 ≤ C)
    (hK : ∀ᶠ t in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (K t) μ)
    (hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ y ∂μ,
      ‖K t y‖ ≤ C * t / (t + dist y x) ^ (d + 1))
    (hgrowth : ∀ᶠ r in 𝓝[>] (0 : ℝ), μ.real (closedBall x r) ≤ A * r ^ d)
    (hlim : Tendsto (fun r : ℝ ↦ ⨍ y in closedBall x r, ‖q y - a‖ ∂μ)
      (𝓝[>] 0) (𝓝 0))
    (hmass : Tendsto (fun t : ℝ ↦ ∫ y, K t y ∂μ) (𝓝[>] 0) (𝓝 v)) :
    Tendsto (fun t : ℝ ↦ ∫ y, q y • K t y ∂μ) (𝓝[>] 0) (𝓝 (a • v)) := by
  have hnormalized := tendsto_ball_integral_div_pow_of_average (fun y ↦ norm_nonneg (q y - a))
    (Eventually.of_forall (fun r ↦ measure_ne_top μ (closedBall x r))) hgrowth hlim
  have herr := tendsto_integral_smul_sub_of_poisson_bound hq hC hK hbound hnormalized
  have h := herr.add (hmass.const_smul a)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin, hK, hbound] with t ht hKt hbt
  have hqi := integrable_smul_of_poisson_bound hq hKt hC ht hbt
  have hai := integrable_smul_of_poisson_bound (integrable_const a) hKt hC ht hbt
  simp_rw [sub_smul]
  rw [integral_sub hqi hai, integral_smul, sub_add_cancel]

/-- Away from any fixed ball, the Poisson bound gives an explicit linear-in-height
bound for the density-weighted vector integral. -/
theorem norm_setIntegral_smul_compl_closedBall_le {q : X → ℝ} {K : X → E} {C t δ : ℝ}
    (hq : Integrable q μ) (hK : AEStronglyMeasurable K μ)
    (hC : 0 ≤ C) (ht : 0 < t) (hδ : 0 < δ)
    (hbound : ∀ᵐ y ∂μ, ‖K y‖ ≤ C * t / (t + dist y x) ^ (d + 1)) :
    ‖∫ y in (closedBall x δ)ᶜ, q y • K y ∂μ‖ ≤
      C * t / δ ^ (d + 1) * ∫ y, ‖q y‖ ∂μ := by
  have hprod := integrable_smul_of_poisson_bound hq hK hC ht hbound
  have hc : 0 ≤ C * t / δ ^ (d + 1) := by positivity
  calc
    ‖∫ y in (closedBall x δ)ᶜ, q y • K y ∂μ‖ ≤
        ∫ y in (closedBall x δ)ᶜ, ‖q y • K y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in (closedBall x δ)ᶜ, (C * t / δ ^ (d + 1)) * ‖q y‖ ∂μ := by
      apply integral_mono_ae hprod.integrableOn.norm (hq.norm.const_mul _).integrableOn
      filter_upwards [ae_restrict_of_ae hbound,
        ae_restrict_mem measurableSet_closedBall.compl] with y hy hymem
      have hyδ : δ < dist y x := by simpa using hymem
      rw [norm_smul]
      have hden : δ ^ (d + 1) ≤ (t + dist y x) ^ (d + 1) :=
        pow_le_pow_left₀ hδ.le (by linarith) (d + 1)
      have hb : ‖K y‖ ≤ C * t / δ ^ (d + 1) := hy.trans
        (div_le_div_of_nonneg_left (mul_nonneg hC ht.le) (by positivity) hden)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (norm_nonneg (q y))
    _ ≤ ∫ y, (C * t / δ ^ (d + 1)) * ‖q y‖ ∂μ :=
      setIntegral_le_integral (hq.norm.const_mul _) (Eventually.of_forall (fun y ↦ by positivity))
    _ = _ := integral_const_mul _ _

/-- Besicovitch differentiation supplies a common full-measure set of points at which
all vector kernels satisfying the size, ball-growth, and mass conditions recover the density.
This applies to finite surface measures on ambient Euclidean space as well as finite volume
restrictions. No total extension of a boundary normal field is required. -/
theorem ae_forall_tendsto_integral_smul_of_poisson_bound
    [SecondCountableTopology X] [HasBesicovitchCovering X] [IsFiniteMeasure μ]
    {q : X → ℝ} (hq : Integrable q μ) :
    ∀ᵐ x ∂μ, ∀ (d : ℕ) (K : ℝ → X → E) (v : E) (A C : ℝ), 0 ≤ C →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (K t) μ) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ y ∂μ,
        ‖K t y‖ ≤ C * t / (t + dist y x) ^ (d + 1)) →
      (∀ᶠ r in 𝓝[>] (0 : ℝ), μ.real (closedBall x r) ≤ A * r ^ d) →
      Tendsto (fun t : ℝ ↦ ∫ y, K t y ∂μ) (𝓝[>] 0) (𝓝 v) →
      Tendsto (fun t : ℝ ↦ ∫ y, q y • K t y ∂μ) (𝓝[>] 0) (𝓝 (q x • v)) := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average_norm_sub hq.locallyIntegrable]
    with x hx
  intro d K v A C hC hK hbound hgrowth hmass
  exact tendsto_integral_smul_of_poisson_bound hq hC hK hbound hgrowth
    (hx.comp (Besicovitch.tendsto_filterAt μ x)) hmass

end PDE.Analysis
