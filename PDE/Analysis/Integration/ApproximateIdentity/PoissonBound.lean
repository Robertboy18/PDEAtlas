/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Approximate identities with a Poisson bound

Dyadic balls control kernels bounded by `t / (t + dist y x) ^ (d + 1)` using
ordinary Lebesgue-point data in dimension `d`. The measure need not be volume:
the estimates also apply to surface measure, with `d` the surface dimension.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace PDE.Analysis

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  {μ : Measure X} {x : X} {f : X → ℝ} {d : ℕ}

private theorem dyadic_coefficient (k d : ℕ) {t : ℝ} (ht : 0 < t) :
    t / ((2 : ℝ) ^ k * t) ^ (d + 1) =
      (1 / 2 : ℝ) ^ k / ((2 : ℝ) ^ k * t) ^ d := by
  rw [pow_succ, div_mul_eq_div_div]
  have h : (1 / 2 : ℝ) ^ k * ((2 : ℝ) ^ k * t) = t := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [div_right_comm]
  congr 1
  exact (div_eq_iff (ne_of_gt (by positivity : 0 < (2 : ℝ) ^ k * t))).2 h.symm

private theorem exists_dyadic_radius {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    ∃ k : ℕ, (2 : ℝ) ^ k * t ≤ t + r ∧ r ≤ 2 * ((2 : ℝ) ^ k * t) := by
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near
    ((le_div_iff₀ ht).2 (by linarith : 1 * t ≤ t + r)) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, (le_div_iff₀ ht).1 hk, ?_⟩
  have h := (div_lt_iff₀ ht).1 hk'
  rw [pow_succ] at h
  nlinarith

/-- Vanishing dimension-normalized ball integrals are uniformly bounded over all radii
when the nonnegative function is integrable. -/
theorem exists_bound_ball_integral_div_pow (hf : Integrable f μ) (hf0 : ∀ y, 0 ≤ f y)
    (hlim : Tendsto (fun r : ℝ ↦ (∫ y in closedBall x r, f y ∂μ) / r ^ d)
      (𝓝[>] 0) (𝓝 0)) :
    ∃ M > 0, ∀ r > 0, (∫ y in closedBall x r, f y ∂μ) / r ^ d ≤ M := by
  have he : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (∫ y in closedBall x r, f y ∂μ) / r ^ d < 1 :=
    hlim.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨δ, hδ, hlocal⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 he
  have hint0 : 0 ≤ ∫ y, f y ∂μ := integral_nonneg hf0
  have hδ0 : 0 < δ := hδ
  have hquot0 : 0 ≤ (∫ y, f y ∂μ) / δ ^ d := div_nonneg hint0 (by positivity)
  refine ⟨1 + (∫ y, f y ∂μ) / δ ^ d, by positivity, fun r hr ↦ ?_⟩
  by_cases hrδ : r < δ
  · have h := hlocal ⟨hr, hrδ⟩
    exact h.le.trans (by linarith)
  · have hpow : δ ^ d ≤ r ^ d := pow_le_pow_left₀ hδ.le (le_of_not_gt hrδ) d
    calc
      (∫ y in closedBall x r, f y ∂μ) / r ^ d ≤ (∫ y, f y ∂μ) / r ^ d := by
        exact div_le_div_of_nonneg_right
          (setIntegral_le_integral hf (Eventually.of_forall hf0)) (by positivity)
      _ ≤ (∫ y, f y ∂μ) / δ ^ d :=
        div_le_div_of_nonneg_left (integral_nonneg hf0) (by positivity) hpow
      _ ≤ 1 + (∫ y, f y ∂μ) / δ ^ d := by linarith

variable [BorelSpace X]

/-- A Poisson weight is controlled by a summable family of dyadic ball averages.
This estimate uses no doubling or regularity assumption on the measure. -/
theorem integral_poisson_weight_le_tsum (hf : Integrable f μ) (hf0 : ∀ y, 0 ≤ f y)
    {t : ℝ} (ht : 0 < t) :
    (∫ y, t / (t + dist y x) ^ (d + 1) * f y ∂μ) ≤
      ∑' k : ℕ, (1 / 2 : ℝ) ^ k / ((2 : ℝ) ^ k * t) ^ d *
        ∫ y in closedBall x (2 * ((2 : ℝ) ^ k * t)), f y ∂μ := by
  classical
  let R : ℕ → ℝ := fun k ↦ (2 : ℝ) ^ k * t
  let a : ℕ → ℝ := fun k ↦ (1 / 2 : ℝ) ^ k / R k ^ d
  let F : ℕ → X → ℝ := fun k y ↦ a k * (closedBall x (2 * R k)).indicator f y
  have hR (k : ℕ) : 0 < R k := by dsimp [R]; positivity
  have htR (k : ℕ) : t ≤ R k := by
    dsimp [R]
    exact le_mul_of_one_le_left ht.le (one_le_pow₀ (by norm_num))
  have ha (k : ℕ) : 0 ≤ a k := by dsimp [a]; positivity
  have ha_le (k : ℕ) : a k ≤ (1 / 2 : ℝ) ^ k / t ^ d := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ ht.le (htR k) d)
  have hF0 (k : ℕ) (y : X) : 0 ≤ F k y := by
    exact mul_nonneg (ha k) (indicator_nonneg (fun z _ ↦ hf0 z) y)
  have hF_le (k : ℕ) (y : X) : F k y ≤ (1 / 2 : ℝ) ^ k * (f y / t ^ d) := by
    calc
      F k y ≤ a k * f y := mul_le_mul_of_nonneg_left
        (indicator_le_self' (fun z _ ↦ hf0 z) y) (ha k)
      _ ≤ ((1 / 2 : ℝ) ^ k / t ^ d) * f y :=
        mul_le_mul_of_nonneg_right (ha_le k) (hf0 y)
      _ = _ := by ring
  have hgeom : Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hsum (y : X) : Summable (fun k ↦ F k y) := by
    apply (hgeom.mul_right (f y / t ^ d)).of_nonneg_of_le (fun k ↦ hF0 k y)
    exact fun k ↦ hF_le k y
  have hsum_le (y : X) : (∑' k, F k y) ≤ 2 * (f y / t ^ d) := by
    calc
      (∑' k, F k y) ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ k * (f y / t ^ d) :=
        (hsum y).tsum_le_tsum (fun k ↦ hF_le k y) (hgeom.mul_right _)
      _ = _ := by rw [tsum_mul_right, tsum_geometric_of_abs_lt_one (by norm_num)]; norm_num
  have hFint (k : ℕ) : Integrable (F k) μ :=
    (hf.indicator measurableSet_closedBall).const_mul (a k)
  have hsumint : Integrable (fun y ↦ ∑' k, F k y) μ := by
    refine ((hf.div_const (t ^ d)).const_mul 2).mono' ?_ ?_
    · exact (AEMeasurable.tsum (fun k ↦ (hFint k).aemeasurable)).aestronglyMeasurable
    · exact Eventually.of_forall fun y ↦ by
        rw [Real.norm_of_nonneg (tsum_nonneg (fun k ↦ hF0 k y))]
        exact hsum_le y
  have hnormsum : Summable (fun k ↦ ∫ y, ‖F k y‖ ∂μ) := by
    apply (hgeom.mul_right ((∫ y, f y ∂μ) / t ^ d)).of_nonneg_of_le
      (fun k ↦ integral_nonneg (fun y ↦ norm_nonneg _))
    intro k
    calc
      (∫ y, ‖F k y‖ ∂μ) ≤ ∫ y, (1 / 2 : ℝ) ^ k * (f y / t ^ d) ∂μ := by
        apply integral_mono (hFint k).norm (((hf.div_const _).const_mul _))
        intro y
        dsimp only
        rw [Real.norm_of_nonneg (hF0 k y)]
        exact hF_le k y
      _ = _ := by rw [integral_const_mul, integral_div]
  have hpoint (y : X) : t / (t + dist y x) ^ (d + 1) * f y ≤ ∑' k, F k y := by
    obtain ⟨k, hk, hk'⟩ := exists_dyadic_radius ht (dist_nonneg (x := y) (y := x))
    have hmem : y ∈ closedBall x (2 * R k) := hk'
    calc
      t / (t + dist y x) ^ (d + 1) * f y ≤ t / R k ^ (d + 1) * f y := by
        apply mul_le_mul_of_nonneg_right _ (hf0 y)
        exact div_le_div_of_nonneg_left ht.le (by positivity)
          (pow_le_pow_left₀ (hR k).le hk (d + 1))
      _ = F k y := by rw [dyadic_coefficient k d ht]; simp [F, a, R, hmem]
      _ ≤ ∑' j, F j y := (hsum y).le_tsum k (fun j _ ↦ hF0 j y)
  calc
    (∫ y, t / (t + dist y x) ^ (d + 1) * f y ∂μ) ≤ ∫ y, ∑' k, F k y ∂μ := by
      exact integral_mono_of_nonneg
        (Eventually.of_forall (fun y ↦ mul_nonneg (by positivity) (hf0 y)))
        hsumint (Eventually.of_forall hpoint)
    _ = ∑' k, ∫ y, F k y ∂μ :=
      (integral_tsum_of_summable_integral_norm hFint hnormsum).symm
    _ = _ := by
      congr 1
      ext k
      rw [show (fun y ↦ F k y) = fun y ↦ a k *
        (closedBall x (2 * R k)).indicator f y from rfl,
        integral_const_mul, integral_indicator measurableSet_closedBall]

private theorem dyadic_ball_integral {t : ℝ} (ht : 0 < t) (k d : ℕ) (b : ℝ) :
    (1 / 2 : ℝ) ^ k / ((2 : ℝ) ^ k * t) ^ d * b =
      (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ k * (b / (2 * ((2 : ℝ) ^ k * t)) ^ d) := by
  rw [mul_pow]
  have h : (2 : ℝ) ^ k * t ≠ 0 := ne_of_gt (by positivity)
  field_simp
  simp only [mul_pow]
  ring

/-- A nonnegative integrable error whose dimension-normalized ball integrals vanish
has vanishing integrals against Poisson weights. The dyadic majorant handles the entire tail. -/
theorem tendsto_integral_poisson_weight (hf : Integrable f μ) (hf0 : ∀ y, 0 ≤ f y)
    (hlim : Tendsto (fun r : ℝ ↦ (∫ y in closedBall x r, f y ∂μ) / r ^ d)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t : ℝ ↦ ∫ y, t / (t + dist y x) ^ (d + 1) * f y ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM, hbound⟩ := exists_bound_ball_integral_div_pow hf hf0 hlim
  let S : ℝ → ℕ → ℝ := fun t k ↦ (1 / 2 : ℝ) ^ k / ((2 : ℝ) ^ k * t) ^ d *
    ∫ y in closedBall x (2 * ((2 : ℝ) ^ k * t)), f y ∂μ
  have hgeom : Summable (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hS (k : ℕ) : Tendsto (fun t ↦ S t k) (𝓝[>] 0) (𝓝 0) := by
    have hscale : Tendsto (fun t : ℝ ↦ 2 * ((2 : ℝ) ^ k * t)) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [mul_zero] using (hid.const_mul ((2 : ℝ) ^ k)).const_mul 2
      · filter_upwards [self_mem_nhdsWithin] with t ht
        change 0 < 2 * ((2 : ℝ) ^ k * t)
        have ht0 : 0 < t := ht
        positivity
    have h := (hlim.comp hscale).const_mul ((2 : ℝ) ^ d * (1 / 2 : ℝ) ^ k)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (dyadic_ball_integral ht k d _).symm
  have hsumlim : Tendsto (fun t ↦ ∑' k, S t k) (𝓝[>] 0) (𝓝 0) := by
    have hsum := hgeom.mul_left ((2 : ℝ) ^ d * M)
    have h := tendsto_tsum_of_dominated_convergence hsum hS ?_
    · simpa only [tsum_zero] using h
    filter_upwards [self_mem_nhdsWithin] with t ht k
    have ht0 : 0 < t := ht
    have hint0 : 0 ≤ ∫ y in closedBall x (2 * ((2 : ℝ) ^ k * t)), f y ∂μ :=
      integral_nonneg hf0
    have hS0 : 0 ≤ S t k := by dsimp [S]; positivity
    rw [Real.norm_of_nonneg hS0]
    dsimp [S]
    rw [dyadic_ball_integral ht0]
    calc
      (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ k *
          ((∫ y in closedBall x (2 * ((2 : ℝ) ^ k * t)), f y ∂μ) /
            (2 * ((2 : ℝ) ^ k * t)) ^ d) ≤
          (2 : ℝ) ^ d * (1 / 2 : ℝ) ^ k * M :=
        mul_le_mul_of_nonneg_left (hbound _ (by positivity)) (by positivity)
      _ = ((2 : ℝ) ^ d * M) * (1 / 2 : ℝ) ^ k := by ring
  apply squeeze_zero' ?_ ?_ hsumlim
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    exact integral_nonneg (fun y ↦ mul_nonneg (by positivity) (hf0 y))
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact integral_poisson_weight_le_tsum hf hf0 ht

end PDE.Analysis
