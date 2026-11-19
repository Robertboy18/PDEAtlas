/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.Algebra.Group.ContinuousDiv
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Uniform convergence of real functions

Three facts about uniform limits of real-valued functions: multiplying by convergent scalars
keeps uniform convergence when the limit is bounded (`TendstoUniformly.mul_tendsto`), uniform
convergence carries the suprema of the absolute values along (`TendstoUniformly.tendsto_iSup_abs`),
and a continuous compactly supported function is the uniform limit of its dilations `f(μ ·)` as
`μ → 1` (`HasCompactSupport.tendstoUniformly_comp_mul`).
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace TendstoUniformly

/-- Multiplying a uniformly convergent family with bounded limit by convergent scalars
gives a uniformly convergent family. -/
theorem mul_tendsto {ι α : Type*} {l : Filter ι} {F : ι → α → ℝ} {f : α → ℝ}
    {κ : ι → ℝ} {k M : ℝ} (h : TendstoUniformly F f l) (hκ : Tendsto κ l (𝓝 k))
    (hf : ∀ x, |f x| ≤ M) :
    TendstoUniformly (fun i x ↦ κ i * F i x) (fun x ↦ k * f x) l := by
  rw [Metric.tendstoUniformly_iff] at h ⊢
  intro ε hε
  set M' : ℝ := max M 0 + 1 with hM'
  set K : ℝ := |k| + 1 with hK
  have hM'pos : 0 < M' := by positivity
  have hKpos : 0 < K := by positivity
  filter_upwards [h (ε / (2 * K)) (by positivity),
    Metric.tendsto_nhds.mp hκ (min 1 (ε / (2 * M'))) (by positivity)] with i hi hκi x
  have h1 : |k - κ i| < min 1 (ε / (2 * M')) := by
    rw [abs_sub_comm]
    simpa only [Real.dist_eq] using hκi
  have h2 : |f x - F i x| < ε / (2 * K) := by simpa only [Real.dist_eq] using hi x
  have h3 : |κ i| ≤ K := by
    have := abs_sub_abs_le_abs_sub (κ i) k
    rw [abs_sub_comm (κ i) k] at this
    linarith [h1.trans_le (min_le_left _ _)]
  have h4 : |f x| ≤ M' := (hf x).trans (by linarith [le_max_left M 0])
  have h5 : |k - κ i| * |f x| ≤ ε / 2 := by
    calc
      |k - κ i| * |f x| ≤ ε / (2 * M') * M' :=
        mul_le_mul (h1.le.trans (min_le_right _ _)) h4 (abs_nonneg _) (by positivity)
      _ = ε / 2 := by field_simp
  have h6 : |κ i| * |f x - F i x| < ε / 2 := by
    calc
      |κ i| * |f x - F i x| ≤ K * |f x - F i x| :=
        mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
      _ < K * (ε / (2 * K)) := mul_lt_mul_of_pos_left h2 hKpos
      _ = ε / 2 := by field_simp
  rw [Real.dist_eq]
  calc
    |k * f x - κ i * F i x| = |(k - κ i) * f x + κ i * (f x - F i x)| := by ring_nf
    _ ≤ |(k - κ i) * f x| + |κ i * (f x - F i x)| := abs_add_le _ _
    _ = |k - κ i| * |f x| + |κ i| * |f x - F i x| := by rw [abs_mul, abs_mul]
    _ < ε := by linarith

/-- Uniform convergence carries the supremum of the absolute values along, provided the
limit is bounded. -/
theorem tendsto_iSup_abs {ι α : Type*} [Nonempty α] {l : Filter ι}
    {F : ι → α → ℝ} {f : α → ℝ} (h : TendstoUniformly F f l)
    (hf : BddAbove (range fun x ↦ |f x|)) :
    Tendsto (fun i ↦ ⨆ x, |F i x|) l (𝓝 (⨆ x, |f x|)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp h (ε / 2) (half_pos hε)] with i hi
  have hclose (x : α) : |f x - F i x| < ε / 2 := by
    simpa only [Real.dist_eq] using hi x
  have hupper (x : α) : |F i x| ≤ (⨆ y, |f y|) + ε / 2 := by
    have h1 := le_ciSup hf x
    have h2 : |F i x| ≤ |f x| + |f x - F i x| := by
      have := abs_sub_abs_le_abs_sub (F i x) (f x)
      rw [abs_sub_comm] at this
      linarith
    linarith [hclose x]
  have hFbdd : BddAbove (range fun x ↦ |F i x|) := ⟨_, by rintro _ ⟨x, rfl⟩; exact hupper x⟩
  have hsup_le : (⨆ x, |F i x|) ≤ (⨆ y, |f y|) + ε / 2 := ciSup_le hupper
  have hle_sup : (⨆ y, |f y|) ≤ (⨆ x, |F i x|) + ε / 2 := by
    apply ciSup_le
    intro x
    have h1 := le_ciSup hFbdd x
    have h2 : |f x| ≤ |F i x| + |f x - F i x| := by
      have := abs_sub_abs_le_abs_sub (f x) (F i x)
      linarith
    linarith [hclose x]
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end TendstoUniformly

namespace HasCompactSupport

/-- A continuous compactly supported function is the uniform limit of its dilations
`f(μ ·)` as `μ → 1`. -/
theorem tendstoUniformly_comp_mul {f : ℝ → ℝ} (hc : HasCompactSupport f) (hf : Continuous f) :
    TendstoUniformly (fun μ x ↦ f (μ * x)) f (𝓝 1) := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp
    (hc.uniformContinuous_of_continuous hf) ε hε
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set K : ℝ := 2 * (|R| + 1) with hK
  have hKpos : 0 < K := by positivity
  have hzero {y : ℝ} (hy : |R| < |y|) : f y = 0 := by
    by_contra hne
    have hmem : y ∈ Metric.closedBall (0 : ℝ) R := hR (subset_tsupport f hne)
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
    linarith [le_abs_self R]
  have hnear : ∀ᶠ μ in 𝓝 (1 : ℝ), |μ - 1| < min (1 / 2) (δ / K) := by
    have h : Tendsto (fun μ : ℝ ↦ |μ - 1|) (𝓝 1) (𝓝 |1 - 1|) :=
      (continuous_sub_right (1 : ℝ)).abs.tendsto 1
    rw [sub_self, abs_zero] at h
    exact h.eventually (gt_mem_nhds (lt_min (by norm_num) (div_pos hδ hKpos)))
  filter_upwards [hnear] with μ hμ x
  have hμ1 : |μ - 1| < 1 / 2 := hμ.trans_le (min_le_left _ _)
  have hμδ : |μ - 1| < δ / K := hμ.trans_le (min_le_right _ _)
  rcases le_or_gt |x| K with hx | hx
  · apply hfδ
    rw [Real.dist_eq, show x - μ * x = (1 - μ) * x by ring, abs_mul, abs_sub_comm]
    calc
      |μ - 1| * |x| ≤ |μ - 1| * K := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
      _ < δ / K * K := mul_lt_mul_of_pos_right hμδ hKpos
      _ = δ := div_mul_cancel₀ _ hKpos.ne'
  · have hμpos : 1 / 2 < μ := by
      have := (abs_lt.mp hμ1).1
      linarith
    have hx1 : |R| < |x| := by linarith
    have hx2 : |R| < |μ * x| := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < μ)]
      nlinarith [abs_nonneg x, abs_nonneg R]
    rw [hzero hx1, hzero hx2, dist_self]
    exact hε

end HasCompactSupport
