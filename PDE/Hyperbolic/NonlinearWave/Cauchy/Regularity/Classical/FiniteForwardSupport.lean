/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiniteForwardUniqueness

/-!
# Compact support and amplitude on proper classical time strips

Finite propagation applies to a classical solution defined only on a finite
forward strip. Compact Cauchy data therefore give a common compact spatial
support, and hence a uniform amplitude bound, on each shorter closed strip.
-/

@[expose] public noncomputable section

open Filter PDE.Analysis PDE.Common Set
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open WaveEquation

variable {n : ℕ}

private theorem exists_forward_germ_extension {u : ℝ^(n + 1) → ℝ} {T s : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | p 0 ∈ Ioo 0 T})
    (hu₀ : ContDiffOn ℝ 1 u {p | p 0 ∈ Ico 0 T}) (hs : 0 ≤ s) (hsT : s < T) :
    ∃ U : ℝ^(n + 1) → ℝ, ContDiffOn ℝ 2 U {p | 0 < p 0} ∧ ContDiffOn ℝ 1 U {p | 0 ≤ p 0} ∧ ∀ t ∈
      Icc 0 s, ∀ x : ℝ^n, U =ᶠ[𝓝 (timeSpaceCons t x)] u := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨(s + T) / 2, ((s + T) / 2 + T) / 2, by linarith, by linarith⟩
  have hb : b.rOut < T := by dsimp [b]; linarith
  have hsb : s < b.rIn := by dsimp [b]; linarith
  refine ⟨fun p ↦ b (p 0) * u p, contDiffOn_timeCutoff b hb hu, contDiffOn_timeCutoff b hb hu₀, ?_⟩
  intro t ht x
  have htball : t ∈ Metric.ball (0 : ℝ) b.rIn := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] using ht.2.trans_lt hsb
  have he : b =ᶠ[𝓝 t] fun _ ↦ (1 : ℝ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds htball] with r hr
    exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hr)
  filter_upwards [he.comp_tendsto (EuclideanSpace.proj 0).continuous.continuousAt] with p hp
  change b (p 0) = 1 at hp
  rw [hp, one_mul]

/-- Compact Cauchy support propagates at speed one within a finite classical
lifespan. Only forward interior C² and initial-face C¹ regularity are assumed. -/
theorem eq_zero_of_cauchyData_finite_strip [Fact (0 < n)] {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {g h : ℝ^n → ℝ} {T R : ℝ} (hf : LocallyLipschitz f) (hf0 : f 0 = 0)
    (hu : ContDiffOn ℝ 2 u {p | p 0 ∈ Ioo 0 T}) (hu₀ : ContDiffOn ℝ 1 u {p | p 0 ∈ Ico 0 T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x)
    (hg : ∀ x, R < ‖x‖ → g x = 0) (hh : ∀ x, R < ‖x‖ → h x = 0) :
    ∀ t ∈ Ico 0 T, ∀ x : ℝ^n, R + t < ‖x‖ → u (timeSpaceCons t x) = 0 := by
  intro t ht x hx
  rcases ht.1.eq_or_lt with rfl | htpos
  · exact (hpos x).trans (hg x (by simpa only [add_zero] using hx))
  obtain ⟨U, hU, hU₀, he⟩ := exists_forward_germ_extension hu hu₀ ht.1 ht.2
  have hbase (y : ℝ^n) (hy : y ∈ Metric.ball x t) : R < ‖y‖ := by
    have hy' : ‖y - x‖ < t := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have hn := norm_le_norm_add_norm_sub y x
    linarith
  have htrace (y : ℝ^n) :
      derivWithin (fun s ↦ U (timeSpaceCons s y)) (Ici 0) 0 = h y := by
    rw [← hvel y]
    apply Filter.EventuallyEq.derivWithin_eq_of_nhds
    exact (he 0 ⟨le_rfl, ht.1⟩ y).comp_tendsto
      ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
        (continuous_id.prodMk continuous_const)).continuousAt
  have hz := eq_on_closed_cone_forward_locallyLipschitz (v := fun _ ↦ 0)
    hf hU contDiffOn_const hU₀ contDiffOn_const x htpos
    (fun s hs y _ ↦ ?_) (fun _ _ _ _ ↦ by simp [waveOperator, hf0])
    (fun y hy ↦ (he 0 ⟨le_rfl, ht.1⟩ y).eq_of_nhds.trans ((hpos y).trans (hg y (hbase y hy))))
    (fun y hy ↦ by simp [htrace, hh y (hbase y hy)])
    t ⟨ht.1, le_rfl⟩ x (by simp)
  · exact (he t ⟨ht.1, le_rfl⟩ x).eq_of_nhds.symm.trans hz
  · rw [waveOperator_congr_nhds (he s (Ioo_subset_Icc_self hs) y),
      (he s (Ioo_subset_Icc_self hs) y).eq_of_nhds]
    exact hwave s ⟨hs.1, hs.2.trans ht.2⟩ y

/-- A classical solution with compact Cauchy data is uniformly bounded on each
closed strip strictly below its lifespan, including the initial face. -/
theorem exists_amplitude_bound_on_proper_strip [Fact (0 < n)] {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {g h : ℝ^n → ℝ} {T S : ℝ} (hf : LocallyLipschitz f) (hf0 : f 0 = 0)
    (hu : ContDiffOn ℝ 2 u {p | p 0 ∈ Ioo 0 T}) (hu₀ : ContDiffOn ℝ 1 u {p | p 0 ∈ Ico 0 T})
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x)
    (hg : HasCompactSupport g) (hh : HasCompactSupport h) (hST : S < T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc 0 S, ∀ x : ℝ^n, ‖u (timeSpaceCons t x)‖ ≤ B := by
  obtain ⟨R, hR⟩ := (hg.union hh).isBounded.exists_norm_le
  have hsupp := eq_zero_of_cauchyData_finite_strip hf hf0 hu hu₀ hwave hpos hvel (R := R)
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport (fun hx' ↦ (not_le_of_gt hx) (hR x (Or.inl hx'))))
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport (fun hx' ↦ (not_le_of_gt hx) (hR x (Or.inr hx'))))
  have hc : ContinuousOn (fun p : ℝ × ℝ^n ↦ u (timeSpaceCons p.1 p.2))
      (Icc 0 S ×ˢ Metric.closedBall (0 : ℝ^n) (R + S)) :=
    hu₀.continuousOn.comp (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.continuousOn
      (fun _ hp ↦ ⟨hp.1.1, hp.1.2.trans_lt hST⟩)
  have hcompact := (isCompact_Icc (a := (0 : ℝ)) (b := S)).prod
    (isCompact_closedBall (0 : ℝ^n) (R + S))
  obtain ⟨A, hA⟩ := (hcompact.image_of_continuousOn hc).isBounded.exists_norm_le
  refine ⟨max A 0, le_max_right _ _, fun t ht x ↦ ?_⟩
  by_cases hx : x ∈ Metric.closedBall (0 : ℝ^n) (R + S)
  · exact (hA _ ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left _ _)
  · have hx' : R + S < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    rw [hsupp t ⟨ht.1, ht.2.trans_lt hST⟩ x
      (by linarith [ht.2] : R + t < ‖x‖), norm_zero]
    exact le_max_right _ _

end PDE.Hyperbolic.NonlinearWave.Cauchy
