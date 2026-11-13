/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ForwardUniqueness
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Uniqueness on a finite forward classical lifespan

A smooth temporal cutoff extends the field beyond a proper subinterval while
preserving its forward regularity and its initial right traces. The
cone theorem then compares arbitrary classical competitors on a finite
lifespan, without requiring a smooth extension to negative times.
-/

@[expose] public noncomputable section

open Filter PDE.Analysis PDE.Common Set
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open WaveEquation

variable {n : ℕ}

/-- Multiplication by a temporal cutoff extends regularity from a finite
forward strip to the corresponding full halfspace. -/
theorem contDiffOn_timeCutoff {k : ℕ∞} {u : ℝ^(n + 1) → ℝ} {T : ℝ} (b : ContDiffBump (0 : ℝ))
    (hb : b.rOut < T) {s : Set (ℝ^(n + 1))} (hu : ContDiffOn ℝ k u (s ∩ {p | p 0 < T})) :
    ContDiffOn ℝ k (fun p ↦ b (p 0) * u p) s := by
  intro p hp
  by_cases ht : p 0 < T
  · have hnb : s ∩ {q : ℝ^(n + 1) | q 0 < T} ∈ 𝓝[s] p := inter_mem self_mem_nhdsWithin
        (nhdsWithin_le_nhds ((isOpen_lt (EuclideanSpace.proj 0).continuous
          continuous_const).mem_nhds ht))
    exact ((b.contDiff.comp (EuclideanSpace.proj 0).contDiff).contDiffWithinAt).mul
      ((hu p ⟨hp, ht⟩).mono_of_mem_nhdsWithin hnb)
  · have hz : b =ᶠ[𝓝 (p 0)] fun _ ↦ (0 : ℝ) := by
      apply notMem_tsupport_iff_eventuallyEq.mp
      rw [b.tsupport_eq]
      intro h
      have hle : |p 0| ≤ b.rOut := by simpa only [Metric.mem_closedBall,
        Real.dist_eq, sub_zero] using h
      exact ht ((le_abs_self (p 0)).trans hle |>.trans_lt hb)
    have he : (fun q : ℝ^(n + 1) ↦ b (q 0) * u q) =ᶠ[𝓝 p] fun _ ↦ (0 : ℝ) := by
      filter_upwards [hz.comp_tendsto (EuclideanSpace.proj 0).continuous.continuousAt] with q hq
      change b (q 0) = 0 at hq
      rw [hq, zero_mul]
    exact (contDiffWithinAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      (he.filter_mono nhdsWithin_le_nhds) he.eq_of_nhds

/-- Equality of right Cauchy data determines a classical solution throughout a
finite forward strip. Only interior C² and boundary C¹ regularity are assumed. -/
theorem eq_on_finite_forward_strip [Fact (0 < n)] {f : ℝ → ℝ} {u v : ℝ^(n + 1) → ℝ} {T : ℝ}
    (hf : LocallyLipschitz f) (hu : ContDiffOn ℝ 2 u {p | p 0 ∈ Ioo 0 T})
    (hv : ContDiffOn ℝ 2 v {p | p 0 ∈ Ioo 0 T}) (hu₀ : ContDiffOn ℝ 1 u {p | p 0 ∈ Ico 0 T})
    (hv₀ : ContDiffOn ℝ 1 v {p | p 0 ∈ Ico 0 T})
    (huwave : ∀ t ∈ Ioo 0 T, ∀ x,
      waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    (hvwave : ∀ t ∈ Ioo 0 T, ∀ x,
      waveOperator v (timeSpaceCons t x) + f (v (timeSpaceCons t x)) = 0)
    (hpos : ∀ x, u (timeSpaceCons 0 x) = v (timeSpaceCons 0 x))
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 =
      derivWithin (fun t ↦ v (timeSpaceCons t x)) (Ici 0) 0) :
    ∀ t ∈ Ico 0 T, ∀ x, u (timeSpaceCons t x) = v (timeSpaceCons t x) := by
  intro t ht x
  rcases ht.1.eq_or_lt with rfl | htpos
  · exact hpos x
  let b : ContDiffBump (0 : ℝ) :=
    ⟨(t + T) / 2, ((t + T) / 2 + T) / 2, by linarith [ht.2], by linarith [ht.2]⟩
  have hb : b.rOut < T := by dsimp [b]; linarith [ht.2]
  have htb : t < b.rIn := by dsimp [b]; linarith [ht.2]
  let U : ℝ^(n + 1) → ℝ := fun p ↦ b (p 0) * u p
  let V : ℝ^(n + 1) → ℝ := fun p ↦ b (p 0) * v p
  have hU : ContDiffOn ℝ 2 U {p | 0 < p 0} := contDiffOn_timeCutoff b hb hu
  have hV : ContDiffOn ℝ 2 V {p | 0 < p 0} := contDiffOn_timeCutoff b hb hv
  have hU₀ : ContDiffOn ℝ 1 U {p | 0 ≤ p 0} := contDiffOn_timeCutoff b hb hu₀
  have hV₀ : ContDiffOn ℝ 1 V {p | 0 ≤ p 0} := contDiffOn_timeCutoff b hb hv₀
  have hlocal (w : ℝ^(n + 1) → ℝ) (s : ℝ) (hs : s ∈ Icc 0 t) (y : ℝ^n) :
      (fun p : ℝ^(n + 1) ↦ b (p 0) * w p) =ᶠ[𝓝 (timeSpaceCons s y)] w := by
    have hsball : s ∈ Metric.ball (0 : ℝ) b.rIn := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1] using
        hs.2.trans_lt htb
    have he : b =ᶠ[𝓝 s] fun _ ↦ (1 : ℝ) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hsball] with r hr
      exact b.one_of_mem_closedBall (Metric.ball_subset_closedBall hr)
    filter_upwards [he.comp_tendsto (EuclideanSpace.proj 0).continuous.continuousAt] with p hp
    change b (p 0) = 1 at hp
    rw [hp, one_mul]
  have hslice (w : ℝ^(n + 1) → ℝ) (s : ℝ) (hs : s ∈ Icc 0 t) (y : ℝ^n) :=
    (hlocal w s hs y).eq_of_nhds
  have htrace (w : ℝ^(n + 1) → ℝ) (y : ℝ^n) :
      derivWithin (fun s ↦ b s * w (timeSpaceCons s y)) (Ici 0) 0 =
        derivWithin (fun s ↦ w (timeSpaceCons s y)) (Ici 0) 0 := by
    apply Filter.EventuallyEq.derivWithin_eq_of_nhds
    exact (hlocal w 0 ⟨le_rfl, ht.1⟩ y).comp_tendsto
      ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
        (continuous_id.prodMk continuous_const)).continuousAt
  have he := eq_on_closed_cone_forward_locallyLipschitz hf hU hV hU₀ hV₀ x htpos
    (fun s hs y _ ↦ ?_) (fun s hs y _ ↦ ?_)
    (fun y _ ↦ ?_) (fun y _ ↦ ?_) t ⟨ht.1, le_rfl⟩ x (by simp)
  · dsimp only [U, V] at he
    rwa [hslice u t ⟨ht.1, le_rfl⟩ x, hslice v t ⟨ht.1, le_rfl⟩ x] at he
  · dsimp only [U]
    rw [waveOperator_congr_nhds (hlocal u s (Ioo_subset_Icc_self hs) y),
      hslice u s (Ioo_subset_Icc_self hs) y]
    exact huwave s ⟨hs.1, hs.2.trans ht.2⟩ y
  · dsimp only [V]
    rw [waveOperator_congr_nhds (hlocal v s (Ioo_subset_Icc_self hs) y),
      hslice v s (Ioo_subset_Icc_self hs) y]
    exact hvwave s ⟨hs.1, hs.2.trans ht.2⟩ y
  · dsimp only [U, V]
    rw [hslice u 0 ⟨le_rfl, ht.1⟩ y, hslice v 0 ⟨le_rfl, ht.1⟩ y]
    exact hpos y
  · change derivWithin (fun s ↦ b s * u (timeSpaceCons s y)) (Ici 0) 0 =
      derivWithin (fun s ↦ b s * v (timeSpaceCons s y)) (Ici 0) 0
    rw [htrace, htrace, hvel]

end PDE.Hyperbolic.NonlinearWave.Cauchy
