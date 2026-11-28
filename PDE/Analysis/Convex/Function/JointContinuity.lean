/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.Jensen

/-!
# Joint continuity of a family of convex functions

## Motivation

A function `G(s, ξ)` is continuous in `s` for each `ξ` and convex in `ξ` for each `s`. Is it
continuous in the pair?

## The idea

In finite dimensions, yes. A point `ξ₀` lies in the interior of a simplex. A convex function is
at most its largest value at the vertices on the simplex, and the finitely many vertex values
are continuous in `s`, so `G(s, ·)` is bounded above on a ball around `ξ₀`, uniformly for `s`
near `s₀`. Convexity through the centre turns the upper bound and the value at `ξ₀` into a lower
bound. A convex function with a two-sided bound on a ball is Lipschitz on the ball of half the
radius, with a constant that depends on the bound only. So
`|G(s, ξ) - G(s₀, ξ₀)| ≤ K ‖ξ - ξ₀‖ + |G(s, ξ₀) - G(s₀, ξ₀)|` near `(s₀, ξ₀)`.

## Main results

* `continuous_uncurry_of_convexOn` (all families on a finite-dimensional real normed space, all
  topological parameter spaces): separate continuity in the parameter and convexity in the
  variable give joint continuity.

## Relations

* The simplex is Mathlib's `exists_mem_interior_convexHull_affineBasis`, the bound on it is
  `ConvexOn.exists_ge_of_mem_convexHull`, and the Lipschitz constant is
  `ConvexOn.lipschitzOnWith_of_abs_le`. `ConvexOn.continuousOn` is the case of one function.
* `PDE.CalculusOfVariations.lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient`
  uses the theorem to pass from a density that is continuous in the value for each gradient to
  one that is continuous in both.

## What stays open

Infinite-dimensional spaces, where a convex function need not be continuous.
-/

@[expose] public section

namespace PDE.Analysis

open Filter Metric Set
open scoped Topology

variable {S H : Type*} [TopologicalSpace S] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ H]

/-- A family `G s ξ` on a finite-dimensional space that is continuous in the parameter `s` for
each `ξ` and convex in `ξ` for each `s` is jointly continuous. Near a point the family is bounded
on a ball, uniformly in the parameter, by its values at the vertices of a simplex, and a bounded
convex function is Lipschitz with a constant given by the bound. -/
theorem continuous_uncurry_of_convexOn {G : S → H → ℝ}
    (hs : ∀ ξ, Continuous fun s ↦ G s ξ) (hconv : ∀ s, ConvexOn ℝ univ (G s)) :
    Continuous (Function.uncurry G) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, ξ₀⟩
  -- a simplex around `ξ₀` and a ball inside it
  obtain ⟨b, hb, -⟩ :=
    exists_mem_interior_convexHull_affineBasis (univ_mem : (univ : Set H) ∈ 𝓝 ξ₀)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hb)
  have hball' : ball ξ₀ r ⊆ convexHull ℝ (range b) := hball.trans interior_subset
  -- the values at the vertices are below `C` for parameters near `s₀`
  set C := (Finset.univ.sup' Finset.univ_nonempty fun i ↦ G s₀ (b i)) + 1 with hC
  have hU₁ : ∀ᶠ s in 𝓝 s₀, ∀ i, G s (b i) < C := by
    refine Filter.eventually_all.2 fun i ↦ ?_
    have hlt : G s₀ (b i) < C := by
      have := Finset.le_sup' (fun i ↦ G s₀ (b i)) (Finset.mem_univ i)
      linarith
    exact (hs (b i)).continuousAt.eventually (gt_mem_nhds hlt)
  have hU₂ : ∀ᶠ s in 𝓝 s₀, G s₀ ξ₀ - 1 < G s ξ₀ :=
    (hs ξ₀).continuousAt.eventually (lt_mem_nhds (by linarith))
  set M := max |2 * (G s₀ ξ₀ - 1) - C| |C| with hM
  -- a two-sided bound on the ball, uniform in the parameter
  have hbound : ∀ᶠ s in 𝓝 s₀, ∀ ξ, dist ξ ξ₀ < r → |G s ξ| ≤ M := by
    filter_upwards [hU₁, hU₂] with s h1 h2 ξ hξ
    have hup (η : H) (hη : η ∈ ball ξ₀ r) : G s η ≤ C := by
      obtain ⟨y, ⟨i, rfl⟩, hy⟩ :=
        (hconv s).exists_ge_of_mem_convexHull (subset_univ _) (hball' hη)
      exact hy.trans (h1 i).le
    have hξ' : ξ ∈ ball ξ₀ r := hξ
    have hrefl : ξ₀ + (ξ₀ - ξ) ∈ ball ξ₀ r := by
      rw [mem_ball, dist_eq_norm] at hξ' ⊢
      simpa [norm_sub_rev] using hξ'
    have hmid : G s ξ₀ ≤ (1 / 2) * G s ξ + (1 / 2) * G s (ξ₀ + (ξ₀ - ξ)) := by
      have h := (hconv s).2 (mem_univ ξ) (mem_univ (ξ₀ + (ξ₀ - ξ)))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      have hpt : (1 / 2 : ℝ) • ξ + (1 / 2 : ℝ) • (ξ₀ + (ξ₀ - ξ)) = ξ₀ := by
        rw [← smul_add, show ξ + (ξ₀ + (ξ₀ - ξ)) = (2 : ℝ) • ξ₀ by rw [two_smul]; abel,
          smul_smul]
        norm_num
      rw [hpt] at h
      simpa using h
    have h3 := hup ξ hξ'
    have h4 := hup _ hrefl
    exact abs_le_max_abs_abs (by linarith) h3
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (le_max_right _ _)
  -- a Lipschitz bound on the smaller ball, uniform in the parameter
  have hlip : ∀ᶠ s in 𝓝 s₀, ∀ ξ ∈ ball ξ₀ (r / 2),
      |G s ξ - G s ξ₀| ≤ 2 * M / (r / 2) * dist ξ ξ₀ := by
    filter_upwards [hbound] with s hs' ξ hξ
    have hL := ((hconv s).subset (subset_univ _)
      (convex_ball ξ₀ r)).lipschitzOnWith_of_abs_le (half_pos hr) hs'
    have hξ' : ξ ∈ ball ξ₀ (r - r / 2) := by rwa [sub_half]
    have hc : ξ₀ ∈ ball ξ₀ (r - r / 2) := by
      rw [sub_half]
      exact mem_ball_self (half_pos hr)
    have h := hL.dist_le_mul ξ hξ' ξ₀ hc
    rwa [Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at h
  have hmain : ∀ᶠ p : S × H in 𝓝 (s₀, ξ₀), dist (G p.1 p.2) (G s₀ ξ₀) ≤
      2 * M / (r / 2) * dist p.2 ξ₀ + dist (G p.1 ξ₀) (G s₀ ξ₀) := by
    have h1 : ∀ᶠ p : S × H in 𝓝 (s₀, ξ₀), ∀ ξ ∈ ball ξ₀ (r / 2),
        |G p.1 ξ - G p.1 ξ₀| ≤ 2 * M / (r / 2) * dist ξ ξ₀ :=
      (continuous_fst.tendsto (s₀, ξ₀)).eventually hlip
    have h2 : ∀ᶠ p : S × H in 𝓝 (s₀, ξ₀), p.2 ∈ ball ξ₀ (r / 2) :=
      (continuous_snd.tendsto (s₀, ξ₀)).eventually (ball_mem_nhds ξ₀ (half_pos hr))
    filter_upwards [h1, h2] with p hp1 hp2
    have htri := dist_triangle (G p.1 p.2) (G p.1 ξ₀) (G s₀ ξ₀)
    have hp := hp1 p.2 hp2
    rw [← Real.dist_eq] at hp
    linarith
  have hlim : Tendsto (fun p : S × H ↦
      2 * M / (r / 2) * dist p.2 ξ₀ + dist (G p.1 ξ₀) (G s₀ ξ₀)) (𝓝 (s₀, ξ₀)) (𝓝 0) := by
    have hA : Continuous fun p : S × H ↦
        2 * M / (r / 2) * dist p.2 ξ₀ + dist (G p.1 ξ₀) (G s₀ ξ₀) :=
      ((continuous_snd.dist continuous_const).const_mul _).add
        (((hs ξ₀).comp continuous_fst).dist continuous_const)
    simpa using hA.tendsto (s₀, ξ₀)
  exact tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) hmain hlim)

end PDE.Analysis
