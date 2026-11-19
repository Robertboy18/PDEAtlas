/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.MetricSpace.UniformConvergence
import CAS.ExactTactic

/-!
# Uniform weak/strong pairing with moving tests

Uniform fixed-test weak convergence and a common state bound extend uniformly
over compact test sets by a finite net argument. A continuous limiting coefficient
on compact time supplies such a set, so strong uniform coefficient convergence
can be paired with weak uniform state convergence along the same filter.

The continuous-linear-map version keeps the weak Hilbert pivot distinct from
the observed space, using Mathlib's adjoint. No compact state envelope, strong
state convergence, or new subsequence is assumed.
-/

@[expose] public noncomputable section


open Filter
open scoped Topology

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Uniform convergence against each fixed Hilbert test extends uniformly over
any compact set of tests when the states have a common norm bound. -/
theorem tendstoUniformlyOn_inner_of_fixed_tests
    {ι X : Type*} {l : Filter ι} (u : ι → X → E) (uLimit : X → E)
    (M : ℝ) (hbound : ∀ n t, ‖u n t‖ ≤ M) (hlimit : ∀ t, ‖uLimit t‖ ≤ M)
    (hpair : ∀ v : E, TendstoUniformly (fun n t ↦ inner ℝ v (u n t))
      (fun t ↦ inner ℝ v (uLimit t)) l)
    {K : Set E} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n (p : X × E) ↦ inner ℝ p.2 (u n p.1))
      (fun p ↦ inner ℝ p.2 (uLimit p.1)) l (Set.univ ×ˢ K) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ := ε / (4 * |M| + 1)
  have hden : 0 < 4 * |M| + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : (4 * |M| + 1) * δ = ε := by
    dsimp [δ]
    exact mul_div_cancel₀ ε (ne_of_gt hden)
  obtain ⟨s, _, hs, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded hK.totallyBounded δ hδ
  have hcenters : ∀ᶠ n in l, ∀ v ∈ s, ∀ t,
      dist (inner ℝ v (uLimit t)) (inner ℝ v (u n t)) < ε / 2 := by
    apply hs.eventually_all.mpr
    intro v _
    exact Metric.tendstoUniformly_iff.mp (hpair v) (ε / 2) (half_pos hε)
  filter_upwards [hcenters] with n hn p hp
  obtain ⟨v, hv, hpv⟩ := Set.mem_iUnion₂.mp (hcover hp.2)
  have hdist : ‖p.2 - v‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hpv
  have hdiff : ‖uLimit p.1 - u n p.1‖ ≤ 2 * |M| := by
    exact (norm_sub_le _ _).trans (by
      linarith [hbound n p.1, hlimit p.1, le_abs_self M])
  have heq : inner ℝ p.2 (uLimit p.1) - inner ℝ p.2 (u n p.1) =
      inner ℝ (p.2 - v) (uLimit p.1 - u n p.1) +
        (inner ℝ v (uLimit p.1) - inner ℝ v (u n p.1)) := by
    simp only [inner_sub_left, inner_sub_right]
    cas
  rw [dist_eq_norm, heq]
  have hsmall : ‖inner ℝ (p.2 - v) (uLimit p.1 - u n p.1)‖ ≤ δ * (2 * |M|) :=
    (norm_inner_le_norm _ _).trans (mul_le_mul hdist.le hdiff (norm_nonneg _) (le_of_lt hδ))
  have hcenter := hn v hv p.1
  rw [dist_eq_norm] at hcenter
  exact (norm_add_le _ _).trans_lt (by nlinarith)

/-- A bounded family converging uniformly against fixed Hilbert tests can be
paired with a strongly converging moving coefficient on compact time. The compact
test range is derived from continuity of the limiting coefficient. -/
theorem tendstoUniformly_inner_of_weak_strong
    {ι X : Type*} [TopologicalSpace X] [CompactSpace X] {l : Filter ι}
    (u : ι → X → E) (uLimit : X → E) (v : ι → X → E) (vLimit : X → E)
    (M : ℝ) (hbound : ∀ n t, ‖u n t‖ ≤ M) (hlimit : ∀ t, ‖uLimit t‖ ≤ M)
    (hpair : ∀ w : E, TendstoUniformly (fun n t ↦ inner ℝ w (u n t))
      (fun t ↦ inner ℝ w (uLimit t)) l)
    (hv : TendstoUniformly v vLimit l) (hc : Continuous vLimit) :
    TendstoUniformly (fun n t ↦ inner ℝ (v n t) (u n t))
      (fun t ↦ inner ℝ (vLimit t) (uLimit t)) l := by
  have hweak := tendstoUniformlyOn_inner_of_fixed_tests u uLimit M hbound hlimit hpair
    (isCompact_range hc)
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hd : 0 < 2 * (|M| + 1) := by positivity
  filter_upwards [Metric.tendstoUniformly_iff.mp hv (ε / (2 * (|M| + 1)))
      (div_pos hε hd),
    Metric.tendstoUniformlyOn_iff.mp hweak (ε / 2) (half_pos hε)] with n hn hw t
  have ha := hn t
  rw [dist_eq_norm] at ha
  have hb := hw (t, vLimit t) ⟨Set.mem_univ _, Set.mem_range_self _⟩
  rw [dist_eq_norm] at hb
  have heq : inner ℝ (vLimit t) (uLimit t) - inner ℝ (v n t) (u n t) =
      (inner ℝ (vLimit t) (uLimit t) - inner ℝ (vLimit t) (u n t)) +
        inner ℝ (vLimit t - v n t) (u n t) := by
    rw [inner_sub_left]
    cas
  have hmul : ‖inner ℝ (vLimit t - v n t) (u n t)‖ ≤
      ε / (2 * (|M| + 1)) * |M| :=
    (norm_inner_le_norm _ _).trans (mul_le_mul ha.le
      ((hbound n t).trans (le_abs_self M)) (norm_nonneg _)
      (le_of_lt (div_pos hε hd)))
  have hcancel : ε / (2 * (|M| + 1)) * (2 * (|M| + 1)) = ε :=
    div_mul_cancel₀ ε (ne_of_gt hd)
  rw [dist_eq_norm, heq]
  exact (norm_add_le _ _).trans_lt (by nlinarith [div_pos hε hd])

/-- Apply a continuous linear observation before weak/strong pairing. Its
Hilbert adjoint transfers the moving coefficient to the original weak pivot,
without identifying the observation's inner product with the pivot's. -/
theorem tendstoUniformly_inner_map_of_weak_strong
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    {ι X : Type*} [TopologicalSpace X] [CompactSpace X] {l : Filter ι}
    (J : E →L[ℝ] F)
    (u : ι → X → E) (uLimit : X → E) (v : ι → X → F) (vLimit : X → F)
    (M : ℝ) (hbound : ∀ n t, ‖u n t‖ ≤ M) (hlimit : ∀ t, ‖uLimit t‖ ≤ M)
    (hpair : ∀ w : E, TendstoUniformly (fun n t ↦ inner ℝ w (u n t))
      (fun t ↦ inner ℝ w (uLimit t)) l)
    (hv : TendstoUniformly v vLimit l) (hc : Continuous vLimit) :
    TendstoUniformly (fun n t ↦ inner ℝ (v n t) (J (u n t)))
      (fun t ↦ inner ℝ (vLimit t) (J (uLimit t))) l := by
  have ht := tendstoUniformly_inner_of_weak_strong u uLimit
    (fun n t ↦ J.adjoint (v n t)) (fun t ↦ J.adjoint (vLimit t))
    M hbound hlimit hpair (J.adjoint.uniformContinuous.comp_tendstoUniformly hv)
      (J.adjoint.continuous.comp hc)
  simpa only [J.adjoint_inner_left] using ht


end PDE.Analysis.Evolution
