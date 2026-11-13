/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Cauchy
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.QuadraticLowerBound

/-!
# Finite propagation of the constructed Fourier wave

The Schwartz Fourier wave propagates compact initial supports at unit
speed for nonnegative time. Consequently each finite forward time interval has
one compact spatial support. These support conclusions are derived from the
closed-cone energy theorem, including its vertex.
-/

@[expose] public section

open PDE.Common MeasureTheory Set Metric
open scoped SchwartzMap

namespace WaveEquation.Fourier

/-- The constructed Fourier wave vanishes outside the expanding support ball.
This follows from the cone energy theorem, including the cone vertex. -/
theorem realSolution_eq_zero_of_radius_lt {n : ℕ} [Fact (0 < n)] (g h : 𝓢(ℝ^n, ℝ)) (c : ℝ^n)
    {R t : ℝ} (ht : 0 ≤ t) (hg : ∀ y, R < dist y c → g y = 0) (hh : ∀ y, R < dist y c → h y = 0)
    {x : ℝ^n} (hx : R + t < dist x c) :
    realSolution g h (timeSpaceCons t x) = 0 := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [realSolution_initial_position]
    exact hg x (by simpa only [add_zero] using hx)
  have hbase (y : ℝ^n) (hy : y ∈ closedBall x (t - 0)) : R < dist y c := by
    have hdist : dist x y ≤ t := by simpa only [sub_zero, mem_closedBall, dist_comm] using hy
    have htri := dist_triangle x y c
    linarith
  have hz := eq_zero_on_closed_backwardCone_semilinear
    (V := fun _ ↦ 0) contDiff_const (fun _ ↦ le_rfl) rfl
    (contDiff_two_realSolution g h) x (a := 0) (T := t)
    (fun r _ y _ ↦ by
      simpa only [semilinearWaveOperator, deriv_const, add_zero] using
        waveOperator_realSolution g h (timeSpaceCons r y))
    (fun y hy ↦ (realSolution_initial_position g h y).trans (hg y (hbase y hy)))
    (fun y hy ↦ (partialDeriv_realSolution_initial_velocity g h y).trans (hh y (hbase y hy)))
  exact hz t ⟨ht.le, le_rfl⟩ x (by simp)

/-- Initial supports in a ball propagate at unit speed for nonnegative time. -/
theorem tsupport_realSolution_slice_subset {n : ℕ} [Fact (0 < n)] (g h : 𝓢(ℝ^n, ℝ)) (c : ℝ^n)
    {R t : ℝ} (ht : 0 ≤ t) (hg : tsupport (g : ℝ^n → ℝ) ⊆ closedBall c R)
    (hh : tsupport (h : ℝ^n → ℝ) ⊆ closedBall c R) :
    tsupport (fun x ↦ realSolution g h (timeSpaceCons t x)) ⊆ closedBall c (R + t) := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  by_contra hout
  have hgzero (y : ℝ^n) (hy : R < dist y c) : g y = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact (not_le.mpr hy) (hg hs)
  have hhzero (y : ℝ^n) (hy : R < dist y c) : h y = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact (not_le.mpr hy) (hh hs)
  exact hx (realSolution_eq_zero_of_radius_lt g h c ht hgzero hhzero (lt_of_not_ge hout))

/-- Compact initial traces give one compact spatial support on every
finite forward time interval. -/
theorem exists_uniform_compactSupport_realSolution {n : ℕ} [Fact (0 < n)] (g h : 𝓢(ℝ^n, ℝ))
    (hg : HasCompactSupport (g : ℝ^n → ℝ)) (hh : HasCompactSupport (h : ℝ^n → ℝ)) (T : ℝ) :
    ∃ K : Set (ℝ^n), IsCompact K ∧ ∀ t ∈ Icc 0 T,
      tsupport (fun x ↦ realSolution g h (timeSpaceCons t x)) ⊆ K := by
  obtain ⟨R, hR⟩ := (hg.union hh).isBounded.subset_closedBall (0 : ℝ^n)
  refine ⟨closedBall 0 (R + T), isCompact_closedBall _ _, ?_⟩
  intro t ht
  exact (tsupport_realSolution_slice_subset g h 0 ht.1
    (fun x hx ↦ hR (Or.inl hx)) (fun x hx ↦ hR (Or.inr hx))).trans
    (closedBall_subset_closedBall (by linarith [ht.2]))

end WaveEquation.Fourier
