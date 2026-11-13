/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralLifespan
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.SpatialSupport
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The integral lifespan alternative from compact Cauchy data

Arbitrary compact C³ displacement and C² velocity construct a local bounded
trajectory. Its Kirchhoff free field is bounded on every finite time slab, so
the integral lifespan alternative applies. Both branches retain the ordinary
initial traces and satisfy the spatially tested nonlinear wave equation.
The result leaves the finite-time amplitude alternative explicit and makes no
pointwise C² claim.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A finite C¹ integral trajectory for the Kirchhoff input solves the
spatially tested PDE throughout its positive interval. -/
theorem IsIntegralTrajectoryBefore.tested_equation {r b L : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u) {φ : ℝ^3 → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) {t : ℝ} (ht : t ∈ Ioo 0 L) :
    HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x)) ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
      ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t :=
  hasDerivAt_deriv_integral_of_signedPower_integral_eq hr hb hg hh hu.regular hu.equation hφ hφs ht

/-- A global C¹ integral trajectory for the Kirchhoff input solves the tested
PDE at every positive time. -/
theorem IsGlobalIntegralTrajectory.tested_equation {r b : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) {u : ℝ × ℝ^3 → ℝ}
    (hu : IsGlobalIntegralTrajectory r b (cauchyFreeField g h) u) {φ : ℝ^3 → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x)) ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
      ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t := by
  have hbefore := hu.before (T := t + 1) (by linarith)
  exact hasDerivAt_deriv_integral_of_signedPower_integral_eq hr hb hg hh
    hbefore.regular hbefore.equation hφ hφs ⟨ht, by linarith⟩

/-- Every real signed power with exponent at least one and arbitrary compact
C³/C² data admit either a global C¹ tested solution or a finite-lifetime C¹
tested solution with amplitude unbounded near its endpoint. Both are
constructed from the data and retain the ordinary position and velocity traces. -/
theorem exists_tested_lifespan_alternative_of_compact_data {r : ℝ}
    (hr : 1 ≤ r) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) :
    ∃ b : ℝ, 0 < b ∧
      ((∃ u : ℝ × ℝ^3 → ℝ, IsGlobalIntegralTrajectory r b (cauchyFreeField g h) u ∧
        (∀ x : ℝ^3, u (0, x) = g x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
        ∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t : ℝ, 0 < t →
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
            ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t) ∨
      ∃ L : ℝ, ∃ u : ℝ × ℝ^3 → ℝ,
        IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u ∧
        (∀ x : ℝ^3, u (0, x) = g x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
        (∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t ∈ Ioo 0 L,
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
            ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t) ∧
        ∀ A < L, ∀ M : ℝ, ∃ p : ℝ × ℝ^3,
          p.1 ∈ Ico 0 L ∧ A ≤ p.1 ∧ M < |u p|) := by
  obtain ⟨T, M, _, hT, hM, u₀, hu₀, hu₀g, hu₀h, hu₀B, _, hu₀e, _⟩ :=
    exists_supported_signedPower_weak_trajectory_of_compact_data hr hg hh hgs hhs
  have h₀ : IsBoundedIntegralTrajectoryBefore r T (cauchyFreeField g h) T u₀ :=
    ⟨hT, hu₀.mono (fun _ hp ↦ abs_lt.mpr hp), ⟨M, hM, hu₀B⟩, hu₀e⟩
  have htraces {w : ℝ × ℝ^3 → ℝ} (heq : EqOn w u₀ {p | -T < p.1 ∧ p.1 < T}) :
      (∀ x : ℝ^3, w (0, x) = g x) ∧
      ∀ x : ℝ^3, HasDerivAt (fun t ↦ w (t, x)) (h x) 0 := by
    refine ⟨?_, ?_⟩
    · intro x
      have hw0 : w (0, x) = u₀ (0, x) := heq ⟨by linarith, hT⟩
      exact hw0.trans (hu₀g x)
    · intro x
      apply (hu₀h x).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds (show -T < 0 by linarith) hT] with t ht using heq ht
  have hH := contDiff_one_cauchyFreeField
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num))
  have hHB (S : ℝ) (_hS : 0 < S) := exists_bound_cauchyFreeField_of_compact_data
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs S
  refine ⟨T, hT, ?_⟩
  rcases exists_integral_lifespan_alternative hr hT hH hHB h₀ with hglobal | hfinite
  · obtain ⟨u, hu, heq⟩ := hglobal
    obtain ⟨hug, huh⟩ := htraces heq
    exact Or.inl ⟨u, hu, hug, huh, fun _ hφ hφs _ ht ↦ hu.tested_equation hr hT hg hh hφ hφs ht⟩
  · obtain ⟨L, u, hu, heq, hblow⟩ := hfinite
    obtain ⟨hug, huh⟩ := htraces heq
    exact Or.inr ⟨L, u, hu, hug, huh,
      fun _ hφ hφs _ ht ↦ hu.tested_equation hr hT hg hh hφ hφs ht, hblow⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
