/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.Bounded.Smooth
import PDE.Analysis.Calculus.LocalExtension.SmoothCutoff
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth dependence along a finite trajectory

A compact trajectory fits inside a ball. A smooth cutoff gives a bounded field
that agrees with the original field on that ball, and its global flow is smooth.
Uniqueness identifies the critical trajectory; compactness then gives one open
set of nearby initial states whose trajectories stay in the ball for the entire
specified time interval.
-/

@[expose] public noncomputable section

open Metric Set
open scoped ContDiff NNReal Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth field has a smooth family around any trajectory on a compact time
interval. The returned global flow uses a cutoff outside that trajectory's
neighborhood; it solves the original equation for nearby initial states on the
entire specified interval. -/
theorem exists_contDiff_infty_flow_near_solution_Icc
    (v : E → E) (hv : ContDiff ℝ ∞ v)
    {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (γ : ℝ → E) (hγ : ContinuousOn γ (Icc a b))
    (hγode : ∀ t ∈ Ioo a b, HasDerivAt γ (v (γ t)) t)
    (q₀ : E) (hγ₀ : γ 0 = q₀) :
    ∃ (Φ : Flow ℝ E) (U : Set E),
      IsOpen U ∧ q₀ ∈ U ∧
      ContDiff ℝ ∞ (fun p : ℝ × E ↦ Φ p.1 p.2) ∧
      EqOn (fun t ↦ Φ t q₀) γ (Icc a b) ∧
      ∀ q ∈ U, ∀ t ∈ Icc a b,
        HasDerivAt (fun s ↦ Φ s q) (v (Φ t q)) t := by
  obtain ⟨R, hR, hball⟩ :=
    (isCompact_Icc.image_of_continuousOn hγ).isBounded.subset_ball_lt 0 (0 : E)
  have hγball (t : ℝ) (ht : t ∈ Icc a b) : γ t ∈ ball (0 : E) R :=
    hball ⟨t, ht, rfl⟩
  obtain ⟨w, K, hw, hwcompact, hwLip, hwv⟩ :=
    hv.exists_lipschitzWith_compactSupport_eqOn_closedBall (by simp) 0 hR
  obtain ⟨B, hB⟩ := hwcompact.exists_bound_of_continuous hw.continuous
  let M : ℝ≥0 := ⟨B, (norm_nonneg (w 0)).trans (hB 0)⟩
  obtain ⟨Φ, hΦ, hΦode⟩ :=
    PDE.Analysis.Evolution.exists_contDiff_infty_flow_hasDerivAt_of_bounded hw
      (M := M) hB
  have heq : EqOn (fun t ↦ Φ t q₀) γ (Icc a b) := by
    apply PDE.Analysis.Evolution.eqOn_Icc_of_hasDerivAt_of_lipschitzOn_balls
      (fun _ _ ↦ ⟨K, hwLip.lipschitzOnWith⟩) (show (0 : ℝ) ∈ Ioo a b from ⟨ha, hb⟩)
      (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun t _ ↦ hΦode q₀ t) hγ ?_
      ((Φ.map_zero_apply q₀).trans hγ₀.symm)
    intro t ht
    rw [hwv (ball_subset_closedBall (hγball t (Ioo_subset_Icc_self ht)))]
    exact hγode t ht
  let S : Set (ℝ × E) := {p | Φ p.1 p.2 ∈ ball (0 : E) R}
  have hS : IsOpen S := isOpen_ball.preimage hΦ.continuous
  have hsub : Icc a b ×ˢ {q₀} ⊆ S := by
    rintro ⟨t, q⟩ ⟨ht, hq⟩
    have hqeq : q = q₀ := mem_singleton_iff.mp hq
    subst q
    change Φ t q₀ ∈ ball (0 : E) R
    have heqt : Φ t q₀ = γ t := heq (show t ∈ Icc a b from ht)
    rw [heqt]
    exact hγball t ht
  obtain ⟨J, U, _hJ, hU, htime, hstate, htube⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hS hsub
  refine ⟨Φ, U, hU, hstate (mem_singleton q₀), hΦ, heq, ?_⟩
  intro q hq t ht
  have hvalue : Φ t q ∈ ball (0 : E) R := by
    change (t, q) ∈ S
    exact htube ⟨htime ht, hq⟩
  simpa only [hwv (ball_subset_closedBall hvalue)] using hΦode q t

end PDE.Analysis.ODE
