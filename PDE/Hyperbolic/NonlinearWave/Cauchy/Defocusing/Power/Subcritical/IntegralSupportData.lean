/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralLifespanData
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralSupport
import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.FreeWave

/-!
# Compact support of the constructed integral lifespan solution

The Kirchhoff field of compact Cauchy data has speed-one propagation. Finite
interval integral uniqueness transfers that support to the maximal
trajectory, including every continuation. Each proper closed strip therefore
has a common compact spatial support. The ordinary amplitude-limit question
and pointwise C² regularity are separate from this support theorem.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The closed supports of all displacement slices on a proper closed strip
lie in one closed ball. The same radius works up to any finite open endpoint. -/
theorem IsIntegralTrajectoryBefore.tsupport_subset_closedBall {r b L R S : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {H u : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H)
    (hHs : ∀ p : ℝ × ℝ^3, 0 ≤ p.1 → R + p.1 < ‖p.2‖ → H p = 0)
    (hu : IsIntegralTrajectoryBefore r b H L u) (hSL : S < L) {t : ℝ} (ht : t ∈ Icc 0 S) :
    tsupport (fun x : ℝ^3 ↦ u (t, x)) ⊆ Metric.closedBall 0 (R + S) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra! hnot
  have hxR : R + S < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hnot
  apply hx
  exact hu.eq_zero_of_supported_free hr hb hH hHs ⟨ht.1, ht.2.trans_lt hSL⟩
    ((add_le_add (le_refl R) ht.2).trans_lt hxR)

/-- A global trajectory has a common compact support on every finite closed
forward strip; its radius grows at speed one. -/
theorem IsGlobalIntegralTrajectory.tsupport_subset_closedBall {r b R S : ℝ} (hr : 1 ≤ r)
    (hb : 0 < b) {H u : ℝ × ℝ^3 → ℝ} (hH : ContDiff ℝ 1 H)
    (hHs : ∀ p : ℝ × ℝ^3, 0 ≤ p.1 → R + p.1 < ‖p.2‖ → H p = 0)
    (hu : IsGlobalIntegralTrajectory r b H u) {t : ℝ} (ht : t ∈ Icc 0 S) :
    tsupport (fun x : ℝ^3 ↦ u (t, x)) ⊆ Metric.closedBall 0 (R + S) := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  by_contra! hnot
  have hxR : R + S < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hnot
  apply hx
  exact hu.eq_zero_of_supported_free hr hb hH hHs ht.1 ((add_le_add (le_refl R) ht.2).trans_lt hxR)

private theorem exists_positive_radius_cauchyFreeField {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 1 g)
    (hh : Continuous h) (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) :
    ∃ R : ℝ, 0 < R ∧ ∀ p : ℝ × ℝ^3, 0 ≤ p.1 → R + p.1 < ‖p.2‖ → cauchyFreeField g h p = 0 := by
  obtain ⟨Rg, hRg, hgR⟩ := hgs.exists_pos_le_norm
  obtain ⟨Rh, _, hhR⟩ := hhs.exists_pos_le_norm
  refine ⟨max Rg Rh, hRg.trans_le (le_max_left _ _), ?_⟩
  intro p hp hx
  exact WaveEquation.SmallData.kirchhoffFormula_hasForwardSupport hg hh
    (fun y hy ↦ hgR y ((le_max_left _ _).trans hy.le))
    (fun y hy ↦ hhR y ((le_max_right _ _).trans hy.le)) p.1 hp p.2 hx

/-- Arbitrary compact C³/C² data construct a C¹ signed-power solution with
speed-one propagation throughout its lifespan. Both ordinary Cauchy
traces and the tested PDE hold for the same field. At a finite endpoint only
terminal-strip unboundedness is asserted, not an ordinary amplitude limit. -/
theorem exists_supported_tested_lifespan_of_compact_data {r : ℝ}
    (hr : 1 ≤ r) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) :
    ∃ b R : ℝ, 0 < b ∧ 0 < R ∧
      ((∃ u : ℝ × ℝ^3 → ℝ, IsGlobalIntegralTrajectory r b (cauchyFreeField g h) u ∧
        (∀ x : ℝ^3, u (0, x) = g x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
        (∀ p : ℝ × ℝ^3, 0 ≤ p.1 → R + p.1 < ‖p.2‖ → u p = 0) ∧
        ∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t : ℝ, 0 < t →
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
            ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t) ∨
      ∃ L : ℝ, ∃ u : ℝ × ℝ^3 → ℝ,
        IsIntegralTrajectoryBefore r b (cauchyFreeField g h) L u ∧
        (∀ x : ℝ^3, u (0, x) = g x) ∧
        (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
        (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → R + p.1 < ‖p.2‖ → u p = 0) ∧
        (∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t ∈ Ioo 0 L,
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
            ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t) ∧
        ∀ A < L, ∀ M : ℝ, ∃ p : ℝ × ℝ^3,
          p.1 ∈ Ico 0 L ∧ A ≤ p.1 ∧ M < |u p|) := by
  obtain ⟨R, hR, hHs⟩ := exists_positive_radius_cauchyFreeField
    (hg.of_le (by norm_num)) hh.continuous hgs hhs
  have hH := contDiff_one_cauchyFreeField
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num))
  obtain ⟨b, hb, hglobal | hfinite⟩ :=
    exists_tested_lifespan_alternative_of_compact_data hr hg hh hgs hhs
  · obtain ⟨u, hu, hpos, hvel, htest⟩ := hglobal
    exact ⟨b, R, hb, hR, Or.inl ⟨u, hu, hpos, hvel,
      fun _ hp hx ↦ hu.eq_zero_of_supported_free hr hb hH hHs hp hx, htest⟩⟩
  · obtain ⟨L, u, hu, hpos, hvel, htest, hblow⟩ := hfinite
    exact ⟨b, R, hb, hR, Or.inr ⟨L, u, hu, hpos, hvel,
      fun _ hp hx ↦ hu.eq_zero_of_supported_free hr hb hH hHs hp hx, htest, hblow⟩⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
