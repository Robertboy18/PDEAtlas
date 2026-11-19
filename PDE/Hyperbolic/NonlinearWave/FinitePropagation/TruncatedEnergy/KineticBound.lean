/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.TruncatedEnergy.FiniteBand
import PDE.FDeriv.SpaceTime

/-!
# Kinetic energy on a cone with initially zero physical energy

A constant shift chosen from the potential values on a finite cylinder
makes its cap and lateral energies nonnegative. No global sign of the potential
is required. The estimate retains the volume of the initial ball.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE PDE.Common PDE.Analysis

namespace WaveEquation

variable {n : ℕ}

/-- A local potential bound controls kinetic energy entering a finite cone
whose initial physical energy vanishes pointwise. -/
theorem ballIntegral_kinetic_le_of_potential_bound [Fact (0 < n)] {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V)
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (c : ℝ^n) {s τ T M : ℝ} (hsτ : s ≤ τ) (hτT : τ < T)
    (hwave : ∀ t ∈ Icc s τ, ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hzero : ∀ x ∈ Metric.ball c (T - s), semilinearWaveEnergyDensity V u (timeSpaceCons s x) = 0)
    (hbound : ∀ t ∈ Icc s τ, ∀ x ∈ Metric.closedBall c (T - s), |V (u (timeSpaceCons t x))| ≤ M) :
    ballIntegral n (fun x ↦ classicalWaveEnergyDensity u (timeSpaceCons τ x)) c (T - τ) ≤
      volume.real (Metric.ball c (T - s)) * M := by
  let W : ℝ → ℝ := fun z ↦ V z + M
  have hW : ContDiff ℝ 1 W := hV.add contDiff_const
  have hw (t : ℝ) (ht : t ∈ Icc s τ) (x : ℝ^n) (hx : x ∈ Metric.ball c (T - t)) :
      semilinearWaveOperator W u (timeSpaceCons t x) = 0 := by
    simpa only [semilinearWaveOperator, W, deriv_add_const] using hwave t ht x hx
  have hidentity := ballIntegral_energy_add_truncatedCone_flux_of_contDiffOn_finite_band
    hW (a := s - 1) (b := τ + 1) hu.contDiffOn c (by linarith) hsτ
      (by linarith) hτT hw
  have hpositive (t : ℝ) (ht : t ∈ Icc s τ) (x : ℝ^n)
      (hx : x ∈ Metric.closedBall c (T - s)) : 0 ≤ W (u (timeSpaceCons t x)) := by
    dsimp only [W]
    linarith [hbound t ht x hx, neg_abs_le (V (u (timeSpaceCons t x)))]
  have hflux : 0 ≤ (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation W u c p ∂Measure.euclideanHausdorffMeasure n) := by
    refine mul_nonneg (by positivity) (setIntegral_nonneg
      (isCompact_truncatedConeLateralSurface c T s τ).measurableSet fun p hp ↦ ?_)
    have hx : spatialPart p ∈ Metric.closedBall c (T - s) := by
      rw [Metric.mem_closedBall, dist_eq_norm, hp.2.2]
      linarith [hp.1]
    have hv := hpositive (p 0) ⟨hp.1, hp.2.1⟩ (spatialPart p) hx
    rw [timeSpaceCons_spatialPart] at hv
    unfold semilinearWaveConeDissipation semilinearWaveNullFlux
    exact add_nonneg (by positivity) hv
  have hinitial : ballIntegral n
      (fun x ↦ semilinearWaveEnergyDensity W u (timeSpaceCons s x)) c (T - s) =
        volume.real (Metric.ball c (T - s)) * M := by
    rw [ballIntegral, ← smul_eq_mul, ← setIntegral_const]
    refine setIntegral_congr_fun measurableSet_ball fun x hx ↦ ?_
    have hz := hzero x hx
    unfold semilinearWaveEnergyDensity at hz ⊢
    dsimp only [W]
    linarith
  have hk : Continuous (fun x : ℝ^n ↦ classicalWaveEnergyDensity u (timeSpaceCons τ x)) :=
    (contDiff_classicalWaveEnergyDensity (m := 1) hu).continuous.comp
      (contDiff_timeSpaceCons_spatial n τ (m := 1)).continuous
  have he : Continuous (fun x : ℝ^n ↦ semilinearWaveEnergyDensity W u (timeSpaceCons τ x)) :=
    (contDiff_semilinearWaveEnergyDensity hW hu).continuous.comp
      (contDiff_timeSpaceCons_spatial n τ (m := 1)).continuous
  have htop : ballIntegral n (fun x ↦ classicalWaveEnergyDensity u (timeSpaceCons τ x)) c (T - τ) ≤
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity W u (timeSpaceCons τ x))
        c (T - τ) := by
    refine setIntegral_mono_on
      ((hk.continuousOn.integrableOn_compact (isCompact_closedBall c (T - τ))).mono_set
        Metric.ball_subset_closedBall)
      ((he.continuousOn.integrableOn_compact (isCompact_closedBall c (T - τ))).mono_set
        Metric.ball_subset_closedBall) measurableSet_ball fun x hx ↦ ?_
    have hx' : x ∈ Metric.closedBall c (T - s) := by
      rw [Metric.mem_closedBall]
      exact (Metric.mem_ball.mp hx).le.trans (sub_le_sub_left hsτ T)
    exact le_add_of_nonneg_right (hpositive τ ⟨hsτ, le_rfl⟩ x hx')
  rw [hinitial] at hidentity
  linarith

/-- The local potential bound can be chosen at a point of the compact
cylinder. Thus it is controlled by any uniform potential tail, when available. -/
theorem exists_potential_value_ballIntegral_kinetic_le [Fact (0 < n)] {V : ℝ → ℝ}
    (hV : ContDiff ℝ 1 V) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (c : ℝ^n) {s τ T : ℝ}
    (hsτ : s ≤ τ) (hτT : τ < T)
    (hwave : ∀ t ∈ Icc s τ, ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hzero : ∀ x ∈ Metric.ball c (T - s), semilinearWaveEnergyDensity V u (timeSpaceCons s x) = 0) :
    ∃ r ∈ Icc s τ, ∃ y ∈ Metric.closedBall c (T - s), ballIntegral n
      (fun x ↦ classicalWaveEnergyDensity u (timeSpaceCons τ x)) c (T - τ) ≤
      volume.real (Metric.ball c (T - s)) * |V (u (timeSpaceCons r y))| := by
  let K := Icc s τ ×ˢ Metric.closedBall c (T - s)
  have hc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall c (T - s))
  have hn : K.Nonempty := ⟨(s, c), ⟨⟨le_rfl, hsτ⟩, by
    rw [Metric.mem_closedBall, dist_self]
    linarith⟩⟩
  have hf : Continuous (fun q : ℝ × ℝ^n ↦ |V (u (timeSpaceCons q.1 q.2))|) :=
    (hV.continuous.comp (hu.continuous.comp
      (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous)).abs
  obtain ⟨q, hq, hmax⟩ := hc.exists_isMaxOn hn
    (f := fun q : ℝ × ℝ^n ↦ |V (u (timeSpaceCons q.1 q.2))|) hf.continuousOn
  refine ⟨q.1, hq.1, q.2, hq.2, ?_⟩
  have hb (r : ℝ) (hr : r ∈ Icc s τ) (y : ℝ^n) (hy : y ∈ Metric.closedBall c (T - s)) :
      |V (u (timeSpaceCons r y))| ≤ |V (u (timeSpaceCons q.1 q.2))| :=
    hmax (show (r, y) ∈ K from ⟨hr, hy⟩)
  exact ballIntegral_kinetic_le_of_potential_bound hV hu c hsτ hτT hwave hzero hb

end WaveEquation
