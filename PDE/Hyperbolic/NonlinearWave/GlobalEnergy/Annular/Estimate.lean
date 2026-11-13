/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.LocalBounds.Ball
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Annular.Local

/-!
# Annular kinetic energy from potential values

Separate compact Cauchy slices provide the initial zero face of distant cones.
Their shifted energy estimates and integration over centers bound annular
kinetic energy by a potential value in a slightly enlarged annulus. The volume
factor remains explicit.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE PDE.Common PDE.Analysis

namespace WaveEquation

/-- Annular kinetic energy is controlled by a potential value on an
enlarged finite annular cylinder. All bounds follow from the source hypotheses. -/
theorem exists_radius_annular_kinetic_le_potential_value {n : ℕ} [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {s : ℝ}
    (hs0 : 0 ≤ s) :
    ∃ R₀ > 0, ∀ t, s ≤ t → ∀ R, R₀ + (t + 1 - s) + 1 < R →
      let L := t + 1 - s
      ∃ r ∈ Icc s t,
      ∃ y ∈ Metric.closedBall (0 : ℝ^n) (2 * R + 1 + L) \
          Metric.ball 0 (R - 1 - L),
      (∀ r' ∈ Icc s t,
        ∀ y' ∈ Metric.closedBall (0 : ℝ^n) (2 * R + 1 + L) \
            Metric.ball 0 (R - 1 - L),
          |V (u (timeSpaceCons r' y'))| ≤ |V (u (timeSpaceCons r y))|) ∧
      ∀ τ ∈ Icc s t,
        volume.real (Metric.ball (0 : ℝ^n) 1) *
          (∫ x in Metric.closedBall (0 : ℝ^n) (2 * R) \ Metric.ball 0 R,
            classicalWaveEnergyDensity u (timeSpaceCons τ x)) ≤
          volume.real (Metric.closedBall (0 : ℝ^n) (2 * R + 1) \
            Metric.ball 0 (R - 1)) * volume.real (Metric.ball (0 : ℝ^n) L) *
              |V (u (timeSpaceCons r y))| := by
  obtain ⟨R₀, hR₀, hlocal⟩ := exists_radius_ballIntegral_kinetic_le_potential_value
    hV hVzero hu hwave hs hs0
  refine ⟨R₀, hR₀, fun t hst R hR ↦ ?_⟩
  dsimp only
  let L := t + 1 - s
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hRpos : 0 < R := by linarith
  let A := Metric.closedBall (0 : ℝ^n) (2 * R) \ Metric.ball 0 R
  let B := Metric.closedBall (0 : ℝ^n) (2 * R + 1) \ Metric.ball 0 (R - 1)
  let D := Metric.closedBall (0 : ℝ^n) (2 * R + 1 + L) \ Metric.ball 0 (R - 1 - L)
  have hA : IsCompact A := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hB : IsCompact B := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  have hD : IsCompact D := (isCompact_closedBall _ _).diff Metric.isOpen_ball
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using (Fact.out : 0 < n))
  obtain ⟨z, hz⟩ := exists_norm_eq (ℝ^n) hRpos.le
  have hzD : z ∈ D := by
    simp only [D, mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, not_lt, hz]
    constructor <;> linarith
  have hprod : IsCompact (Icc s t ×ˢ D) := isCompact_Icc.prod hD
  have hcont : Continuous (fun q : ℝ × ℝ^n ↦ |V (u (timeSpaceCons q.1 q.2))|) :=
    (hV.continuous.comp (hu.continuous.comp
      (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous)).abs
  obtain ⟨q, hq, hmax⟩ := hprod.exists_isMaxOn ⟨(s, z), ⟨⟨le_rfl, hst⟩, hzD⟩⟩
    (f := fun q : ℝ × ℝ^n ↦ |V (u (timeSpaceCons q.1 q.2))|) hcont.continuousOn
  refine ⟨q.1, hq.1, q.2, hq.2, fun r hr y hy ↦ hmax (show (r, y) ∈ Icc s t ×ˢ D from ⟨hr, hy⟩),
    fun τ hτ ↦ ?_⟩
  let K : ℝ^n → ℝ := fun x ↦ classicalWaveEnergyDensity u (timeSpaceCons τ x)
  have hK : Continuous K := (contDiff_classicalWaveEnergyDensity (m := 1)
      (hu.of_le (by norm_num))).continuous.comp
        (contDiff_timeSpaceCons_spatial n τ (m := 1)).continuous
  have hnear (x : ℝ^n) (hx : x ∈ A) (c : ℝ^n) (hc : dist x c < 1) : c ∈ B := by
    simp only [A, mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, not_lt] at hx
    simp only [B, mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, not_lt]
    rw [dist_eq_norm] at hc
    have hxc := norm_le_norm_add_norm_sub x c
    have hcx := norm_le_norm_add_norm_sub c x
    rw [norm_sub_rev c x] at hcx
    constructor <;> linarith
  have hbound (c : ℝ^n) (hc : c ∈ B) : (∫ x in Metric.ball c 1, K x) ≤
        volume.real (Metric.ball (0 : ℝ^n) L) * |V (u (timeSpaceCons q.1 q.2))| := by
    have hc' := hc
    simp only [B, mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, not_lt] at hc'
    have hfar : R₀ + (τ + 1 - s) < ‖c‖ := by linarith [hτ.2]
    obtain ⟨r, hr, y, hy, hb⟩ := hlocal τ hτ.1 c hfar
    have hy' : ‖y - c‖ ≤ L := by
      have hy'' : ‖y - c‖ ≤ τ + 1 - s := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
      dsimp only [L]
      linarith [hτ.2]
    have hyD : y ∈ D := by
      simp only [D, mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right, not_lt]
      have hcy := norm_le_norm_add_norm_sub y c
      have hyc := norm_le_norm_add_norm_sub c y
      rw [norm_sub_rev c y] at hyc
      constructor <;> linarith
    have hv : |V (u (timeSpaceCons r y))| ≤ |V (u (timeSpaceCons q.1 q.2))| :=
      hmax (show (r, y) ∈ Icc s t ×ˢ D from ⟨⟨hr.1, hr.2.trans hτ.2⟩, hyD⟩)
    rw [Measure.addHaar_real_ball_center volume c] at hb
    have hvol : volume.real (Metric.ball (0 : ℝ^n) (τ + 1 - s)) ≤
        volume.real (Metric.ball (0 : ℝ^n) L) :=
      measureReal_mono (Metric.ball_subset_ball (by dsimp only [L]; linarith [hτ.2]))
    exact hb.trans (mul_le_mul hvol hv (abs_nonneg _) (by positivity))
  have havg := measure_ball_mul_integral_le_of_local_ball_bound (r := 1) hA hB hK
    (fun x ↦ classicalWaveEnergyDensity_nonneg u (timeSpaceCons τ x)) hnear hbound
  simpa only [K, mul_assoc] using havg

end WaveEquation
