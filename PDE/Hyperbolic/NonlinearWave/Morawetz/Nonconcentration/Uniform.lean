/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.InitialData
public import PDE.Hyperbolic.NonlinearWave.Morawetz.Nonconcentration.Forward

/-!
# A uniform quintic cone-flux estimate from compact initial data

The global initial energy controls every initial cone ball by nonnegativity. Consequently one
explicit coefficient works for all centers, terminal times, and intermediate slices. Integrability
comes from the compact Cauchy data and forward traces, rather than an assumed energy bound.

This supplies a constant in the estimate (5) of Evans, §12.4, Theorem 2, uniform in the center and
the terminal time, under the standing assumption `g, h ∈ C_c^∞(ℝ³)` of §12.4. The solution is
forward C² below the vertex.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, standing assumptions and Theorem 2, equation (5).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE.Common PDE.Analysis

namespace WaveEquation

/-- Compact Cauchy data give a single quantitative cone-flux coefficient depending
only on the global initial energy. It works for every center, terminal time, and
slice on which the forward classical quintic wave exists. -/
theorem integral_quinticSlice_le_globalInitialEnergy_flux_rpow_of_compact_data {u : ℝ^4 → ℝ}
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 1 g) (hh : Continuous h) (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h) (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x) :
    let E := forwardSemilinearWaveEnergy (Real.signedPowerPotential 5) u 0
    ∀ {T : ℝ}, 0 < T → ContDiffOn ℝ 2 u {p | 0 ≤ p 0 ∧ p 0 < T} →
      (∀ t ∈ Ioo 0 T, ∀ x : ℝ^3,
        waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) →
      ∀ c : ℝ^3, ∀ s ∈ Ico 0 T,
        let φ := (1 / Real.sqrt 2) * (∫ p in
          {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
            semilinearWaveConeDissipation (Real.signedPowerPotential 5) u c p
              ∂Measure.euclideanHausdorffMeasure 3)
        (∫ x in Metric.ball c (T - s), u (timeSpaceCons s x) ^ 6) ≤
          (24 * E ^ (2 / 3 : ℝ) +
            12 * (∫ x in Metric.ball (0 : ℝ^3) 1,
              ‖x‖ ^ (-(3 / 2) : ℝ)) ^ (2 / 3 : ℝ) * (6 : ℝ) ^ (1 / 3 : ℝ)) *
                φ ^ (1 / 3 : ℝ) := by
  dsimp only
  intro T hT hu hwave c s hs
  have hVpos : ∀ z, 0 ≤ Real.signedPowerPotential 5 z :=
    fun z ↦ Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5) z
  have hρpos : ∀ x, 0 ≤
      forwardSemilinearWaveEnergyDensity (Real.signedPowerPotential 5) u 0 x := by
    intro x
    unfold forwardSemilinearWaveEnergyDensity
    exact add_nonneg (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))) (hVpos _)
  have hi := integrable_forwardSemilinearWaveEnergyDensity_initial_of_compact_data hT
    (Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5)).continuous
    (Real.signedPowerPotential_zero (by norm_num : (1 : ℝ) ≤ 5))
    (hu.of_le (by norm_num)) hg hh hgc hhc hpos hvel
  have hE : (∫ x in Metric.ball c T,
      forwardSemilinearWaveEnergyDensity (Real.signedPowerPotential 5) u 0 x) ≤
      forwardSemilinearWaveEnergy (Real.signedPowerPotential 5) u 0 :=
    setIntegral_le_integral hi (ae_of_all _ hρpos)
  have hlocal := integral_quinticSlice_le_initialEnergy_flux_rpow_of_contDiffOn_forward
    hT hu c (fun t ht x _ ↦ hwave t ht x) s hs
  apply hlocal.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (mul_nonneg (by positivity)
    (integral_nonneg (semilinearWaveConeDissipation_nonneg hVpos u c))) _)
  apply add_le_add _ le_rfl
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (integral_nonneg hρpos) hE (by norm_num)) (by norm_num)

end WaveEquation
