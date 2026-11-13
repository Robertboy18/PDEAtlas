/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Nonconcentration.Quantitative
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ForwardBasic
import PDE.Analysis.Calculus.LocalExtension.ForwardBand
import PDE.Hyperbolic.Classical.ForwardLocalization

/-!
# Quintic nonconcentration up to the initial time

The quintic wave on the forward band satisfies the quantitative one-third-power cone-flux estimate
for every initial or interior slice. Initial energy uses the differential within the forward
half-space. A smooth extension across its lower edge is derived, and all positive-time derivatives
are unchanged. There is no regularity assumption at the terminal vertex.

This is the estimate (5) of Evans, §12.4, Theorem 2, for every slice `0 ≤ s < T`, with an explicit
constant depending on the initial cone energy.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, Notation and Theorem 2, equation (5).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE PDE.Common PDE.Analysis
open scoped Topology

namespace WaveEquation

/-- The quantitative quintic cone estimate for every forward slice, including
zero. The initial energy uses the differential within the forward half-space. -/
theorem integral_quinticSlice_le_initialEnergy_flux_rpow_of_contDiffOn_forward {u : ℝ^4 → ℝ} {T : ℝ}
    (hT : 0 < T) (hu : ContDiffOn ℝ 2 u {p | 0 ≤ p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    let E := ∫ x in Metric.ball c T,
      forwardSemilinearWaveEnergyDensity (Real.signedPowerPotential 5) u 0 x
    ∀ s ∈ Ico 0 T,
      let φ := (1 / Real.sqrt 2) * (∫ p in
        {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
          semilinearWaveConeDissipation (Real.signedPowerPotential 5) u c p
            ∂Measure.euclideanHausdorffMeasure 3)
      (∫ x in Metric.ball c (T - s), u (timeSpaceCons s x) ^ 6) ≤
        (24 * E ^ (2 / 3 : ℝ) +
          12 * (∫ x in Metric.ball (0 : ℝ^3) 1, ‖x‖ ^ (-(3 / 2) : ℝ)) ^ (2 / 3 : ℝ) *
            (6 : ℝ) ^ (1 / 3 : ℝ)) * φ ^ (1 / 3 : ℝ) := by
  obtain ⟨v, hv, heq⟩ := exists_contDiffOn_extension_halfOpenBand 0 hT hu
  have hgerm {p : ℝ^4} (hp : 0 < p 0) : v =ᶠ[𝓝 p] u := eventuallyEq_of_eqOn_forward heq hp
  have hwv : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator v (timeSpaceCons t x) + v (timeSpaceCons t x) ^ 5 = 0 := by
    intro t ht x hx
    have he := hgerm (show 0 < (timeSpaceCons t x) 0 by simpa using ht.1)
    rw [waveOperator_congr_nhds he, he.eq_of_nhds]
    exact hwave t ht x hx
  have henergy (x : ℝ^3) :
      semilinearWaveEnergyDensity (Real.signedPowerPotential 5) v (timeSpaceCons 0 x) =
        forwardSemilinearWaveEnergyDensity (Real.signedPowerPotential 5) u 0 x := by
    have hopen : IsOpen {p : ℝ^4 | p 0 < T} :=
      isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const
    have hvat := hv.contDiffAt (hopen.mem_nhds
      (show (timeSpaceCons 0 x) 0 < T by simpa using hT))
    have hdf : forwardDifferential u 0 x = fderiv ℝ v (timeSpaceCons 0 x) := by
      unfold forwardDifferential
      rw [max_self, ← fderivWithin_congr' heq (show 0 ≤ (timeSpaceCons 0 x) 0 by simp)]
      exact (hvat.differentiableAt (by norm_num)).fderivWithin
        (uniqueDiffOn_forward_halfSpace _ (by simp))
    unfold forwardSemilinearWaveEnergyDensity semilinearWaveEnergyDensity
      classicalWaveEnergyDensity classicalWaveSpatialGradient
    rw [hdf, max_self, ← heq (show 0 ≤ (timeSpaceCons 0 x) 0 by simp)]
    rfl
  dsimp only
  intro s hs
  have hb := integral_quinticSlice_le_initialEnergy_flux_rpow_of_upper_band hT hv c hwv s hs
  have hflux : (∫ p in {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
        semilinearWaveConeDissipation (Real.signedPowerPotential 5) v c p
          ∂Measure.euclideanHausdorffMeasure 3) =
      ∫ p in {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
        semilinearWaveConeDissipation (Real.signedPowerPotential 5) u c p
          ∂Measure.euclideanHausdorffMeasure 3 := by
    apply setIntegral_congr_fun
      ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).measurableSet.inter
        ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).measurableSet.inter
          (isClosed_eq (((spatialPartCLM 3).continuous.sub continuous_const).norm)
            (continuous_const.sub (EuclideanSpace.proj 0).continuous)).measurableSet))
    intro p hp
    have he := hgerm (hs.1.trans_lt hp.1)
    simp only [semilinearWaveConeDissipation, semilinearWaveNullFlux,
      classicalWaveSpatialGradient, partialDeriv_congr_nhds _ he, he.eq_of_nhds]
  have hslice (x : ℝ^3) : v (timeSpaceCons s x) = u (timeSpaceCons s x) :=
    heq (by simpa using hs.1)
  simpa only [ballIntegral, henergy, hflux, hslice] using hb

end WaveEquation
