/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ConeFlux
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ConeEnergyContinuity
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Transport

/-!
# Energy flux through the closed lateral cone

The transport identity, continuity at the vertex, and normalized Hausdorff
coarea balance the initial energy, outgoing flux, and the work of the equation's
residual. For an exact solution the residual vanishes, giving the flux identity (3) of Evans,
§12.1.2, Theorem 2(i), including both endpoints.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(i) and its proof, equations (3)-(4).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Common PDE.Analysis

namespace WaveEquation

variable {n : ℕ}

/-- The outgoing cone flux equals the initial energy plus the work of the
wave-equation residual inside the cone. Keeping the residual allows the
identity to be used before a smooth approximation solves the equation exactly. -/
theorem normalized_integral_semilinearWaveConeDissipation_eq_energy_add_residual [Fact (0 < n)]
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u) (c : ℝ^n) {T : ℝ}
    (hT : 0 ≤ T) :
    (1 / Real.sqrt 2) *
        (∫ p in backwardConeLateralSurface c T,
          semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) =
      semilinearBackwardConeEnergy V u c T 0 +
        ∫ t in (0 : ℝ)..T, ballIntegral n
          (fun x ↦ semilinearWaveEnergyBalanceResidual V u (timeSpaceCons t x))
          c (T - t) := by
  rw [normalized_integral_backwardConeLateralSurface_eq_timeIntegral c hT _
    (measurable_semilinearWaveConeDissipation hV.continuous hu c).aestronglyMeasurable
    (integrableOn_semilinearWaveConeDissipation_graph hV.continuous hu c T)]
  let D (t : ℝ) := sphereIntegral n
    (fun x ↦ semilinearWaveConeDissipation V u c (timeSpaceCons t x)) c (T - t)
  let R (t : ℝ) := ballIntegral n
    (fun x ↦ semilinearWaveEnergyBalanceResidual V u (timeSpaceCons t x)) c (T - t)
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (semilinearBackwardConeEnergy V u c T) (R t - D t) t := by
    apply (hasDerivAt_semilinearBackwardConeEnergy hV hu c T ht.2).congr_deriv
    change R t + sphereIntegral n _ c (T - t) = R t - sphereIntegral n _ c (T - t)
    rw [sub_eq_add_neg]
    congr 1
    rw [← sphereIntegral_neg]
    apply sphereIntegral_congr_on_sphere (sub_pos.mpr ht.2)
    intro x hx
    apply semilinearWaveConeBoundaryFlux_eq_neg_dissipation
    intro hxc
    subst x
    have hz : 0 = T - t := by simpa only [Metric.mem_sphere, dist_self] using hx
    linarith [ht.2]
  have hiD : IntervalIntegrable D volume 0 T :=
    intervalIntegrable_sphereIntegral_semilinearWaveConeDissipation hV.continuous hu c hT
  have hiR : IntervalIntegrable R volume 0 T := ((continuousOn_ballIntegral_shrinking
      (contDiff_semilinearWaveEnergyBalanceResidual (m := 0) hV hu).continuous c T).mono
        Icc_subset_Iic_self).intervalIntegrable_of_Icc hT
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    ((continuousOn_semilinearBackwardConeEnergy hV hu c T).mono Icc_subset_Iic_self)
    hder (hiR.sub hiD)
  have hz : semilinearBackwardConeEnergy V u c T T = 0 := by
    rw [semilinearBackwardConeEnergy_eq_ballIntegral hV.continuous
      (hu.of_le (by norm_num))]
    simp [ballIntegral]
  rw [intervalIntegral.integral_sub hiR hiD, hz] at hFTC
  change (∫ t in (0 : ℝ)..T, D t) = _
  linarith

/-- Evans, §12.1.2, Theorem 2(i), equation (3): the energy at the base equals the
outgoing null flux through the closed lateral cone. The surface measure is
normalized Euclidean n-dimensional Hausdorff measure, with the factor
1/√2. Smoothness discharges all integrability and endpoint hypotheses. -/
theorem normalized_integral_semilinearWaveConeDissipation [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u) (c : ℝ^n) {T : ℝ} (hT : 0 ≤ T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0) :
    (1 / Real.sqrt 2) * (∫ p in backwardConeLateralSurface c T, semilinearWaveConeDissipation V u c
      p ∂Measure.euclideanHausdorffMeasure n) = semilinearBackwardConeEnergy V u c T 0 := by
  rw [normalized_integral_semilinearWaveConeDissipation_eq_energy_add_residual hV hu c hT]
  suffices hzero : (∫ t in (0 : ℝ)..T, ballIntegral n
      (fun x ↦ semilinearWaveEnergyBalanceResidual V u (timeSpaceCons t x)) c (T - t)) = 0 by
    rw [hzero, add_zero]
  calc
    _ = ∫ _ in (0 : ℝ)..T, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hT
      intro t ht
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      exact semilinearWaveEnergyBalanceResidual_eq_zero hV hu.contDiffAt (hwave t ht x hx)
    _ = 0 := intervalIntegral.integral_zero


end WaveEquation
