/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PowerPotential.Classical
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.TruncatedEnergy
import CAS.ExactTactic

/-!
# Full quintic cone flux bounded by the bottom energy

Truncated physical conservation bounds every interior portion of the lateral
cone. Dominated exhaustion gives the bound on the whole open lateral surface,
with its Hausdorff normalization and no regularity at the vertex.

This is the bound of the flux `φ(s)` of Evans, §12.4, by the energy of the bottom ball, from the
flux identity (3) of §12.1.2, Theorem 2(i).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, Theorem 2(i), equation (3); §12.4, Notation.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter PDE PDE.Common PDE.Analysis
open scoped Topology

namespace WaveEquation

/-- The full future null energy flux is bounded by the bottom energy.
Only an open regularity band below the vertex is needed. -/
theorem normalized_integral_quinticConeDissipation_le_energy {u : ℝ^4 → ℝ} {s₀ s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : s₀ < s) (hsT : s < T)
    (hwave : ∀ t ∈ Ico s T, ∀ x ∈ ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    (1 / Real.sqrt 2) * (∫ p in
      {p | s < p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0},
        semilinearWaveConeDissipation (Real.signedPowerPotential 5) u c p
          ∂Measure.euclideanHausdorffMeasure 3) ≤
      ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity (Real.signedPowerPotential 5) u
        (timeSpaceCons s x)) c (T - s) := by
  let V := Real.signedPowerPotential 5
  let D := semilinearWaveConeDissipation V u c
  let S := {p : ℝ^4 | s ≤ p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0}
  let E := ballIntegral 3 (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s)
  have hV : ContDiff ℝ 1 V :=
    Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5)
  have hVpos : ∀ z, 0 ≤ V z :=
    fun z ↦ Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5) z
  have hw : ∀ t ∈ Ico s T, ∀ x ∈ ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0 := by
    intro t ht x hx
    unfold semilinearWaveOperator V
    rw [(Real.hasDerivAt_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5) _).deriv]
    unfold Real.signedPower
    rw [show (5 : ℝ) - 1 = (4 : ℕ) by norm_num, Real.rpow_natCast,
      (show Even 4 by decide).pow_abs]
    have he : u (timeSpaceCons t x) ^ 4 * u (timeSpaceCons t x) =
        u (timeSpaceCons t x) ^ 5 := by cas
    rw [he]
    exact hwave t ht x hx
  have hD : IntegrableOn D S (Measure.euclideanHausdorffMeasure 3) :=
    integrableOn_cone_dissipation hV hVpos hu c hs hw
  have hpos : ∀ p, 0 ≤ D p := semilinearWaveConeDissipation_nonneg hVpos u c
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (Measure.euclideanHausdorffMeasure 3).restrict S) (l := 𝓝[<] T)
    (f := D) (F := fun τ ↦ (truncatedConeLateralSurface c T s τ).indicator D) (fun p ↦ ‖D p‖)
    (Eventually.of_forall fun τ ↦ hD.aestronglyMeasurable.indicator
      (isCompact_truncatedConeLateralSurface c T s τ).measurableSet)
    (Eventually.of_forall fun τ ↦ Eventually.of_forall fun p ↦ norm_indicator_le_norm_self D p)
    hD.norm ?_
  · have hbound : ∀ᶠ τ in 𝓝[<] T, (1 / Real.sqrt 2) * (∫ p in S,
          (truncatedConeLateralSurface c T s τ).indicator D p
            ∂Measure.euclideanHausdorffMeasure 3) ≤ E := by
      have he : ∀ᶠ τ in 𝓝[<] T, s < τ := (eventually_gt_nhds hsT).filter_mono nhdsWithin_le_nhds
      filter_upwards [he, self_mem_nhdsWithin] with τ hsτ hτ
      rw [integral_indicator (isCompact_truncatedConeLateralSurface c T s τ).measurableSet,
        Measure.restrict_restrict (isCompact_truncatedConeLateralSurface c T s τ).measurableSet,
        inter_eq_left.mpr (show truncatedConeLateralSurface c T s τ ⊆ S from
          fun _ hp ↦ ⟨hp.1, hp.2.1.trans_lt hτ, hp.2.2⟩)]
      exact integral_truncatedCone_flux_le_energy hV hVpos hu c hs hsτ.le hτ
        (fun t ht ↦ hw t ⟨ht.1, ht.2.trans_lt hτ⟩)
    have hb := le_of_tendsto (hlim.const_mul (1 / Real.sqrt 2)) hbound
    apply le_trans (mul_le_mul_of_nonneg_left ?_ (by positivity)) hb
    exact setIntegral_mono_set hD (ae_of_all _ hpos)
      (Eventually.of_forall fun _ hp ↦ ⟨hp.1.le, hp.2⟩)
  · have hS : MeasurableSet S := by
      dsimp only [S]
      exact (isClosed_le continuous_const (EuclideanSpace.proj 0).continuous).measurableSet.inter
        ((isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const).measurableSet.inter
          (isClosed_eq (((spatialPartCLM 3).continuous.sub continuous_const).norm)
            (continuous_const.sub (EuclideanSpace.proj 0).continuous)).measurableSet)
    filter_upwards [ae_restrict_mem hS] with p hp
    apply tendsto_const_nhds.congr'
    have he : ∀ᶠ τ in 𝓝[<] T, p 0 < τ := (eventually_gt_nhds hp.2.1).filter_mono nhdsWithin_le_nhds
    filter_upwards [he] with τ hτ
    exact (indicator_of_mem (show p ∈ truncatedConeLateralSurface c T s τ from
      ⟨hp.1, hτ.le, hp.2.2⟩) D).symm

end WaveEquation
