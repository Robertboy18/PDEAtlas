/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.TruncatedEnergy
import PDE.Analysis.Calculus.LocalExtension.TimeBand
import PDE.Hyperbolic.Classical.ForwardLocalization

/-!
# Truncated cone energy inside an independent regularity band

The geometric vertex time may lie beyond the interval where the wave is defined
smoothly. A temporal cutoff preserves the field's germs around the two caps and
lateral surface, so the energy identity applies without extending the
solution of the PDE beyond that interval.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE PDE.Common PDE.Analysis
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- The residual form of the energy identity needs regularity only around
the two caps. The geometric vertex may lie beyond this regularity band. -/
theorem ballIntegral_energy_add_truncatedCone_flux_eq_energy_add_residual_on_band [Fact (0 < n)]
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) {u : ℝ^(n + 1) → ℝ}
    {a b s τ T : ℝ} (hu : ContDiffOn ℝ 2 u {p | a < p 0 ∧ p 0 < b})
    (c : ℝ^n) (has : a < s) (hsτ : s ≤ τ) (hτb : τ < b) (hτT : τ < T) :
    ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons τ x)) c (T - τ) +
      (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) =
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s) +
        ∫ t in s..τ, ballIntegral n
          (fun x ↦ semilinearWaveEnergyBalanceResidual V u (timeSpaceCons t x))
          c (T - t) := by
  obtain ⟨U, hU, heq⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band
    (k := 2) (f := u) (EuclideanSpace.proj 0 : ℝ^(n + 1) →L[ℝ] ℝ)
    (by simpa using hu) has hτb
  simp only [EuclideanSpace.coe_proj] at heq
  have hlocal (t : ℝ) (ht : t ∈ Icc s τ) (x : ℝ^n) : u =ᶠ[𝓝 (timeSpaceCons t x)] U :=
    heq _ (by simpa only [timeSpaceCons_zero] using ht)
  have hcap (t : ℝ) (ht : t ∈ Icc s τ) :
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons t x)) c (T - t) =
        ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V U (timeSpaceCons t x))
          c (T - t) := by
    unfold ballIntegral
    apply setIntegral_congr_fun measurableSet_ball
    intro x _
    have he := hlocal t ht x
    simp only [semilinearWaveEnergyDensity, classicalWaveEnergyDensity_congr_nhds he, he.eq_of_nhds]
  have hflux : (∫ p in truncatedConeLateralSurface c T s τ,
      semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) =
      ∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation V U c p ∂Measure.euclideanHausdorffMeasure n := by
    apply setIntegral_congr_fun (isCompact_truncatedConeLateralSurface c T s τ).measurableSet
    intro p hp
    have he := heq p ⟨hp.1, hp.2.1⟩
    simp only [semilinearWaveConeDissipation, semilinearWaveNullFlux,
      classicalWaveSpatialGradient, partialDeriv_congr_nhds _ he, he.eq_of_nhds]
  have hres : (∫ t in s..τ, ballIntegral n
      (fun x ↦ semilinearWaveEnergyBalanceResidual V u (timeSpaceCons t x)) c (T - t)) =
      ∫ t in s..τ, ballIntegral n
        (fun x ↦ semilinearWaveEnergyBalanceResidual V U (timeSpaceCons t x)) c (T - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hsτ] at ht
    apply setIntegral_congr_fun measurableSet_ball
    intro x _
    have he := hlocal t ht x
    dsimp only
    rw [semilinearWaveEnergyBalanceResidual_eq_mul_operator hV
      (hU.contDiffAt.congr_of_eventuallyEq he),
      semilinearWaveEnergyBalanceResidual_eq_mul_operator hV hU.contDiffAt]
    simp only [semilinearWaveOperator, partialDeriv_congr_nhds _ he,
      waveOperator_congr_nhds he, he.eq_of_nhds]
  rw [hcap τ ⟨hsτ, le_rfl⟩, hcap s ⟨le_rfl, hsτ⟩, hflux, hres]
  exact ballIntegral_energy_add_truncatedCone_flux_eq_energy_add_residual
    hV hU.contDiffOn c has hsτ hτT

/-- Energy at the upper cap plus normalized lateral flux equals energy at the
lower cap. The regularity band and geometric vertex time are independent. -/
theorem ballIntegral_energy_add_truncatedCone_flux_of_contDiffOn_finite_band [Fact (0 < n)]
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) {u : ℝ^(n + 1) → ℝ}
    {a b s τ T : ℝ} (hu : ContDiffOn ℝ 2 u {p | a < p 0 ∧ p 0 < b})
    (c : ℝ^n) (has : a < s) (hsτ : s ≤ τ) (hτb : τ < b) (hτT : τ < T)
    (hwave : ∀ t ∈ Icc s τ, ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0) :
    ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons τ x)) c (T - τ) +
      (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) =
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s) := by
  have hopen : IsOpen {p : ℝ^(n + 1) | a < p 0 ∧ p 0 < b} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hzero : (∫ t in s..τ, ballIntegral n
      (fun x ↦ semilinearWaveEnergyBalanceResidual V u (timeSpaceCons t x)) c (T - t)) = 0 := by
    rw [intervalIntegral.integral_of_le hsτ]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have ht : t ∈ Icc s τ := ⟨ht.1.le, ht.2⟩
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hup := hu.contDiffAt (hopen.mem_nhds
      (show a < (timeSpaceCons t x) 0 ∧ (timeSpaceCons t x) 0 < b by
        simpa only [timeSpaceCons_zero] using And.intro (has.trans_le ht.1) (ht.2.trans_lt hτb)))
    exact semilinearWaveEnergyBalanceResidual_eq_zero hV hup (hwave t ht x hx)
  simpa only [hzero, add_zero] using
    ballIntegral_energy_add_truncatedCone_flux_eq_energy_add_residual_on_band
      hV hu c has hsτ hτb hτT

/-- Nonnegative potential makes energy decrease between two caps inside the
regularity band, even when the geometric vertex lies beyond that band. -/
theorem ballIntegral_energy_le_of_le_of_contDiffOn_finite_band [Fact (0 < n)] {V : ℝ → ℝ}
    (hV : ContDiff ℝ 1 V) (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} {a b s τ T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | a < p 0 ∧ p 0 < b}) (c : ℝ^n) (has : a < s) (hsτ : s ≤ τ)
    (hτb : τ < b) (hτT : τ < T)
    (hwave : ∀ t ∈ Icc s τ, ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0) :
    ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons τ x)) c (T - τ) ≤
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s) := by
  have h := ballIntegral_energy_add_truncatedCone_flux_of_contDiffOn_finite_band
    hV hu c has hsτ hτb hτT hwave
  have hflux : 0 ≤ (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) :=
    mul_nonneg (by positivity) (integral_nonneg fun p ↦
      semilinearWaveConeDissipation_nonneg hVnonneg u c p)
  linarith

/-- Shrinking-ball energy is antitone at the regular times below the geometric
vertex. -/
theorem ballIntegral_energy_antitoneOn_of_contDiffOn_finite_band [Fact (0 < n)] {V : ℝ → ℝ}
    (hV : ContDiff ℝ 1 V) (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} {a b T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | a < p 0 ∧ p 0 < b}) (c : ℝ^n)
    (hwave : ∀ t ∈ Ioo a b ∩ Iio T, ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator V u (timeSpaceCons t x) = 0) :
    AntitoneOn (fun t ↦ ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons t x))
      c (T - t)) (Ioo a b ∩ Iio T) := by
  intro s hs τ hτ hsτ
  exact ballIntegral_energy_le_of_le_of_contDiffOn_finite_band hV hVnonneg hu c
    hs.1.1 hsτ hτ.1.2 hτ.2 (fun t ht ↦ hwave t
      ⟨⟨hs.1.1.trans_le ht.1, ht.2.trans_lt hτ.1.2⟩, ht.2.trans_lt hτ.2⟩)

end WaveEquation
