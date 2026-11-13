/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.PDEAmplitude
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.CompactSlab
import PDE.Hyperbolic.NonlinearWave.FinitePropagation.QuadraticLowerBound
import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.FreeWave

/-!
# Compact Cauchy data supply the subcritical amplitude inputs

Finite propagation (Evans, §12.1.2, Theorem 2(ii)) supplies compact support on every finite lifespan
slab. Continuity then bounds amplitude on that slab and makes the energy density integrable,
including at the initial and terminal slices. Conservation (§12.1.1, Theorem 1) identifies that
energy with the energy of the data. The subcritical estimate removes the preliminary amplitude
bound, uniformly over all shorter lifespan slabs.

This is an a priori theorem for ambient C² candidates with the PDE and Cauchy traces. It gives the
bound `‖u‖_{L^∞(ℝ³ × (0,T))} ≤ C(T)` that step 1 of the proof of Theorem 3 of Evans, §12.3.3, sets
out to prove.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1; §12.1.2, Theorem 2(ii); §12.3.3,
  Theorem 3 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric PDE PDE.Common PDE.Analysis WaveEquation

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- Compact initial support propagates at unit speed throughout a finite slab.
Continuity of the PDE residual supplies its initial-time value. -/
theorem eq_zero_of_initial_support {p : ℝ} (hp : 1 ≤ p) {u : ℝ^4 → ℝ} (hu : ContDiff ℝ 2 u)
    {S R : ℝ} (hS : 0 < S)
    (hwave : ∀ t ∈ Ioo 0 S, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) +
      Real.signedPower p (u (timeSpaceCons t x)) = 0)
    (hg : ∀ x : ℝ^3, R < ‖x‖ → u (timeSpaceCons 0 x) = 0)
    (hh : ∀ x : ℝ^3, R < ‖x‖ → (∂[0] u) (timeSpaceCons 0 x) = 0) :
    ∀ t ∈ Icc 0 S, ∀ x : ℝ^3, R + t < ‖x‖ → u (timeSpaceCons t x) = 0 := by
  have hV := Real.contDiff_one_signedPowerPotential hp
  have hclosed (x : ℝ^3) : EqOn
      (fun t ↦ semilinearWaveOperator (Real.signedPowerPotential p) u (timeSpaceCons t x))
      (fun _ ↦ 0) (Icc 0 S) := by
    have hc : Continuous
        (fun t ↦ semilinearWaveOperator (Real.signedPowerPotential p) u (timeSpaceCons t x)) :=
      ((continuous_waveOperator_of_contDiff_two hu).add
        (hV.continuous_deriv_one.comp hu.continuous)).comp
          ((contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous.comp
            (continuous_id.prodMk continuous_const))
    have he : EqOn
        (fun t ↦ semilinearWaveOperator (Real.signedPowerPotential p) u (timeSpaceCons t x))
        (fun _ ↦ 0) (Ioo 0 S) := by
      intro t ht
      simpa only [semilinearWaveOperator, (Real.hasDerivAt_signedPowerPotential hp _).deriv]
        using hwave t ht x
    simpa only [closure_Ioo hS.ne] using he.closure hc continuous_const
  intro t ht x hx
  have haway (y : ℝ^3) (hy : y ∈ closedBall x (t - 0)) : R < ‖y‖ := by
    have hd : ‖x - y‖ ≤ t := by
      simpa only [mem_closedBall, dist_eq_norm, sub_zero, norm_sub_rev] using hy
    have hn := norm_sub_norm_le x y
    linarith
  have hz := eq_zero_on_closed_backwardCone_semilinear hV
    (Real.signedPowerPotential_nonneg hp) (Real.signedPowerPotential_zero hp) hu x
    (a := 0) (T := t) (fun s hs y _ ↦ hclosed y ⟨hs.1, hs.2.le.trans ht.2⟩)
    (fun y hy ↦ hg y (haway y hy)) (fun y hy ↦ hh y (haway y hy))
  exact hz t ⟨ht.1, le_rfl⟩ x (by simp)

/-- Continuous fields with common compact spatial support are bounded on a
closed time slab. This supplies the preliminary bound used by the nonlinear
amplitude estimate. -/
theorem exists_bound_of_compact_slab {u : ℝ^4 → ℝ} (hu : Continuous u) {S : ℝ} {K : Set (ℝ^3)}
    (hK : IsCompact K) (hs : ∀ t ∈ Icc 0 S, ∀ x ∉ K, u (timeSpaceCons t x) = 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc 0 S, ∀ x, |u (timeSpaceCons t x)| ≤ A := by
  have hc : Continuous (fun z : ℝ × ℝ^3 ↦ u (timeSpaceCons z.1 z.2)) :=
    hu.comp (contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous
  obtain ⟨A, hA⟩ := (((isCompact_Icc.prod hK).image hc).isBounded).exists_norm_le
  refine ⟨max A 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · exact (hA _ ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left _ _)
  · rw [hs t ht x hx, abs_zero]
    exact le_max_right _ _

/-- Common compact support of the field on a closed positive slab also
supports its energy density at the endpoint slices. -/
theorem integrable_energy_of_compact_slab {V : ℝ → ℝ} {u : ℝ^4 → ℝ} (hV : ContDiff ℝ 1 V)
    (hV0 : V 0 = 0) (hu : ContDiff ℝ 2 u) {S : ℝ} (hS : 0 < S) {K : Set (ℝ^3)} (hK : IsCompact K)
    (hs : ∀ t ∈ Icc 0 S, ∀ x ∉ K, u (timeSpaceCons t x) = 0) {t : ℝ} (ht : t ∈ Icc 0 S) :
    Integrable (semilinearWaveSpatialEnergyDensity V u t) := by
  have hc : Continuous (Function.uncurry (semilinearWaveSpatialEnergyDensity V u)) :=
    (contDiff_semilinearWaveEnergyDensity hV hu).continuous.comp
      (contDiff_timeSpaceCons_uncurry 3 (m := 1)).continuous
  apply (hc.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
  refine HasCompactSupport.intro hK ?_
  intro x hx
  have he : EqOn (fun s ↦ semilinearWaveSpatialEnergyDensity V u s x)
      (fun _ ↦ 0) (Ioo 0 S) := by
    intro s hsI
    exact semilinearWaveSpatialEnergyDensity_eq_zero_off_support hV0 isOpen_Ioo
      hK.isClosed (fun _ _ _ ↦ (hu.of_le (by norm_num)).contDiffAt)
      (fun s hsI y hy ↦ hs s (Ioo_subset_Icc_self hsI) y hy) hsI hx
  have hcl := he.closure (hc.comp (continuous_id.prodMk continuous_const)) continuous_const
  rw [closure_Ioo hS.ne] at hcl
  exact hcl ht

/-- Two differentiable fields with identical Cauchy data have identical
initial physical energies. No evolution equation is needed. -/
theorem spatialEnergy_zero_eq_of_initial_data (V : ℝ → ℝ) {u v : ℝ^4 → ℝ} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (hg : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = v (timeSpaceCons 0 x))
    (hh : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = (∂[0] v) (timeSpaceCons 0 x)) :
    semilinearWaveSpatialEnergy V u 0 = semilinearWaveSpatialEnergy V v 0 := by
  have he : (fun x : ℝ^3 ↦ u (timeSpaceCons 0 x)) = fun x ↦ v (timeSpaceCons 0 x) := funext hg
  have hgrad (x : ℝ^3) : classicalWaveSpatialGradient u (timeSpaceCons 0 x) =
      classicalWaveSpatialGradient v (timeSpaceCons 0 x) := by
    apply PiLp.ext
    intro i
    simp only [classicalWaveSpatialGradient_apply]
    rw [← partialDeriv_timeSpaceCons_spatial i u 0 x (hu _), he,
      partialDeriv_timeSpaceCons_spatial i v 0 x (hv _)]
  unfold semilinearWaveSpatialEnergy
  apply integral_congr_ae
  filter_upwards with x
  simp only [semilinearWaveSpatialEnergyDensity, semilinearWaveEnergyDensity,
    classicalWaveEnergyDensity, hg x, hh x, hgrad x]

/-- Smooth compact Cauchy data give a uniform amplitude bound for every
ambient C² solution on every shorter slab. Only the nonlinear PDE and
initial traces are assumed of the candidate. The constant depends on the data,
the real exponent `1 < p < 5`, and the fixed time horizon. -/
theorem exists_uniform_amplitude_bound_of_compact_data {p : ℝ} (hp : 1 < p) (hp5 : p < 5) (T : ℝ)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ B : ℝ, 0 < B ∧ ∀ (S : ℝ) (u : ℝ^4 → ℝ),
      0 < S → S ≤ T → ContDiff ℝ 2 u →
      (∀ x, u (timeSpaceCons 0 x) = g x) →
      (∀ x, (∂[0] u) (timeSpaceCons 0 x) = h x) →
      (∀ t ∈ Ioo 0 S, ∀ x,
        waveOperator u (timeSpaceCons t x) + Real.signedPower p (u (timeSpaceCons t x)) = 0) →
      ∀ t ∈ Ioc 0 S, ∀ x, |u (timeSpaceCons t x)| ≤ B := by
  obtain ⟨Rg, _, hgR⟩ := hgs.exists_pos_le_norm
  obtain ⟨Rh, _, hhR⟩ := hhs.exists_pos_le_norm
  let R := max Rg Rh
  have hgR' (x : ℝ^3) (hx : R < ‖x‖) : g x = 0 := hgR x ((le_max_left _ _).trans hx.le)
  have hhR' (x : ℝ^3) (hx : R < ‖x‖) : h x = 0 := hhR x ((le_max_right _ _).trans hx.le)
  obtain ⟨G, hG⟩ := hg.continuous.bounded_above_of_compact_support hgs
  have hG0 : 0 ≤ G := (norm_nonneg (g 0)).trans (hG 0)
  let v := spaceTimeUncurry (kirchhoffFormula g h)
  have hv : ContDiff ℝ 2 v := contDiff_two_kirchhoffFormula hg hh
  let K := closedBall (0 : ℝ^3) (R + T)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hvK : ∀ t ∈ Icc 0 T, ∀ x ∉ K, v (timeSpaceCons t x) = 0 := by
    intro t ht x hx
    apply WaveEquation.SmallData.kirchhoffFormula_hasForwardSupport
      (hg.of_le (by norm_num)) hh.continuous hgR' hhR' t ht.1 x
    have hx' : R + T < ‖x‖ := by
      simpa only [K, mem_closedBall, dist_zero_right, not_le] using hx
    linarith [ht.2]
  obtain ⟨V, hV0, hVbound⟩ := exists_bound_of_compact_slab hv.continuous hK hvK
  let E := √(2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential p) v 0)
  have hE0 : 0 ≤ E := Real.sqrt_nonneg _
  have hEsq : E ^ 2 = 2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential p) v 0 :=
    Real.sq_sqrt (mul_nonneg (by norm_num)
      (semilinearWaveSpatialEnergy_nonneg _ (Real.signedPowerPotential_nonneg hp.le) v 0))
  obtain ⟨B, hB, hbound⟩ := exists_uniform_amplitude_bound_of_power_solution hp hp5 T E G V
    hE0 hG0 hV0
  refine ⟨B, hB, ?_⟩
  intro S u hS hST hu hposition hinitial hwave
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hs := eq_zero_of_initial_support hp.le hu2 hS hwave
    (fun x hx ↦ (hposition x).trans (hgR' x hx)) (fun x hx ↦ (hinitial x).trans (hhR' x hx))
  have huK : ∀ t ∈ Icc 0 S, ∀ x ∉ K, u (timeSpaceCons t x) = 0 := by
    intro t ht x hx
    apply hs t ht x
    have hx' : R + T < ‖x‖ := by
      simpa only [K, mem_closedBall, dist_zero_right, not_le] using hx
    linarith [ht.2]
  have hpot := Real.contDiff_one_signedPowerPotential hp.le
  have hpot0 := Real.signedPowerPotential_zero hp.le
  have hw (t : ℝ) (ht : t ∈ Ioo 0 S) (x : ℝ^3) :
      semilinearWaveOperator (Real.signedPowerPotential p) u (timeSpaceCons t x) = 0 := by
    simpa only [semilinearWaveOperator, (Real.hasDerivAt_signedPowerPotential hp.le _).deriv]
      using hwave t ht x
  have he0 : semilinearWaveSpatialEnergy (Real.signedPowerPotential p) u 0 =
      semilinearWaveSpatialEnergy (Real.signedPowerPotential p) v 0 := by
    apply spatialEnergy_zero_eq_of_initial_data _ (hu2.differentiable (by norm_num))
      (hv.differentiable (by norm_num))
    · intro x
      simpa only [v, kirchhoffFormula_initial_position] using hposition x
    · intro x
      simpa only [v, partialDeriv_kirchhoffFormula_initial_velocity
        (hg.of_le (by norm_num)) (hh.of_le (by norm_num))] using hinitial x
  obtain ⟨A, _, hA⟩ := exists_bound_of_compact_slab hu.continuous hK huK
  apply hbound S u g h hS hST hu hg hh hposition hinitial hG
    (fun t ht x ↦ hVbound t ⟨ht.1.le, ht.2.trans hST⟩ x) hwave
    (fun t ht ↦ integrable_energy_of_compact_slab hpot hpot0 hu2 hS hK huK ht)
  · intro t ht
    rw [semilinearWaveSpatialEnergy_eq_of_compact_support_on_Icc hpot hpot0 hu2 hK
      hS huK hw ht, he0, hEsq]
  · exact ⟨A, fun t ht x ↦ hA t (Ioc_subset_Icc_self ht) x⟩

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
