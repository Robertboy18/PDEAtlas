/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Cone.Convergence
public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.TruncatedEnergy.FiniteBand
public import PDE.Hyperbolic.NonlinearWave.Regularization.EnergyConvergence
public import PDE.Hyperbolic.NonlinearWave.Regularization.EnergyResidual

/-!
# Cone energy for C¹ tested waves

The finite-cone energy identity survives C¹ local uniform convergence when
its energy residual tends locally uniformly to zero. Compactness controls
both caps and the lateral surface; the shrinking-ball integral controls the
residual inside the cone.

For a C¹ tested semilinear wave with a common compact spatial support,
spatial convolution gives the required approximations. The resulting identity concerns the original
field.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE PDE.Common PDE.Analysis
open scoped Topology Convolution

namespace WaveEquation

/-- C¹ convergence and a vanishing energy residual preserve the finite-cone identity. -/
theorem ballIntegral_energy_add_truncatedCone_flux_of_approximation {n : ℕ} [Fact (0 < n)]
    {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {u : ℝ^(n + 1) → ℝ} {U : ι → ℝ^(n + 1) → ℝ} {a b s τ T : ℝ}
    (hu : ContDiffOn ℝ 1 u {p | a < p 0 ∧ p 0 < b})
    (hU : ∀ i, ContDiffOn ℝ 2 (U i) {p | a < p 0 ∧ p 0 < b})
    (hlim : TendstoLocallyUniformlyOn U u l {p | a < p 0 ∧ p 0 < b})
    (hD : ∀ j : Fin (n + 1), TendstoLocallyUniformlyOn (fun i ↦ ∂[j] (U i)) (∂[j] u) l
      {p | a < p 0 ∧ p 0 < b})
    (hR : TendstoLocallyUniformlyOn (fun i ↦ semilinearWaveEnergyBalanceResidual V (U i))
      (fun _ ↦ 0) l {p | a < p 0 ∧ p 0 < b})
    (c : ℝ^n) (has : a < s) (hsτ : s ≤ τ) (hτb : τ < b) (hτT : τ < T) :
    ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons τ x)) c (T - τ) +
      (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation V u c p ∂Measure.euclideanHausdorffMeasure n) =
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s) := by
  let S : Set (ℝ^(n + 1)) := {p | a < p 0 ∧ p 0 < b}
  have hS : IsOpen S :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hE := tendstoLocallyUniformlyOn_semilinearWaveEnergyDensity hV.continuous hu hS hlim hD
  have hEc (i : ι) : ContinuousOn (semilinearWaveEnergyDensity V (U i)) S := by
    intro p hp
    exact (contDiffAt_semilinearWaveEnergyDensity (m := 0)
      ((hV.of_le (by norm_num)).contDiffAt)
      (((hU i).of_le (by norm_num)).contDiffAt (hS.mem_nhds hp))).continuousAt.continuousWithinAt
  have hcap (t : ℝ) (ht : t ∈ Icc s τ) :
      Tendsto (fun i ↦ ballIntegral n
        (fun x ↦ semilinearWaveEnergyDensity V (U i) (timeSpaceCons t x)) c (T - t))
        l (𝓝 (ballIntegral n
          (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons t x)) c (T - t))) := by
    have hc : Continuous (timeSpaceCons t : ℝ^n → ℝ^(n + 1)) :=
      (timeSpaceContinuousLinearEquiv n).symm.continuous.comp
        (continuous_const.prodMk continuous_id)
    have hm : MapsTo (timeSpaceCons t) (Metric.closedBall c (T - t)) S := by
      intro x _
      exact ⟨has.trans_le ht.1, ht.2.trans_lt hτb⟩
    have hl := hE.comp (timeSpaceCons t) hm hc.continuousOn
    have hk := isCompact_closedBall c (T - t)
    have hl' := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hk).mp hl
    exact hl'.tendsto_setIntegral_of_continuousOn
        (Eventually.of_forall fun i ↦ (hEc i).comp hc.continuousOn hm)
        hk measurableSet_ball Metric.ball_subset_closedBall
        (measure_ball_lt_top.ne)
  let N : Set (ℝ^(n + 1)) := S ∩ {p | spatialPart p ≠ c}
  have hN : IsOpen N := hS.inter (isOpen_ne_fun (spatialPartCLM n).continuous continuous_const)
  have hnormal : ContinuousOn (fun p : ℝ^(n + 1) ↦
      NormedSpace.normalize (spatialPart p - c)) N := by
    have hx : ContinuousOn (fun p : ℝ^(n + 1) ↦ spatialPart p - c) N :=
      ((spatialPartCLM n).continuous.sub continuous_const).continuousOn
    exact (hx.norm.inv₀ (fun p hp ↦ norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp.2))).smul hx
  have hflux := tendstoLocallyUniformlyOn_semilinearWaveNullFlux hV.continuous
    (hu.mono inter_subset_left) hN hnormal (hlim.mono inter_subset_left)
    (fun j ↦ (hD j).mono inter_subset_left)
  have hfluxc (i : ι) : ContinuousOn (semilinearWaveConeDissipation V (U i) c) N := by
    have hui : ContDiffOn ℝ 1 (U i) N := (hU i).of_le (by norm_num) |>.mono inter_subset_left
    have ht := hui.continuousOn_partialDeriv 0 hN
    have hg := continuousOn_classicalWaveSpatialGradient hui hN
    exact (continuousOn_const.mul (((ht.smul hnormal).sub hg).norm.pow 2)).add
      (hV.continuous.comp_continuousOn hui.continuousOn)
  have hsurface : truncatedConeLateralSurface c T s τ ⊆ N := by
    intro p hp
    refine ⟨⟨has.trans_le hp.1, hp.2.1.trans_lt hτb⟩, ?_⟩
    intro heq
    have hn : ‖spatialPart p - c‖ = 0 := by rw [heq, sub_self, norm_zero]
    have hpos : 0 < T - p 0 := sub_pos.mpr (hp.2.1.trans_lt hτT)
    exact (ne_of_gt hpos) (hp.2.2.symm.trans hn)
  have hfluxlim := tendsto_integral_truncatedConeLateralSurface hflux
    (Eventually.of_forall hfluxc) c T s τ hsurface
  let K : Set (ℝ × ℝ^n) := Icc s τ ×ˢ Metric.closedBall c (T - s)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall c (T - s))
  let e := timeSpaceContinuousLinearEquiv n
  have hm : MapsTo e.symm K S := by
    intro p hp
    exact ⟨has.trans_le hp.1.1, hp.1.2.trans_lt hτb⟩
  have hRlim := hR.comp e.symm hm e.symm.continuous.continuousOn
  have hRcont (i : ι) : ContinuousOn
      (fun p : ℝ × ℝ^n ↦ semilinearWaveEnergyBalanceResidual V (U i) (e.symm p)) K :=
    (continuousOn_semilinearWaveEnergyBalanceResidual hV (hU i) hS).comp
      e.symm.continuous.continuousOn hm
  have hres := tendsto_integral_ballIntegral_shrinking c hsτ
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp hRlim)
    hRcont continuousOn_const
  simp only [Function.comp_apply, ballIntegral, integral_zero,
    intervalIntegral.integral_zero] at hres
  have heq (i : ι) := ballIntegral_energy_add_truncatedCone_flux_eq_energy_add_residual_on_band
    hV (hU i) c has hsτ hτb hτT
  have hleft := (hcap τ ⟨hsτ, le_rfl⟩).add (hfluxlim.const_mul (1 / Real.sqrt 2))
  have hright := (hcap s ⟨le_rfl, hsτ⟩).add hres
  simp only [add_zero] at hright
  exact tendsto_nhds_unique hleft (hright.congr fun i ↦ (heq i).symm)

/-- A C¹ tested semilinear wave obeys the exact energy identity on each finite cone.
Spatial smoothing supplies the second derivatives only for the approximations. -/
theorem ballIntegral_energy_add_truncatedCone_flux_of_tested_wave {n : ℕ} [Fact (0 < n)]
    {u : ℝ × ℝ^n → ℝ} {K : Set (ℝ^n)} {V : ℝ → ℝ} {a b s τ T : ℝ} (hK : IsCompact K)
    (hu : ContDiffOn ℝ 1 u (Ioo a b ×ˢ univ)) (hs : ∀ t ∈ Ioo a b, ∀ x ∉ K, u (t, x) = 0)
    (hV : ContDiff ℝ 1 V) (hV0 : deriv V 0 = 0)
    (hw : ∀ t ∈ Ioo a b, ∀ ψ : ℝ^n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      HasDerivAt (deriv (fun r ↦ ∫ y, u (r, y) * ψ y)) ((∫ y, u (t, y) * PDE.laplacian ψ y) - ∫ y,
      deriv V (u (t, y)) * ψ y) t)
    (c : ℝ^n) (has : a < s) (hsτ : s ≤ τ) (hτb : τ < b) (hτT : τ < T) :
    let v := fun p : ℝ^(n + 1) ↦ u (timeSpaceContinuousLinearEquiv n p)
    ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V v (timeSpaceCons τ x)) c (T - τ) +
      (1 / Real.sqrt 2) * (∫ p in truncatedConeLateralSurface c T s τ,
        semilinearWaveConeDissipation V v c p ∂Measure.euclideanHausdorffMeasure n) =
      ballIntegral n (fun x ↦ semilinearWaveEnergyDensity V v (timeSpaceCons s x)) c (T - s) := by
  let φ : ℕ → ContDiffBump (0 : ℝ^n) := fun j ↦
    { rIn := (1 / ((j : ℝ) + 1)) / 2
      rOut := 1 / ((j : ℝ) + 1)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hφ : Tendsto (fun j ↦ (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let e := timeSpaceContinuousLinearEquiv n
  let A := fun i (p : ℝ × ℝ^n) ↦
    ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
      (fun y ↦ u (p.1, y))) p.2
  let U := fun i (p : ℝ^(n + 1)) ↦ A i (e p)
  let v := fun p : ℝ^(n + 1) ↦ u (e p)
  let S : Set (ℝ^(n + 1)) := {p | a < p 0 ∧ p 0 < b}
  have hsub : S ⊆ spaceTimeCylinder univ (Ioo a b) := fun _ hp ↦ ⟨hp, mem_univ _⟩
  have hv : ContDiffOn ℝ 1 v S :=
    (hu.comp_continuousLinearMap e.toContinuousLinearMap).mono hsub
  have hreg (i : ℕ) : ContDiffOn ℝ 2 (U i) S := by
    exact (contDiffOn_two_convolution_timeSpace_of_tested_wave
      (F := fun p ↦ -deriv V (u p)) isOpen_Ioo hK hu
      ((hV.continuous_deriv_one.comp_continuousOn hu.continuousOn).neg)
      hs (fun t ht x hx ↦ by rw [hs t ht x hx, hV0, neg_zero])
      (fun t ht ψ hψ hψs ↦ by
        simpa only [neg_mul, integral_neg, sub_eq_add_neg] using hw t ht ψ hψ hψs)
      ((φ i).contDiff_normed (μ := volume))
      ((φ i).hasCompactSupport_normed (μ := volume))).mono hsub
  have hlim : TendstoLocallyUniformlyOn U v atTop S :=
    ((ContDiffBump.tendstoLocallyUniformlyOn_convolution_parameter
      (μ := volume) hu.continuousOn hφ).comp e (mapsTo_preimage e _)
        e.continuous.continuousOn).mono hsub
  have hD (j : Fin (n + 1)) :
      TendstoLocallyUniformlyOn (fun i ↦ ∂[j] (U i)) (∂[j] v) atTop S :=
    (ContDiffBump.tendstoLocallyUniformlyOn_partialDeriv_convolution_timeSpace
      isOpen_Ioo hK hu hs hφ j).mono hsub
  have hR : TendstoLocallyUniformlyOn
      (fun i ↦ semilinearWaveEnergyBalanceResidual V (U i)) (fun _ ↦ 0) atTop S :=
    (tendstoLocallyUniformlyOn_convolution_energyBalanceResidual
      isOpen_Ioo hK hu hs hV hV0 hw hφ).mono hsub
  exact ballIntegral_energy_add_truncatedCone_flux_of_approximation
    hV hv hreg hlim hD hR c has hsτ hτb hτT

end WaveEquation
