/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Regularization.Approximation
public import PDE.Hyperbolic.Models.Wave.Regularization.Regularity
public import PDE.Hyperbolic.Models.Wave.Regularization.Residual
public import PDE.Hyperbolic.NonlinearWave.EnergyIdentity
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime

/-!
# Vanishing energy defects under spatial smoothing

A C¹ tested wave becomes C² after spatial convolution. The nonlinear residual
converges locally uniformly to zero, while the time derivative converges to
that of the original field. Their product is the classical energy defect.
This gives the vanishing error needed to pass finite-cone energy identities
to the original C¹ solution, without assuming its second derivatives exist.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE PDE.Common
open scoped Topology Convolution

namespace WaveEquation

/-- The local energy defect of a spatially smoothed tested wave tends locally
uniformly to zero. Only C¹ regularity of the original field is required. -/
theorem tendstoLocallyUniformlyOn_convolution_energyBalanceResidual {n : ℕ} {u : ℝ × ℝ^n → ℝ}
    {I : Set ℝ} {K : Set (ℝ^n)} {V : ℝ → ℝ} (hI : IsOpen I) (hK : IsCompact K)
    (hu : ContDiffOn ℝ 1 u (I ×ˢ univ)) (hs : ∀ t ∈ I, ∀ x ∉ K, u (t, x) = 0) (hV : ContDiff ℝ 1 V)
    (hV0 : deriv V 0 = 0)
    (hw : ∀ t ∈ I, ∀ ψ : ℝ^n → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      HasDerivAt (deriv (fun s ↦ ∫ y, u (s, y) * ψ y))
      ((∫ y, u (t, y) * PDE.laplacian ψ y) - ∫ y, deriv V (u (t, y)) * ψ y) t)
    {ι : Type*} {φ : ι → ContDiffBump (0 : ℝ^n)} {l : Filter ι}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) :
    let e := timeSpaceContinuousLinearEquiv n
    let U := fun i (p : ℝ^(n + 1)) ↦
      ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        (fun y ↦ u ((e p).1, y))) (e p).2
    TendstoLocallyUniformlyOn (fun i ↦ semilinearWaveEnergyBalanceResidual V (U i))
      (fun _ ↦ 0) l (spaceTimeCylinder univ I) := by
  let e := timeSpaceContinuousLinearEquiv n
  let A := fun i (p : ℝ × ℝ^n) ↦ ((φ i).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
      (fun y ↦ u (p.1, y))) p.2
  let U := fun i (p : ℝ^(n + 1)) ↦ A i (e p)
  let S := spaceTimeCylinder (univ : Set (ℝ^n)) I
  have hS : IsOpen S := isOpen_spaceTimeCylinder isOpen_univ hI
  have hround (t : ℝ) (x : ℝ^n) : e (timeSpaceCons t x) = (t, x) := by
    simp only [e, timeSpaceContinuousLinearEquiv_apply, time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons]
  have hreg (i : ι) : ContDiffOn ℝ 2 (U i) S := contDiffOn_two_convolution_timeSpace_of_tested_wave
      (F := fun p ↦ -deriv V (u p)) hI hK hu
      ((hV.continuous_deriv_one.comp_continuousOn hu.continuousOn).neg)
      hs (fun t ht x hx ↦ by rw [hs t ht x hx, hV0, neg_zero])
      (fun t ht ψ hψ hψs ↦ by
        simpa only [neg_mul, integral_neg, sub_eq_add_neg] using hw t ht ψ hψ hψs)
      ((φ i).contDiff_normed (μ := volume)) ((φ i).hasCompactSupport_normed (μ := volume))
  have hd := ContDiffBump.tendstoLocallyUniformlyOn_partialDeriv_convolution_timeSpace
    hI hK hu hs hφ 0
  have hr := (tendstoLocallyUniformlyOn_convolution_wave_residual hu.continuousOn
    hV.continuous_deriv_one hw hφ).comp e (mapsTo_preimage e _) e.continuous.continuousOn
  have hc : Continuous (fun q : ℝ × ℝ ↦ q.1 * q.2) := continuous_fst.mul continuous_snd
  have huc : ContDiffOn ℝ 1 (fun p ↦ u (e p)) S :=
    hu.comp_continuousLinearMap e.toContinuousLinearMap
  have hmul := hc.comp_tendstoLocallyUniformlyOn (hd.prodMk hr)
    ((huc.continuousOn_partialDeriv 0 hS).prodMk continuousOn_const)
  simp only [Function.comp_apply, mul_zero] at hmul
  refine hmul.congr ?_
  intro i p hp
  have hpoint : timeSpaceCons (e p).1 (e p).2 = p := e.symm_apply_apply p
  have hup : ContDiffAt ℝ 2 (U i) (timeSpaceCons (e p).1 (e p).2) := by
    rw [hpoint]
    exact (hreg i).contDiffAt (hS.mem_nhds hp)
  have hop : semilinearWaveOperator V (U i) p = deriv (deriv (fun s ↦ A i (s, (e p).2))) (e p).1 -
        PDE.laplacian (fun y ↦ A i ((e p).1, y)) (e p).2 + deriv V (A i (e p)) := by
    conv_lhs => rw [← hpoint]
    rw [semilinearWaveOperator, waveOperator_timeSpaceCons_of_contDiffAt hup]
    simp only [U, hround]
  change (∂[0] (U i)) p * _ = semilinearWaveEnergyBalanceResidual V (U i) p
  rw [semilinearWaveEnergyBalanceResidual_eq_mul_operator hV
    ((hreg i).contDiffAt (hS.mem_nhds hp)), hop]

end WaveEquation
