/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SobolevSemigroup
public import PDE.Analysis.Fourier.UnitaryNormalization
public import PDE.Spaces.Sobolev.Calculus.Pullback.Dilation.HigherOrder

/-!
# Spatial dilation and heat evolution

Fourier change of variables gives the parabolic covariance of the actual L²
heat operator. The physical base map transfers this identity to every integer
weak-derivative graph space.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Fractional PDE.Analysis.Fourier
open scoped ENNReal NNReal Sobolev

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- Elapsed heat time after spatial rescaling. -/
def parabolicHeatTime (a : ℝ) (t : ℝ≥0) : ℝ≥0 :=
  ⟨a ^ 2 * (t : ℝ), by positivity⟩

@[simp]
theorem coe_parabolicHeatTime (a : ℝ) (t : ℝ≥0) :
    (parabolicHeatTime a t : ℝ) = a ^ 2 * (t : ℝ) := rfl

/-- The Gaussian symbol has the exact parabolic scaling law. -/
theorem heatSymbol_dilation (a : ℝ) (ha : a ≠ 0) (t : ℝ≥0) (ξ : ℝ^n) :
    heatSymbol n (parabolicHeatTime a t) (a⁻¹ • ξ) = heatSymbol n t ξ := by
  unfold heatSymbol
  rw [coe_parabolicHeatTime]
  congr 2
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
  field_simp

/-- Heat and scalar dilation commute with the exact rescaling of elapsed time. -/
theorem heatL2_compSMul (a : ℝ) (ha : a ≠ 0) (t : ℝ≥0)
    (u : Lp ℂ 2 (volume : Measure (ℝ^n))) :
    heatL2 n t (Lp.compSMul volume 2 a ha u) =
      Lp.compSMul volume 2 a ha (heatL2 n (parabolicHeatTime a t) u) := by
  let q : ℝ≥0 := parabolicHeatTime a t
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (heatL2 n t (Lp.compSMul volume 2 a ha u)) =
    𝓕 (Lp.compSMul volume 2 a ha (heatL2 n q u))
  rw [fourier_heatL2, fourier_compSMul, fourier_compSMul, fourier_heatL2]
  apply Lp.ext
  have hqAE : ⇑(heatSymbolLinf n q) =ᵐ[volume] heatSymbol n q :=
    (memLp_top_heatSymbol (n := n) q).coeFn_toLp
  have htAE : ⇑(heatSymbolLinf n t) =ᵐ[volume] heatSymbol n t :=
    (memLp_top_heatSymbol (n := n) t).coeFn_toLp
  have hmul := (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero ha)).ae_eq_comp
    (Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n q) (𝓕 u))
  have hq := (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero ha)).ae_eq_comp hqAE
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (heatSymbolLinf n t)
      (|(a ^ Module.finrank ℝ (ℝ^n))⁻¹| •
        Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha) (𝓕 u)),
    Lp.coeFn_smul |(a ^ Module.finrank ℝ (ℝ^n))⁻¹|
      (Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha) (𝓕 u)),
    Lp.coeFn_smul |(a ^ Module.finrank ℝ (ℝ^n))⁻¹|
      (Lp.compSMul volume 2 a⁻¹ (inv_ne_zero ha) (heatSymbolLinf n q • 𝓕 u)),
    Lp.coeFn_compSMul volume 2 a⁻¹ (inv_ne_zero ha) (𝓕 u),
    Lp.coeFn_compSMul volume 2 a⁻¹ (inv_ne_zero ha) (heatSymbolLinf n q • 𝓕 u),
    hmul, hq, htAE] with ξ hleft hscalar hright hd hdq hm hq ht
  rw [hleft, hright]
  simp only [Pi.smul_apply', smul_eq_mul]
  rw [hscalar]
  simp only [Pi.smul_apply, Complex.real_smul]
  rw [hd, hdq, ht]
  simp only [Function.comp_apply, smul_eq_mul, Pi.mul_apply] at hm hq
  rw [hm, hq, show heatSymbol n q (a⁻¹ • ξ) = heatSymbol n t ξ from
    heatSymbol_dilation a ha t ξ]
  ring

/-- Complexification of the physical Sobolev base respects scalar dilation. -/
theorem baseL2_dilationWkpCLM (a : ℝ) (ha : a ≠ 0) (u : W^{k,2}(ℝ^n)) :
    baseL2 (dilationWkpCLM (by norm_num) a ha u) =
      Lp.compSMul volume 2 a ha (baseL2 u) := by
  apply Lp.ext
  have hbase := dilationWkpCLM_base_ae (by norm_num : (2 : ℝ≥0∞) ≠ ∞) a ha u
  simp only [domainMeasure, Measure.restrict_univ] at hbase
  have hcomp := (Measure.quasiMeasurePreserving_smul volume ha).ae_eq_comp
    (complexifyL2CLM_ae (wkpBaseCoordinateCLM u))
  rw [← complexifyL2CLM_base, ← complexifyL2CLM_base]
  filter_upwards [complexifyL2CLM_ae (wkpBaseCoordinateCLM
      (dilationWkpCLM (by norm_num) a ha u)),
    Lp.coeFn_compSMul volume 2 a ha (complexifyL2CLM n (wkpBaseCoordinateCLM u)),
    hbase, hcomp] with x hleft hright hbase hcomp
  have hbase' : wkpBaseCoordinateCLM
      (dilationWkpCLM (by norm_num : (2 : ℝ≥0∞) ≠ ∞) a ha u) x =
      wkpBaseCoordinateCLM u (a • x) := by
    simpa only [baseRepresentative, wkpBaseCoordinateCLM_apply] using hbase
  exact hleft.trans ((congrArg Complex.ofReal hbase').trans
    (hcomp.symm.trans hright.symm))

/-- The physical complexified base map respects real scalar multiplication. -/
theorem baseL2_smul (a : ℝ) (u : W^{k,2}(ℝ^n)) : baseL2 (a • u) = a • baseL2 u := by
  rw [← complexifyL2CLM_base, map_smul, map_smul, complexifyL2CLM_base]

/-- Parabolic covariance on the actual integer Sobolev graph space. -/
theorem heatSobolev_dilationWkpCLM (a : ℝ) (ha : a ≠ 0) (t : ℝ≥0)
    (u : W^{k,2}(ℝ^n)) :
    heatSobolev n k t (dilationWkpCLM (by norm_num) a ha u) =
      dilationWkpCLM (by norm_num) a ha (heatSobolev n k (parabolicHeatTime a t) u) := by
  apply baseL2_injective
  rw [baseL2_heatSobolev, baseL2_dilationWkpCLM, baseL2_dilationWkpCLM,
    baseL2_heatSobolev, heatL2_compSMul]

end HeatEquation.WholeSpace
