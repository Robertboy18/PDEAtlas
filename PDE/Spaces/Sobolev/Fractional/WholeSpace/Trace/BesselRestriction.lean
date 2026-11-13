/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.BesselLifting

/-!
# Bounded normal restriction in Bessel coordinates

The normal integral is conjugated by Bessel and Fourier isometries. Its norm is
at most one, and the isometric Bessel lifting is a right inverse. Multiplication
by `sqrt π` gives the physical boundary normalization; physical agreement is
proved separately using the Fourier slice identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform BesselPotentialSpace
open scoped ENNReal BesselPotentialSpace

namespace SobolevSpace.Fractional.Trace

open SobolevSpace.Trace.HalfSpace

/-- Pull ambient Euclidean frequency coordinates into tangential-normal coordinates. -/
def splitFrequencyLI (n : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ^(n + 1)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (ℝ^n × ℝ)) :=
  Lp.compMeasurePreservingₗᵢ ℂ tangentialNormalMeasurableEquiv.symm
    measurePreserving_tangentialNormalMeasurableEquiv.symm

/-- Almost-everywhere formula for splitting frequency coordinates. -/
theorem splitFrequencyLI_apply_ae (n : ℕ)
    (u : Lp ℂ 2 (volume : Measure ℝ^(n + 1))) :
    splitFrequencyLI n u =ᵐ[volume] fun p ↦ u (joinTangentialNormal p) := by
  simpa [splitFrequencyLI, Lp.compMeasurePreservingₗᵢ, Lp.compMeasurePreservingₗ,
    Function.comp_def] using
    Lp.coeFn_compMeasurePreserving u measurePreserving_tangentialNormalMeasurableEquiv.symm

/-- Splitting the Euclidean lifting recovers the product-coordinate lifting. -/
theorem splitFrequencyLI_normalLiftEuclideanLI (n : ℕ)
    (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    splitFrequencyLI n (normalLiftEuclideanLI n v) = normalLift v := by
  apply Lp.ext
  have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).symm
  filter_upwards [splitFrequencyLI_apply_ae n (normalLiftEuclideanLI n v),
    hm.quasiMeasurePreserving.ae (normalLiftEuclideanLI_apply_ae n v),
    normalLift_apply_ae v] with p h1 h2 h3
  simp only [tangentialNormalMeasurableEquiv_symm_apply, split_joinTangentialNormal] at h2
  rw [h1, h2, h3]

/-- Contractive restriction between complex Bessel spaces in normalized Fourier coordinates. -/
def besselNormalRestrictionCLM (n : ℕ) :
    H^{(1 : ℝ)}(ℝ^(n + 1)) →L[ℂ] H^{(1 / 2 : ℝ)}(ℝ^n) :=
  (toLpₗᵢ (ℝ^n) ℂ (1 / 2) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    normalRestriction n ∘L (splitFrequencyLI n).toContinuousLinearMap ∘L
    (Lp.fourierTransformₗᵢ (ℝ^(n + 1)) ℂ).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (toLpₗᵢ (ℝ^(n + 1)) ℂ 1 2).toContinuousLinearEquiv.toContinuousLinearMap

/-- Weighted Fourier coordinates of the bounded restriction. -/
theorem fourier_toLp_besselNormalRestrictionCLM (n : ℕ) (u : H^{(1 : ℝ)}(ℝ^(n + 1))) :
    𝓕 (toLp (besselNormalRestrictionCLM n u)) =
      normalRestriction n (splitFrequencyLI n (𝓕 (toLp u))) := by
  simp only [besselNormalRestrictionCLM, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  rw [← toLpₗᵢ_apply, LinearIsometryEquiv.apply_symm_apply, toLpₗᵢ_apply]
  exact (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).apply_symm_apply _

/-- The normalized Bessel restriction estimate, with no dimension-dependent constant. -/
theorem norm_besselNormalRestrictionCLM_apply_le (n : ℕ)
    (u : H^{(1 : ℝ)}(ℝ^(n + 1))) :
    ‖besselNormalRestrictionCLM n u‖ ≤ ‖u‖ := by
  rw [← norm_fourier_toLp_eq, fourier_toLp_besselNormalRestrictionCLM]
  calc
    _ ≤ ‖splitFrequencyLI n (𝓕 (toLp u))‖ := norm_normalRestriction_apply_le n _
    _ = ‖u‖ := by rw [LinearIsometry.norm_map, norm_fourier_toLp_eq]

/-- Restriction of the constructed Bessel lifting is the original boundary element. -/
theorem besselNormalRestrictionCLM_besselNormalLiftLI (n : ℕ)
    (v : H^{(1 / 2 : ℝ)}(ℝ^n)) :
    besselNormalRestrictionCLM n (besselNormalLiftLI n v) = v := by
  apply injective_toLp (ℝ^n) ℂ (1 / 2) 2
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (toLp (besselNormalRestrictionCLM n (besselNormalLiftLI n v))) = 𝓕 (toLp v)
  rw [fourier_toLp_besselNormalRestrictionCLM, fourier_toLp_besselNormalLiftLI,
    splitFrequencyLI_normalLiftEuclideanLI, normalRestriction_normalLift]

end SobolevSpace.Fractional.Trace
