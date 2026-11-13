/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.Operator
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.SchwartzBoundary
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.FourierWeight

/-!
# Agreement of the bounded trace with classical Schwartz restriction

The normal-frequency operator has the same weighted Fourier representative as
classical boundary restriction. The proof combines Fubini, the explicit kernel
cancellation, and the Schwartz Fourier slice identity. Thus the two operators
agree on physical functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform BesselPotentialSpace
open scoped ENNReal BesselPotentialSpace SchwartzMap

namespace SobolevSpace.Fractional.Trace

open SobolevSpace.Trace.HalfSpace

private theorem fourier_toLp_schwartz_ae {n : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (f : 𝓢(ℝ^n, ℂ)) :
    (𝓕 (toLp (SchwartzMap.memSobolev (p := 2) (s := s) f).toBesselPotentialSpace) :
      Lp ℂ 2 (volume : Measure ℝ^n)) =ᵐ[volume]
        fun ξ ↦ besselSymbol n s ξ * (𝓕 f : 𝓢(ℝ^n, ℂ)) ξ := by
  have h := coeFn_fourier_toLp hs
    (SchwartzMap.memSobolev (p := 2) (s := s) f).toBesselPotentialSpace
  rw [toL2Fun_ofSchwartz, SchwartzMap.toLp_fourier_eq] at h
  filter_upwards [h, (𝓕 f : 𝓢(ℝ^n, ℂ)).coeFn_toLp 2] with ξ h1 h2
  rw [h1, h2]

/-- The bounded Bessel trace returns the Schwartz boundary value. -/
theorem wholeSpaceTraceCLM_ofSchwartz {n : ℕ} (f : 𝓢(ℝ^(n + 1), ℂ)) :
    wholeSpaceTraceCLM n (SchwartzMap.memSobolev (p := 2) (s := 1) f).toBesselPotentialSpace =
      (SchwartzMap.memSobolev (p := 2) (s := (1 / 2 : ℝ))
        (schwartzBoundaryCLM n f)).toBesselPotentialSpace := by
  let u := (SchwartzMap.memSobolev (p := 2) (s := (1 : ℝ)) f).toBesselPotentialSpace
  let A := splitFrequencyLI n (𝓕 (toLp u))
  have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).symm
  have hA : ∀ᵐ p ∂((volume : Measure ℝ^n).prod (volume : Measure ℝ)),
      A p = besselSymbol (n + 1) 1 (joinTangentialNormal p) *
        (𝓕 f : 𝓢(ℝ^(n + 1), ℂ)) (joinTangentialNormal p) := by
    rw [← Measure.volume_eq_prod]
    have hsplit := splitFrequencyLI_apply_ae n (𝓕 (toLp u))
    have hinput := hm.quasiMeasurePreserving.ae (fourier_toLp_schwartz_ae zero_le_one f)
    filter_upwards [hsplit, hinput] with p h1 h2
    simp only [tangentialNormalMeasurableEquiv_symm_apply] at h2
    exact h1.trans h2
  apply injective_toLp (ℝ^n) ℂ (1 / 2) 2
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (toLp (wholeSpaceTraceCLM n u)) = _
  rw [fourier_toLp_wholeSpaceTraceCLM]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (Real.sqrt Real.pi : ℂ) (normalRestriction n A),
    normalRestriction_apply_ae A, Measure.ae_ae_of_ae_prod hA,
    fourier_toLp_schwartz_ae (by positivity : 0 ≤ (1 / 2 : ℝ))
      (schwartzBoundaryCLM n f)] with ξ h1 h2 h3 h4
  rw [h1]
  simp only [Pi.smul_apply]
  rw [h2]
  apply Eq.trans ?_ h4.symm
  change (Real.sqrt Real.pi : ℂ) •
    (∫ t : ℝ, normalKernel (tangentialScale ξ) t • A (ξ, t)) = _
  rw [← integral_smul, fourier_schwartzBoundary_eq_normal, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [h3] with t ht
  rw [ht]
  exact normalKernel_smul_besselSymbol ξ t _

/-- Physical `L²` agreement of the constructed trace and classical Schwartz restriction. -/
theorem toL2Fun_wholeSpaceTraceCLM_ofSchwartz {n : ℕ} (f : 𝓢(ℝ^(n + 1), ℂ)) :
    toL2Fun (by positivity : 0 ≤ (1 / 2 : ℝ))
      (wholeSpaceTraceCLM n (SchwartzMap.memSobolev (p := 2) (s := 1) f).toBesselPotentialSpace) =
        (schwartzBoundaryCLM n f).toLp 2 := by
  rw [wholeSpaceTraceCLM_ofSchwartz, toL2Fun_ofSchwartz]

/-- The fractional norm of the physical Schwartz boundary is controlled by the ambient `H¹` norm. -/
theorem norm_schwartzBoundary_bessel_le {n : ℕ} (f : 𝓢(ℝ^(n + 1), ℂ)) :
    ‖(SchwartzMap.memSobolev (p := 2) (s := (1 / 2 : ℝ))
      (schwartzBoundaryCLM n f)).toBesselPotentialSpace‖ ≤
        Real.sqrt Real.pi *
          ‖(SchwartzMap.memSobolev (p := 2) (s := (1 : ℝ)) f).toBesselPotentialSpace‖ := by
  rw [← wholeSpaceTraceCLM_ofSchwartz]
  exact norm_wholeSpaceTraceCLM_apply_le n _

end SobolevSpace.Fractional.Trace
