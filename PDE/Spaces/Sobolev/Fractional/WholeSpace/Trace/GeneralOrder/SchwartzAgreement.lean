/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.Real
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.KernelWeight
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.SchwartzBoundary
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.FourierWeight

/-!
# Physical Schwartz agreement for general-order trace

The exact weight cancellation and the Fourier slice identity show
that the constructed trace is restriction to the last-coordinate hyperplane.
The result holds in the Bessel spaces and on physical `L²`
representatives, both complex and real.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform BesselPotentialSpace
open scoped ENNReal BesselPotentialSpace SchwartzMap

namespace SobolevSpace.Fractional.Trace.GeneralOrder

open SobolevSpace.Trace.HalfSpace

/-- The general-order trace returns the Schwartz boundary value. -/
theorem wholeSpaceTraceCLM_ofSchwartz {n : ℕ} {s : ℝ} (hs : 1 / 2 < s)
    (f : 𝓢(ℝ^(n + 1), ℂ)) :
    wholeSpaceTraceCLM n hs (SchwartzMap.memSobolev (p := 2) (s := s) f).toBesselPotentialSpace =
      (SchwartzMap.memSobolev (p := 2) (s := s - 1 / 2)
        (schwartzBoundaryCLM n f)).toBesselPotentialSpace := by
  have hschwartz {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (g : 𝓢(ℝ^d, ℂ)) :
      (𝓕 (toLp (SchwartzMap.memSobolev (p := 2) (s := r) g).toBesselPotentialSpace) :
        Lp ℂ 2 (volume : Measure ℝ^d)) =ᵐ[volume]
          fun ξ ↦ besselSymbol d r ξ * (𝓕 g : 𝓢(ℝ^d, ℂ)) ξ := by
    have h := coeFn_fourier_toLp hr
      (SchwartzMap.memSobolev (p := 2) (s := r) g).toBesselPotentialSpace
    rw [toL2Fun_ofSchwartz, SchwartzMap.toLp_fourier_eq] at h
    filter_upwards [h, (𝓕 g : 𝓢(ℝ^d, ℂ)).coeFn_toLp 2] with ξ h1 h2
    rw [h1, h2]
  let u := (SchwartzMap.memSobolev (p := 2) (s := s) f).toBesselPotentialSpace
  let A := splitFrequencyLI n (𝓕 (toLp u))
  have hm := (measurePreserving_tangentialNormalMeasurableEquiv (n := n)).symm
  have hA : ∀ᵐ p ∂((volume : Measure ℝ^n).prod (volume : Measure ℝ)),
      A p = besselSymbol (n + 1) s (joinTangentialNormal p) *
        (𝓕 f : 𝓢(ℝ^(n + 1), ℂ)) (joinTangentialNormal p) := by
    rw [← Measure.volume_eq_prod]
    have hsplit := splitFrequencyLI_apply_ae n (𝓕 (toLp u))
    have hinput := hm.quasiMeasurePreserving.ae (hschwartz (by linarith) f)
    filter_upwards [hsplit, hinput] with p h1 h2
    simp only [tangentialNormalMeasurableEquiv_symm_apply] at h2
    exact h1.trans h2
  apply injective_toLp (ℝ^n) ℂ (s - 1 / 2) 2
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (toLp (wholeSpaceTraceCLM n hs u)) = _
  rw [fourier_toLp_wholeSpaceTraceCLM]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (traceConstant s : ℂ) (frequencyRestriction n hs A),
    frequencyRestriction_apply_ae hs A, Measure.ae_ae_of_ae_prod hA,
    hschwartz (by linarith : 0 ≤ s - 1 / 2) (schwartzBoundaryCLM n f)]
    with ξ h1 h2 h3 h4
  rw [h1]
  simp only [Pi.smul_apply]
  rw [h2]
  apply Eq.trans ?_ h4.symm
  change (traceConstant s : ℂ) •
    (∫ t : ℝ, frequencyKernel s ξ t • A (ξ, t)) = _
  rw [← integral_smul, fourier_schwartzBoundary_eq_normal, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [h3] with t ht
  rw [ht]
  exact frequencyKernel_smul_besselSymbol hs ξ t _

/-- Physical `L²` agreement with classical Schwartz restriction at every admissible order. -/
theorem toL2Fun_wholeSpaceTraceCLM_ofSchwartz {n : ℕ} {s : ℝ} (hs : 1 / 2 < s)
    (f : 𝓢(ℝ^(n + 1), ℂ)) :
    toL2Fun (by linarith : 0 ≤ s - 1 / 2)
      (wholeSpaceTraceCLM n hs (SchwartzMap.memSobolev (p := 2) (s := s)
        f).toBesselPotentialSpace) = (schwartzBoundaryCLM n f).toLp 2 := by
  rw [wholeSpaceTraceCLM_ofSchwartz, toL2Fun_ofSchwartz]

theorem norm_schwartzBoundary_bessel_le {n : ℕ} {s : ℝ} (hs : 1 / 2 < s)
    (f : 𝓢(ℝ^(n + 1), ℂ)) :
    ‖(SchwartzMap.memSobolev (p := 2) (s := s - 1 / 2)
      (schwartzBoundaryCLM n f)).toBesselPotentialSpace‖ ≤
        traceConstant s *
          ‖(SchwartzMap.memSobolev (p := 2) (s := s) f).toBesselPotentialSpace‖ := by
  rw [← wholeSpaceTraceCLM_ofSchwartz hs]
  exact norm_wholeSpaceTraceCLM_apply_le n hs _

/-- A real Sobolev element represented by a Schwartz function has its classical boundary values. -/
theorem toL2FunCLM_wholeSpaceTraceRealCLM_ofSchwartz {n : ℕ} {s : ℝ}
    (hs : 1 / 2 < s) (u : HsSpaceReal (n + 1) s) (f : 𝓢(ℝ^(n + 1), ℂ))
    (hu : toL2Fun (by linarith : 0 ≤ s) u.val = f.toLp 2) :
    HsSpaceReal.toL2FunCLM n (by linarith : 0 ≤ s - 1 / 2)
      (wholeSpaceTraceRealCLM n hs u) =ᵐ[volume]
        fun y ↦ (f (joinTangentialNormal (y, 0))).re := by
  have hu' : u.val =
      (SchwartzMap.memSobolev (p := 2) (s := s) f).toBesselPotentialSpace := by
    apply toL2Fun_injective (by linarith : 0 ≤ s)
    rw [hu, toL2Fun_ofSchwartz]
  have hphysical : toL2Fun (by linarith : 0 ≤ s - 1 / 2)
      (wholeSpaceTraceRealCLM n hs u).val = (schwartzBoundaryCLM n f).toLp 2 := by
    change toL2Fun _ (wholeSpaceTraceCLM n hs u.val) = _
    rw [hu', toL2Fun_wholeSpaceTraceCLM_ofSchwartz hs]
  filter_upwards [HsSpaceReal.toL2FunCLM_apply_ae (by linarith : 0 ≤ s - 1 / 2)
    (wholeSpaceTraceRealCLM n hs u), (schwartzBoundaryCLM n f).coeFn_toLp 2]
    with y h1 h2
  rw [h1, hphysical, h2, schwartzBoundaryCLM_apply]

end SobolevSpace.Fractional.Trace.GeneralOrder
