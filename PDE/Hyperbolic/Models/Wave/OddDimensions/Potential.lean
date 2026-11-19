/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.OddDimensions.Regularity

/-!
# Odd-dimensional wave potentials

The weighted spherical profile, written in canonical spacetime
coordinates, solves the wave equation with zero displacement. Its initial
velocity is `(2k+1)‼` times the original datum. The Euler–Poisson–Darboux
identity and parameter commutation prove the equation from `C^(k+2)` data.
-/

@[expose] public noncomputable section

open PDE (laplacian time)

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The weighted spherical profile in canonical spacetime coordinates. -/
def oddWavePotential (k : ℕ) (f : ℝ^(2 * k + 3) → ℝ) : ℝ^(2 * k + 3 + 1) → ℝ :=
  spaceTimeUncurry (oddSphericalProfile k f)

/-- Evaluation in space and time recovers the original radial profile. -/
@[simp]
theorem oddWavePotential_timeSpaceCons (k : ℕ) (f : ℝ^(2 * k + 3) → ℝ) (x : ℝ^(2 * k + 3)) (t : ℝ) :
    oddWavePotential k f (timeSpaceCons t x) = oddSphericalProfile k f x t := by
  simp [oddWavePotential, spaceTimeUncurry, time]

/-- The potential loses at most `k` derivatives from the spatial data. -/
theorem contDiff_oddWavePotential (k s : ℕ) {f : ℝ^(2 * k + 3) → ℝ} (hf : ContDiff ℝ (k + s) f) :
    ContDiff ℝ s (oddWavePotential k f) :=
  (contDiff_spaceTimeUncurry_iff _).mpr (contDiff_oddSphericalProfile k s hf)

/-- The potential vanishes on the initial slice by signed-radius oddness. -/
theorem oddWavePotential_initial (k : ℕ) (f : ℝ^(2 * k + 3) → ℝ) (x : ℝ^(2 * k + 3)) :
    oddWavePotential k f (timeSpaceCons 0 x) = 0 := by
  rw [oddWavePotential_timeSpaceCons]
  exact (oddSphericalProfile_odd k f x).map_zero

/-- A time-coordinate derivative is the ordinary derivative of the original
radial profile. -/
theorem partialDeriv_oddWavePotential_time (k : ℕ) {f : ℝ^(2 * k + 3) → ℝ}
    (hf : ContDiff ℝ (k + 1) f) (x : ℝ^(2 * k + 3)) (t : ℝ) :
    (∂[0] (oddWavePotential k f)) (timeSpaceCons t x) = deriv (oddSphericalProfile k f x) t := by
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ _ _
    ((contDiff_oddWavePotential k 1 hf).differentiable one_ne_zero _)]
  simp only [oddWavePotential_timeSpaceCons]

/-- The initial velocity of the unnormalized potential is `(2k+1)‼ f`. -/
theorem partialDeriv_oddWavePotential_initial (k : ℕ) {f : ℝ^(2 * k + 3) → ℝ}
    (hf : ContDiff ℝ (k + 1) f) (x : ℝ^(2 * k + 3)) :
    (∂[0] (oddWavePotential k f)) (timeSpaceCons 0 x) =
      (Nat.doubleFactorial (2 * k + 1) : ℝ) * f x := by
  rw [partialDeriv_oddWavePotential_time k hf]
  exact deriv_oddSphericalProfile_zero k f x
    ((contDiff_unitSphereAverage hf).comp (contDiff_const.prodMk contDiff_id))

/-- Oddness forces zero initial acceleration at the `C²` regularity budget. -/
theorem secondPartialDeriv_oddWavePotential_initial (k : ℕ) {f : ℝ^(2 * k + 3) → ℝ}
    (hf : ContDiff ℝ (k + 2) f) (x : ℝ^(2 * k + 3)) :
    (∂[0] (∂[0] (oddWavePotential k f))) (timeSpaceCons 0 x) = 0 := by
  rw [secondPartialDeriv_timeSpaceCons (contDiff_oddWavePotential k 2 hf)]
  simp only [oddWavePotential_timeSpaceCons]
  exact (odd_deriv_of_even (even_deriv_of_odd (oddSphericalProfile_odd k f x))).map_zero

/-- The second time derivative equals the transformed spatial Laplacian,
by the finite-order weighted EPD identity. -/
theorem secondDeriv_oddSphericalProfile (k : ℕ) {f : ℝ^(2 * k + 3) → ℝ} (hf : ContDiff ℝ (k + 2) f)
    (x : ℝ^(2 * k + 3)) {t : ℝ} (ht : 0 < t) :
    deriv (deriv (oddSphericalProfile k f x)) t = oddSphericalProfile k (laplacian f) x t := by
  have : Fact (0 < 2 * k + 3) := ⟨by omega⟩
  apply oddRadialTransform_eulerPoissonDarboux k
    ((contDiff_unitSphereAverage hf).comp (contDiff_const.prodMk contDiff_id)) (r := t) _ ht
  intro r hr
  simpa only [show 2 * k + 3 - 1 = 2 * k + 2 by omega, Function.comp_def, id_eq] using
    radialLaplacian_unitSphereAverage f x hr (hf.of_le (by norm_cast; omega))

/-- The raw-data potential solves the wave equation at every positive time. -/
theorem waveOperator_oddWavePotential (k : ℕ) {f : ℝ^(2 * k + 3) → ℝ} (hf : ContDiff ℝ (k + 2) f)
    {p : ℝ^(2 * k + 3 + 1)} (hp : 0 < p 0) :
    waveOperator (oddWavePotential k f) p = 0 := by
  have he := waveOperator_timeSpaceCons (contDiff_oddWavePotential k 2 hf)
    (spatialPartCLM (2 * k + 3) p) (p 0)
  rw [timeSpaceCons_spatialPartCLM] at he
  rw [he]
  simp only [oddWavePotential_timeSpaceCons]
  rw [secondDeriv_oddSphericalProfile k hf _ hp, laplacian_oddSphericalProfile k hf, sub_self]

end WaveEquation
