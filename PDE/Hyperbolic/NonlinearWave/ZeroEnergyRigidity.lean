/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
import Mathlib.Analysis.Calculus.MeanValue
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Bounds
import PDE.FDeriv.SpaceTime

/-!
# Zero-energy rigidity for semilinear waves

For a nonnegative potential, vanishing spatial energy forces the continuous
kinetic and spatial-gradient densities to vanish. Consequently, both the time
derivative and spatial gradient vanish pointwise on that time slice.

Global energy conservation transports this rigidity from any reference time
to every spatial slice.

The spatial energy is `E(t) = ∫ ½ uₜ² + ½ |Dₓu|² + V(u) dx` with `V ≥ 0`, so each of its three
densities is nonnegative and continuous in `x`; a nonnegative continuous integrable function with
zero integral vanishes identically, which gives the pointwise conclusions. Conservation of energy
for the semilinear wave `uₜₜ - Δu + V'(u) = 0` is the mechanism that spreads a zero-energy slice
to all slices (Evans, §12.1.1, Theorem 1). The
`_of_referenceEnergy_eq_zero` theorems take `E(t) = E(t₀)` as a hypothesis.

## Main results

* `semilinearWaveTimeDerivative_eq_zero_of_spatialEnergy_eq_zero`,
  `semilinearWaveSpatialGradient_eq_zero_of_spatialEnergy_eq_zero`,
  `semilinearWavePotential_eq_zero_of_spatialEnergy_eq_zero`: on a slice with `E(t) = 0`, the
  time derivative, spatial gradient and potential density vanish pointwise.
* `semilinearWave_eq_zero_on_timeSlice_of_spatialEnergy_eq_zero`: if moreover `V` vanishes only
  at `0`, the field itself vanishes on the slice.
* `semilinearWave_fderiv_eq_zero_of_referenceEnergy_eq_zero`,
  `eq_const_of_semilinearWave_referenceEnergy_eq_zero`: under conserved zero energy the full
  spacetime derivative vanishes and the field is constant.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

private theorem continuous_eq_zero_of_nonneg_of_integral_eq_zero {f : ℝ^n → ℝ} (hf : Continuous f)
    (hfnonneg : 0 ≤ f) (hfintegrable : Integrable f) (hfintegral : ∫ x, f x = 0) :
    f = 0 := by
  apply (hf.ae_eq_iff_eq (volume : Measure (ℝ^n)) continuous_const).mp
  exact (integral_eq_zero_iff_of_nonneg hfnonneg hfintegrable).mp hfintegral

/-- If a nonnegative semilinear wave energy vanishes on a time slice, then
the time derivative of the field vanishes pointwise on that slice. -/
theorem semilinearWaveTimeDerivative_eq_zero_of_spatialEnergy_eq_zero (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t = 0) :
    ∀ x : ℝ^n, (∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  have hkineticIntegral : (∫ x : ℝ^n,
        semilinearWaveSpatialKineticEnergyDensity (n := n) u t x) = 0 := by
    apply le_antisymm
    · simpa only [henergy] using integral_semilinearWaveKineticEnergy_le_spatialEnergy
          (n := n) V hVnonneg hu t henergyIntegrable
    · exact integral_nonneg <| semilinearWaveSpatialKineticEnergyDensity_nonneg (n := n) u t
  have hkineticZero : semilinearWaveSpatialKineticEnergyDensity (n := n) u t = 0 :=
    continuous_eq_zero_of_nonneg_of_integral_eq_zero
      (continuous_semilinearWaveSpatialKineticEnergyDensity (n := n) hu t)
      (semilinearWaveSpatialKineticEnergyDensity_nonneg (n := n) u t)
      (integrable_semilinearWaveSpatialKineticEnergyDensity
        (n := n) V hVnonneg hu t henergyIntegrable) hkineticIntegral
  intro x
  have hx := congrFun hkineticZero x
  simp only [semilinearWaveSpatialKineticEnergyDensity, Pi.zero_apply] at hx
  nlinarith [sq_nonneg ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x))]

/-- If a nonnegative semilinear wave energy vanishes on a time slice, then
the spatial gradient of the field vanishes pointwise on that slice. -/
theorem semilinearWaveSpatialGradient_eq_zero_of_spatialEnergy_eq_zero (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t = 0) :
    ∀ x : ℝ^n, classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t x) =
      0 := by
  have hgradientIntegral : (∫ x : ℝ^n,
        semilinearWaveSpatialGradientEnergyDensity (n := n) u t x) = 0 := by
    apply le_antisymm
    · simpa only [henergy] using integral_semilinearWaveGradientEnergy_le_spatialEnergy
          (n := n) V hVnonneg hu t henergyIntegrable
    · exact integral_nonneg <| semilinearWaveSpatialGradientEnergyDensity_nonneg (n := n) u t
  have hgradientZero : semilinearWaveSpatialGradientEnergyDensity (n := n) u t = 0 :=
    continuous_eq_zero_of_nonneg_of_integral_eq_zero
      (continuous_semilinearWaveSpatialGradientEnergyDensity (n := n) hu t)
      (semilinearWaveSpatialGradientEnergyDensity_nonneg (n := n) u t)
      (integrable_semilinearWaveSpatialGradientEnergyDensity
        (n := n) V hVnonneg hu t henergyIntegrable) hgradientIntegral
  intro x
  have hx := congrFun hgradientZero x
  simp only [semilinearWaveSpatialGradientEnergyDensity, Pi.zero_apply] at hx
  apply norm_eq_zero.mp
  nlinarith [sq_nonneg ‖classicalWaveSpatialGradient (n := n) u
        (PDE.Common.timeSpaceCons (n := n) t x)‖]

/-- If a nonnegative semilinear wave energy vanishes on a time slice, then
the potential energy vanishes pointwise on that slice. -/
theorem semilinearWavePotential_eq_zero_of_spatialEnergy_eq_zero (V : ℝ → ℝ) (hV : Continuous V)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t = 0) :
    ∀ x : ℝ^n, V (u (PDE.Common.timeSpaceCons (n := n) t x)) = 0 := by
  have hpotentialIntegral : (∫ x : ℝ^n,
        semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t x) = 0 := by
    apply le_antisymm
    · simpa only [henergy] using integral_semilinearWavePotentialEnergy_le_spatialEnergy
          (n := n) V hV hVnonneg hu t henergyIntegrable
    · exact integral_nonneg <| semilinearWaveSpatialPotentialEnergyDensity_nonneg
          (n := n) V hVnonneg u t
  have hpotentialZero : semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t = 0 :=
    continuous_eq_zero_of_nonneg_of_integral_eq_zero
      (continuous_semilinearWaveSpatialPotentialEnergyDensity (n := n) hV hu t)
      (semilinearWaveSpatialPotentialEnergyDensity_nonneg (n := n) V hVnonneg u t)
      (integrable_semilinearWaveSpatialPotentialEnergyDensity
        (n := n) hV hVnonneg hu t henergyIntegrable) hpotentialIntegral
  intro x
  have hx := congrFun hpotentialZero x
  simpa only [semilinearWaveSpatialPotentialEnergyDensity, Pi.zero_apply] using hx

/-- If a nonnegative potential vanishes only at zero, then zero spatial
energy forces the field itself to vanish on the time slice. The potential need not be
continuous: the field is, so where it is nonzero the energy density is positive on an open set. -/
theorem semilinearWave_eq_zero_on_timeSlice_of_spatialEnergy_eq_zero (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) (hVzero : ∀ z, V z = 0 → z = 0) {u : ℝ^(n + 1) → ℝ}
    (hu : Continuous u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t = 0) :
    ∀ x : ℝ^n, u (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  have hle (x : ℝ^n) := semilinearWaveSpatialPotentialEnergyDensity_le_spatialEnergyDensity
    (n := n) V u t x
  have hf0 : 0 ≤ semilinearWaveSpatialEnergyDensity (n := n) V u t := fun x ↦
    (semilinearWaveSpatialPotentialEnergyDensity_nonneg (n := n) V hVnonneg u t x).trans (hle x)
  have hfae := (integral_eq_zero_iff_of_nonneg hf0 henergyIntegrable).mp henergy
  by_contra hne
  push Not at hne
  obtain ⟨x₀, hx₀⟩ := hne
  have hcont : Continuous fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x) :=
    hu.comp (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 0)).continuous
  have hsub : {x : ℝ^n | u (PDE.Common.timeSpaceCons (n := n) t x) ≠ 0} ⊆
      {x | ¬ semilinearWaveSpatialEnergyDensity (n := n) V u t x = (0 : ℝ^n → ℝ) x} :=
    fun x hx ↦ (lt_of_lt_of_le ((hVnonneg _).lt_of_ne fun h ↦ hx (hVzero _ h.symm))
      (hle x)).ne'
  exact ((isOpen_ne_fun hcont continuous_const).measure_pos volume ⟨x₀, hx₀⟩).ne'
    (measure_mono_null hsub (ae_iff.mp hfae))

/-- If conserved nonnegative energy vanishes at a reference time, the time
derivative of the field vanishes on every spatial slice. -/
theorem semilinearWaveTimeDerivative_eq_zero_of_referenceEnergy_eq_zero (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergyEq : semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (hreferenceEnergy : semilinearWaveSpatialEnergy (n := n) V u t₀ = 0) :
    ∀ x : ℝ^n, (∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  exact semilinearWaveTimeDerivative_eq_zero_of_spatialEnergy_eq_zero
    V hVnonneg hu t henergyIntegrable (henergyEq.trans hreferenceEnergy)

/-- If conserved nonnegative energy vanishes at a reference time, the spatial
gradient of the field vanishes on every spatial slice. -/
theorem semilinearWaveSpatialGradient_eq_zero_of_referenceEnergy_eq_zero (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergyEq : semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (hreferenceEnergy : semilinearWaveSpatialEnergy (n := n) V u t₀ = 0) :
    ∀ x : ℝ^n, classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t x) =
      0 := by
  exact semilinearWaveSpatialGradient_eq_zero_of_spatialEnergy_eq_zero
    V hVnonneg hu t henergyIntegrable (henergyEq.trans hreferenceEnergy)

/-- Vanishing conserved nonnegative energy forces the Fréchet derivative of
the spacetime field to vanish everywhere. -/
theorem semilinearWave_fderiv_eq_zero_of_referenceEnergy_eq_zero (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t₀ : ℝ)
    (henergyIntegrable : ∀ t, Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergyEq : ∀ t, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (hreferenceEnergy : semilinearWaveSpatialEnergy (n := n) V u t₀ = 0) (p : ℝ^(n + 1)) :
    fderiv ℝ u p = 0 := by
  have htime :
      (∂[0] u) p = 0 := by
    simpa only [PDE.Common.timeSpaceCons_spatialPart] using
      semilinearWaveTimeDerivative_eq_zero_of_referenceEnergy_eq_zero
        (n := n) V hVnonneg hu t₀ (p 0) (henergyIntegrable (p 0)) (henergyEq (p 0))
        hreferenceEnergy (PDE.Common.spatialPart p)
  have hgradient :
      classicalWaveSpatialGradient (n := n) u p = 0 := by
    simpa only [PDE.Common.timeSpaceCons_spatialPart] using
      semilinearWaveSpatialGradient_eq_zero_of_referenceEnergy_eq_zero
        (n := n) V hVnonneg hu t₀ (p 0) (henergyIntegrable (p 0)) (henergyEq (p 0))
        hreferenceEnergy (PDE.Common.spatialPart p)
  ext v
  rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul, zero_apply,
    Fin.sum_univ_succ, htime, zero_mul, zero_add]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [← classicalWaveSpatialGradient_apply, hgradient]
  simp

/-- Vanishing conserved nonnegative energy makes the spacetime field
constant. -/
theorem eq_const_of_semilinearWave_referenceEnergy_eq_zero (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z)
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t₀ : ℝ)
    (henergyIntegrable : ∀ t, Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergyEq : ∀ t, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (hreferenceEnergy : semilinearWaveSpatialEnergy (n := n) V u t₀ = 0) :
    u = fun _ ↦ u 0 := by
  funext p
  exact is_const_of_fderiv_eq_zero
    (hu.differentiable (by norm_num)) (semilinearWave_fderiv_eq_zero_of_referenceEnergy_eq_zero
      (n := n) V hVnonneg hu t₀ henergyIntegrable henergyEq hreferenceEnergy) p 0

end WaveEquation
