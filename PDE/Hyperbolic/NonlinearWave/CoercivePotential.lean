/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
import PDE.FDeriv.SpaceTime
import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Bounds

/-!
# Field bounds from coercive wave potentials

A potential satisfying `μ z² ≤ V z` with `μ > 0` controls the spatial
`L²` mass of the wave field by the total semilinear wave energy. Global
energy conservation transports the bound to any chosen initial time.

The estimates are stated in terms of the energy density and conservation
theorem. We also prove rigidity: zero total energy
forces the field to vanish almost everywhere, and everywhere when the field
is continuous.

The setting is the semilinear wave equation `u_tt - Δu + V'(u) = 0` with the
energy `E(t) = ∫ ½ u_t² + ½ |∇u|² + V(u) dx` of Evans, §12.1.1, with `V` in the role of his `F`.
A potential with
`V(z) ≥ μ z²` is the abstract form of a positive mass term, and the bound
`∫ u² ≤ E/μ` is the usual way such a term gives control of the `L²` norm of
`u` itself, which the kinetic and gradient parts of the energy do not provide.

## Main results

* `integral_semilinearWaveFieldSq_le_spatialEnergy_div`: `∫ u(t)² ≤ E(t)/μ`.
* `semilinearWaveCoerciveEnergy_le_two_mul_spatialEnergy`: the unnormalized
  sum `∫ u_t² + |∇u|² + 2μ u²` is at most `2E(t)`.
* `semilinearWaveField_eq_zero_of_spatialEnergy_eq_zero`: zero energy forces a
  continuous field to vanish on the slice.
* The `_referenceEnergy` variants transport these bounds through an energy
  equality `E(t) = E(t₀)`.  That equality is a hypothesis here; it is proved for
  classical solutions in `GlobalEnergy.Conservation`.

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

/-- A nonnegative quadratic lower bound on the potential makes every spatial
energy slice nonnegative. -/
theorem semilinearWaveSpatialEnergy_nonneg_of_coercive (V : ℝ → ℝ) (μ : ℝ) (hμ : 0 ≤ μ)
    (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) (u : ℝ^(n + 1) → ℝ) (t : ℝ) :
    0 ≤ semilinearWaveSpatialEnergy (n := n) V u t := by
  apply semilinearWaveSpatialEnergy_nonneg
  intro z
  exact (mul_nonneg hμ (sq_nonneg z)).trans (hVcoercive z)

/-- Positive quadratic coercivity and integrability of the total energy
density imply integrability of the squared field on the same time slice. -/
theorem integrable_semilinearWaveFieldSq_of_coercive (V : ℝ → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    Integrable fun x : ℝ^n ↦ (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 := by
  have hscaled : Integrable (semilinearWaveSpatialPotentialEnergyDensity (n := n)
          (fun z : ℝ ↦ μ * z ^ 2) u t) :=
    integrable_semilinearWaveSpatialPotentialEnergyDensity_of_le (n := n)
      (continuous_const.mul (continuous_id.pow 2)) (fun z ↦ mul_nonneg hμ.le (sq_nonneg z))
      hVcoercive hu t henergyIntegrable
  have hinv := hscaled.const_mul μ⁻¹
  simpa only [semilinearWaveSpatialPotentialEnergyDensity, ← mul_assoc,
    inv_mul_cancel₀ hμ.ne', one_mul] using hinv

/-- A quadratically coercive potential controls the spatial integral of the
squared wave field by the total energy on the same time slice. -/
theorem integral_semilinearWaveFieldSq_le_spatialEnergy_div (V : ℝ → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    (∫ x : ℝ^n, (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) ≤
      semilinearWaveSpatialEnergy (n := n) V u t / μ := by
  have hscaled : (∫ x : ℝ^n, semilinearWaveSpatialPotentialEnergyDensity (n := n)
            (fun z : ℝ ↦ μ * z ^ 2) u t x) ≤ semilinearWaveSpatialEnergy (n := n) V u t :=
    integral_semilinearWaveSpatialPotentialEnergyDensity_le_spatialEnergy_of_le
      (n := n) V (fun z : ℝ ↦ μ * z ^ 2) (continuous_const.mul (continuous_id.pow 2))
      (fun z ↦ mul_nonneg hμ.le (sq_nonneg z)) hVcoercive hu t henergyIntegrable
  simp only [semilinearWaveSpatialPotentialEnergyDensity] at hscaled
  rw [integral_const_mul] at hscaled
  exact (le_div_iff₀ hμ).2 (by simpa [mul_comm] using hscaled)

/-- Zero energy for a positively coercive potential forces the field to
vanish almost everywhere on the time slice. -/
theorem semilinearWaveField_ae_eq_zero_of_spatialEnergy_eq_zero (V : ℝ → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) (u : ℝ^(n + 1) → ℝ) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t = 0) :
    (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)) =ᵐ[ (volume : Measure (ℝ^n))] 0 := by
  have hVnonneg : ∀ z, 0 ≤ V z := fun z ↦ (mul_nonneg hμ.le (sq_nonneg z)).trans (hVcoercive z)
  have henergyAE : semilinearWaveSpatialEnergyDensity (n := n) V u t =ᵐ[
        (volume : Measure (ℝ^n))] 0 := by
    apply (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall fun x ↦
        semilinearWaveEnergyDensity_nonneg (n := n) V hVnonneg u _) henergyIntegrable).mp
    simpa [semilinearWaveSpatialEnergy, semilinearWaveSpatialEnergyDensity] using henergy
  filter_upwards [henergyAE] with x hx
  have hpotential := hVcoercive (u (PDE.Common.timeSpaceCons (n := n) t x))
  simp only [semilinearWaveSpatialEnergyDensity,
    semilinearWaveEnergyDensity, classicalWaveEnergyDensity, Pi.zero_apply] at hx
  have hfieldSq :
      (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 = 0 := by
    nlinarith [sq_nonneg ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)), sq_nonneg
        ‖classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t x)‖]
  exact sq_eq_zero_iff.mp hfieldSq

/-- If a positive quadratic potential controls the field and a spatial
energy slice vanishes, then the spatial integral of the squared field also
vanishes. -/
theorem integral_semilinearWaveFieldSq_eq_zero_of_spatialEnergy_eq_zero (V : ℝ → ℝ) (μ : ℝ)
    (hμ : 0 < μ) (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) (u : ℝ^(n + 1) → ℝ) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t = 0) :
    (∫ x : ℝ^n, (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ semilinearWaveField_ae_eq_zero_of_spatialEnergy_eq_zero
      (n := n) V μ hμ hVcoercive u t henergyIntegrable henergy] with x hx
  simp only [Pi.zero_apply] at hx ⊢
  rw [hx]
  norm_num

/-- Zero energy for a positively coercive potential forces a continuous
field to vanish pointwise on the time slice. -/
theorem semilinearWaveField_eq_zero_of_spatialEnergy_eq_zero (V : ℝ → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t = 0) :
    ∀ x : ℝ^n, u (PDE.Common.timeSpaceCons (n := n) t x) = 0 := by
  have hfieldContinuous : Continuous fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x) :=
    hu.comp (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
  have hfieldZero : (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x)) = 0 :=
    (hfieldContinuous.ae_eq_iff_eq (volume : Measure (ℝ^n)) continuous_const).mp
        (semilinearWaveField_ae_eq_zero_of_spatialEnergy_eq_zero
          (n := n) V μ hμ hVcoercive u t henergyIntegrable henergy)
  intro x
  simpa only [Pi.zero_apply] using congrFun hfieldZero x

/-- The coercive quadratic energy associated with a mass coefficient `μ`.

This is the spatial integral of the squared time derivative, the squared
spatial gradient, and the weighted squared field. It is a convenient
unscaled norm-like quantity; the semilinear wave energy bounds it when the
potential has the lower bound `μ z² ≤ V z`. -/
def semilinearWaveCoerciveEnergy
    (μ : ℝ) (u : ℝ^(n + 1) → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℝ^n,
    ((∂[0] u)
        (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 +
      ‖classicalWaveSpatialGradient (n := n) u
          (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2 +
      2 * μ * (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2

/-- A nonnegative quadratic lower bound on the potential controls the sum
of the squared time derivative, squared spatial gradient, and weighted field
mass by twice the total energy. -/
theorem semilinearWaveCoerciveEnergy_le_two_mul_spatialEnergy (V : ℝ → ℝ) (μ : ℝ) (hμ : 0 ≤ μ)
    (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    semilinearWaveCoerciveEnergy (n := n) μ u t ≤
      2 * semilinearWaveSpatialEnergy (n := n) V u t := by
  have hVnonneg : ∀ z, 0 ≤ V z := fun z ↦ (mul_nonneg hμ (sq_nonneg z)).trans (hVcoercive z)
  have htime : Integrable fun x : ℝ^n ↦ ((∂[0] u)
          (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 := by
    simpa [semilinearWaveSpatialKineticEnergyDensity] using
      (integrable_semilinearWaveSpatialKineticEnergyDensity
        (n := n) V hVnonneg hu t henergyIntegrable).const_mul 2
  have hgradient : Integrable fun x : ℝ^n ↦ ‖classicalWaveSpatialGradient (n := n) u
          (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2 := by
    simpa [semilinearWaveSpatialGradientEnergyDensity] using
      (integrable_semilinearWaveSpatialGradientEnergyDensity
        (n := n) V hVnonneg hu t henergyIntegrable).const_mul 2
  have hfield : Integrable fun x : ℝ^n ↦ 2 * μ *
          (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 := by
    have hscaled := integrable_semilinearWaveSpatialPotentialEnergyDensity_of_le (n := n)
        (V := V) (W := fun z : ℝ ↦ μ * z ^ 2) (continuous_const.mul (continuous_id.pow 2))
        (fun z ↦ mul_nonneg hμ (sq_nonneg z)) hVcoercive hu.continuous t henergyIntegrable
    simpa only [semilinearWaveSpatialPotentialEnergyDensity, mul_assoc] using hscaled.const_mul 2
  have hsum : Integrable fun x : ℝ^n ↦ ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 +
          ‖classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2 +
          2 * μ *
            (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2 := by
    exact ((htime.add hgradient).add hfield).congr <| Filter.Eventually.of_forall fun _ ↦ rfl
  unfold semilinearWaveCoerciveEnergy semilinearWaveSpatialEnergy
  rw [← integral_const_mul]
  apply integral_mono hsum (henergyIntegrable.const_mul 2)
  intro x
  have hpotential := hVcoercive (u (PDE.Common.timeSpaceCons (n := n) t x))
  simp only [semilinearWaveSpatialEnergyDensity,
    semilinearWaveEnergyDensity, classicalWaveEnergyDensity]
  nlinarith

/-- Global energy conservation bounds the spatial integral of the squared
wave field at time `t` by the total energy at the reference time `t₀`. -/
theorem integral_semilinearWaveFieldSq_le_referenceEnergy_div (V : ℝ → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t = semilinearWaveSpatialEnergy (n := n) V
      u t₀) :
    (∫ x : ℝ^n, (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) ≤
      semilinearWaveSpatialEnergy (n := n) V u t₀ / μ := by
  calc
    (∫ x : ℝ^n, (u (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) ≤
        semilinearWaveSpatialEnergy (n := n) V u t / μ :=
      integral_semilinearWaveFieldSq_le_spatialEnergy_div V μ hμ hVcoercive hu t henergyIntegrable
    _ = semilinearWaveSpatialEnergy (n := n) V u t₀ / μ := by rw [henergy]

/-- Global energy conservation transports the combined coercive estimate to
the total energy at a reference time. -/
theorem semilinearWaveCoerciveEnergy_le_two_mul_referenceEnergy (V : ℝ → ℝ) (μ : ℝ) (hμ : 0 ≤ μ)
    (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t = semilinearWaveSpatialEnergy (n := n) V
      u t₀) :
    semilinearWaveCoerciveEnergy (n := n) μ u t ≤
      2 * semilinearWaveSpatialEnergy (n := n) V u t₀ := by
  calc
    semilinearWaveCoerciveEnergy (n := n) μ u t ≤ 2 * semilinearWaveSpatialEnergy (n := n) V u t :=
      semilinearWaveCoerciveEnergy_le_two_mul_spatialEnergy V μ hμ hVcoercive hu t henergyIntegrable
    _ = 2 * semilinearWaveSpatialEnergy (n := n) V u t₀ := by rw [henergy]

/-- A state whose squared norm is controlled by the coercive wave energy is
bounded by the square root of twice the conserved reference energy.

The hypothesis relating `state` to `semilinearWaveCoerciveEnergy` is
intentionally explicit. Its proof depends on the state space and local
well-posedness theory chosen by a particular wave model. -/
theorem norm_le_sqrt_two_mul_referenceEnergy_of_sq_le_coerciveEnergy {E : Type*} [Norm E]
    (V : ℝ → ℝ) (μ : ℝ) (hμ : 0 ≤ μ) (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (t₀ t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : semilinearWaveSpatialEnergy (n := n) V u t = semilinearWaveSpatialEnergy (n := n) V
      u t₀)
    {state : E} (hstate : ‖state‖ ^ 2 ≤ semilinearWaveCoerciveEnergy (n := n) μ u t) :
    ‖state‖ ≤ Real.sqrt (2 * semilinearWaveSpatialEnergy (n := n) V u t₀) :=
  Real.le_sqrt_of_sq_le <| hstate.trans <| semilinearWaveCoerciveEnergy_le_two_mul_referenceEnergy
        V μ hμ hVcoercive hu t₀ t henergyIntegrable henergy

end WaveEquation
