/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Basic
import PDE.FDeriv.SpaceTime

/-!
# A priori bounds from global semilinear wave energy

For a nonnegative potential, each normalized kinetic, spatial-gradient, and
potential contribution is nonnegative and bounded by the total spatial
energy. Under the natural continuity hypotheses, domination by an integrable
total energy density also proves that each component is integrable. This
distinction matters because the Bochner integral is totalized on
nonintegrable functions.

These are fixed-time estimates. Consequences of energy
conservation are in `ConservedEnergyBounds`, while vanishing-energy results
are in `ZeroEnergyRigidity`.

The energy is `E(t) = ∫ ½ u_t² + ½ |∇u|² + V(u) dx` for the semilinear wave
equation `u_tt - Δu + V'(u) = 0` (Evans, §12.1.1). The sign condition `V ≥ 0` is what lets
`E` control each of its three
parts separately; without it the potential term could cancel the others.

## Main results

* `semilinearWaveSpatialEnergy_nonneg`: `E(t) ≥ 0` for `V ≥ 0`.
* `integrable_semilinearWaveSpatialKineticEnergyDensity` and its gradient and
  potential companions: integrability of each component from integrability of
  the total density.
* `integral_semilinearWaveTimeDerivativeSq_le_two_mul_spatialEnergy`,
  `integral_semilinearWaveGradientSq_le_two_mul_spatialEnergy`,
  `integral_semilinearWavePotentialEnergy_le_spatialEnergy`: the bounds
  `∫ u_t² ≤ 2E`, `∫ |∇u|² ≤ 2E`, `∫ V(u) ≤ E` on a fixed time slice.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- A nonnegative potential makes the total energy on every spatial slice
nonnegative. No integrability assumption is needed for this order property of
the Bochner integral. -/
theorem semilinearWaveSpatialEnergy_nonneg (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z) (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) :
    0 ≤ semilinearWaveSpatialEnergy (n := n) V u t := by
  unfold semilinearWaveSpatialEnergy
  apply integral_nonneg
  intro x
  exact semilinearWaveEnergyDensity_nonneg (n := n) V hVnonneg u _

/-- The normalized kinetic-energy density is nonnegative. -/
theorem semilinearWaveSpatialKineticEnergyDensity_nonneg (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) :
    0 ≤ semilinearWaveSpatialKineticEnergyDensity (n := n) u t x := by
  unfold semilinearWaveSpatialKineticEnergyDensity
  positivity

/-- The normalized spatial-gradient energy density is nonnegative. -/
theorem semilinearWaveSpatialGradientEnergyDensity_nonneg (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) :
    0 ≤ semilinearWaveSpatialGradientEnergyDensity (n := n) u t x := by
  unfold semilinearWaveSpatialGradientEnergyDensity
  positivity

/-- A nonnegative potential gives a nonnegative potential-energy density. -/
theorem semilinearWaveSpatialPotentialEnergyDensity_nonneg (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z)
    (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) :
    0 ≤ semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t x := by
  exact hVnonneg _

/-- For a nonnegative potential, the kinetic component is bounded by the
full energy density pointwise. -/
theorem semilinearWaveSpatialKineticEnergyDensity_le_spatialEnergyDensity (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) :
    semilinearWaveSpatialKineticEnergyDensity (n := n) u t x ≤
      semilinearWaveSpatialEnergyDensity (n := n) V u t x := by
  rw [semilinearWaveSpatialEnergyDensity_eq_components]
  exact le_add_of_nonneg_right <| add_nonneg (semilinearWaveSpatialGradientEnergyDensity_nonneg
        (n := n) u t x) (semilinearWaveSpatialPotentialEnergyDensity_nonneg
        (n := n) V hVnonneg u t x)

/-- For a nonnegative potential, the spatial-gradient component is bounded
by the full energy density pointwise. -/
theorem semilinearWaveSpatialGradientEnergyDensity_le_spatialEnergyDensity (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) :
    semilinearWaveSpatialGradientEnergyDensity (n := n) u t x ≤
      semilinearWaveSpatialEnergyDensity (n := n) V u t x := by
  rw [semilinearWaveSpatialEnergyDensity_eq_components]
  linarith only [semilinearWaveSpatialKineticEnergyDensity_nonneg (n := n) u t x,
    semilinearWaveSpatialPotentialEnergyDensity_nonneg (n := n) V hVnonneg u t x]

/-- For a nonnegative potential, the potential component is bounded by the
full energy density pointwise. -/
theorem semilinearWaveSpatialPotentialEnergyDensity_le_spatialEnergyDensity (V : ℝ → ℝ)
    (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) :
    semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t x ≤
      semilinearWaveSpatialEnergyDensity (n := n) V u t x := by
  rw [semilinearWaveSpatialEnergyDensity_eq_components]
  linarith only [semilinearWaveSpatialKineticEnergyDensity_nonneg (n := n) u t x,
    semilinearWaveSpatialGradientEnergyDensity_nonneg (n := n) u t x]

/-- Any scalar density bounded by the potential is bounded by the total
energy density on the same spatial slice. -/
theorem semilinearWaveSpatialPotentialEnergyDensity_le_spatialEnergyDensity_of_le (V W : ℝ → ℝ)
    (hWV : ∀ z, W z ≤ V z) (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) :
    semilinearWaveSpatialPotentialEnergyDensity (n := n) W u t x ≤
      semilinearWaveSpatialEnergyDensity (n := n) V u t x := by
  calc
    semilinearWaveSpatialPotentialEnergyDensity (n := n) W u t x ≤
        semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t x := hWV _
    _ ≤ semilinearWaveSpatialEnergyDensity (n := n) V u t x :=
      semilinearWaveSpatialPotentialEnergyDensity_le_spatialEnergyDensity (n := n) V u t x

/-- The normalized kinetic-energy density on a fixed-time slice is
continuous for a `C²` field. -/
theorem continuous_semilinearWaveSpatialKineticEnergyDensity {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (t : ℝ) :
    Continuous (semilinearWaveSpatialKineticEnergyDensity (n := n) u t) := by
  have hpartial : Continuous fun p : ℝ^(n + 1) ↦
        (∂[0] u) p := by
    exact (PDE.contDiff_partialDeriv_of_succ (n := n + 1) (m := 1) (i := 0) hu).continuous
  unfold semilinearWaveSpatialKineticEnergyDensity
  exact continuous_const.mul ((hpartial.comp
      (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous).pow 2)

/-- The normalized spatial-gradient energy density on a fixed-time slice is
continuous for a `C²` field. -/
theorem continuous_semilinearWaveSpatialGradientEnergyDensity {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (t : ℝ) :
    Continuous (semilinearWaveSpatialGradientEnergyDensity (n := n) u t) := by
  have hgradient : Continuous fun x : ℝ^n ↦ classicalWaveSpatialGradient (n := n) u
          (PDE.Common.timeSpaceCons (n := n) t x) := (contDiff_classicalWaveSpatialGradient
      (n := n) (m := 1) hu).continuous.comp
        (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous
  unfold semilinearWaveSpatialGradientEnergyDensity
  exact continuous_const.mul (hgradient.norm.pow 2)

/-- The potential-energy density on a fixed-time slice is continuous when
the potential and field are continuous. -/
theorem continuous_semilinearWaveSpatialPotentialEnergyDensity {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : Continuous V) (hu : Continuous u) (t : ℝ) :
    Continuous (semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t) := by
  unfold semilinearWaveSpatialPotentialEnergyDensity
  exact hV.comp (hu.comp (PDE.Common.contDiff_timeSpaceCons_spatial n t (m := 1)).continuous)

/-- Integrability of a nonnegative total energy density implies integrability
of its normalized kinetic-energy component. -/
theorem integrable_semilinearWaveSpatialKineticEnergyDensity (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z)
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    Integrable (semilinearWaveSpatialKineticEnergyDensity (n := n) u t) := by
  apply henergyIntegrable.mono_nonneg (continuous_semilinearWaveSpatialKineticEnergyDensity
      (n := n) hu t).aestronglyMeasurable
  · exact Filter.Eventually.of_forall <| semilinearWaveSpatialKineticEnergyDensity_nonneg
        (n := n) u t
  · exact Filter.Eventually.of_forall <|
      semilinearWaveSpatialKineticEnergyDensity_le_spatialEnergyDensity (n := n) V hVnonneg u t

/-- Integrability of a nonnegative total energy density implies integrability
of its normalized spatial-gradient component. -/
theorem integrable_semilinearWaveSpatialGradientEnergyDensity (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z)
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    Integrable (semilinearWaveSpatialGradientEnergyDensity (n := n) u t) := by
  apply henergyIntegrable.mono_nonneg (continuous_semilinearWaveSpatialGradientEnergyDensity
      (n := n) hu t).aestronglyMeasurable
  · exact Filter.Eventually.of_forall <| semilinearWaveSpatialGradientEnergyDensity_nonneg
        (n := n) u t
  · exact Filter.Eventually.of_forall <|
      semilinearWaveSpatialGradientEnergyDensity_le_spatialEnergyDensity (n := n) V hVnonneg u t

/-- A continuous nonnegative scalar density dominated by the potential
inherits integrability from the total energy density. -/
theorem integrable_semilinearWaveSpatialPotentialEnergyDensity_of_le {V W : ℝ → ℝ}
    (hW : Continuous W) (hWnonneg : ∀ z, 0 ≤ W z) (hWV : ∀ z, W z ≤ V z) {u : ℝ^(n + 1) → ℝ}
    (hu : Continuous u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    Integrable (semilinearWaveSpatialPotentialEnergyDensity (n := n) W u t) := by
  apply henergyIntegrable.mono_nonneg (continuous_semilinearWaveSpatialPotentialEnergyDensity
      (n := n) hW hu t).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ hWnonneg (u (PDE.Common.timeSpaceCons (n := n) t x))
  · exact Filter.Eventually.of_forall <|
      semilinearWaveSpatialPotentialEnergyDensity_le_spatialEnergyDensity_of_le (n := n) V W hWV u t

/-- Integrability of a nonnegative total energy density implies integrability
of its potential-energy component. -/
theorem integrable_semilinearWaveSpatialPotentialEnergyDensity {V : ℝ → ℝ} (hV : Continuous V)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    Integrable (semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t) := by
  exact integrable_semilinearWaveSpatialPotentialEnergyDensity_of_le
    (n := n) (V := V) (W := V) hV hVnonneg (fun _ ↦ le_rfl) hu t henergyIntegrable

/-- The total spatial energy controls its normalized kinetic contribution
`(1 / 2) ∫ uₜ²`. -/
theorem integral_semilinearWaveKineticEnergy_le_spatialEnergy (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z)
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    (∫ x : ℝ^n, semilinearWaveSpatialKineticEnergyDensity (n := n) u t x) ≤
      semilinearWaveSpatialEnergy (n := n) V u t := by
  unfold semilinearWaveSpatialEnergy
  exact integral_mono (integrable_semilinearWaveSpatialKineticEnergyDensity
      (n := n) V hVnonneg hu t henergyIntegrable) henergyIntegrable
    (semilinearWaveSpatialKineticEnergyDensity_le_spatialEnergyDensity (n := n) V hVnonneg u t)

/-- The total spatial energy controls its normalized spatial-gradient
contribution `(1 / 2) ∫ ‖Dₓu‖²`. -/
theorem integral_semilinearWaveGradientEnergy_le_spatialEnergy (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z)
    {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    (∫ x : ℝ^n, semilinearWaveSpatialGradientEnergyDensity (n := n) u t x) ≤
      semilinearWaveSpatialEnergy (n := n) V u t := by
  unfold semilinearWaveSpatialEnergy
  exact integral_mono (integrable_semilinearWaveSpatialGradientEnergyDensity
      (n := n) V hVnonneg hu t henergyIntegrable) henergyIntegrable
    (semilinearWaveSpatialGradientEnergyDensity_le_spatialEnergyDensity (n := n) V hVnonneg u t)

/-- The integral of a nonnegative scalar density dominated by the potential
is bounded by the total spatial energy. -/
theorem integral_semilinearWaveSpatialPotentialEnergyDensity_le_spatialEnergy_of_le (V W : ℝ → ℝ)
    (hW : Continuous W) (hWnonneg : ∀ z, 0 ≤ W z) (hWV : ∀ z, W z ≤ V z) {u : ℝ^(n + 1) → ℝ}
    (hu : Continuous u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    (∫ x : ℝ^n, semilinearWaveSpatialPotentialEnergyDensity (n := n) W u t x) ≤
      semilinearWaveSpatialEnergy (n := n) V u t := by
  unfold semilinearWaveSpatialEnergy
  exact integral_mono (integrable_semilinearWaveSpatialPotentialEnergyDensity_of_le
      (n := n) hW hWnonneg hWV hu t henergyIntegrable) henergyIntegrable
    (semilinearWaveSpatialPotentialEnergyDensity_le_spatialEnergyDensity_of_le (n := n) V W hWV u t)

/-- The total spatial energy controls the potential-energy contribution
`∫ V(u)`. -/
theorem integral_semilinearWavePotentialEnergy_le_spatialEnergy (V : ℝ → ℝ) (hV : Continuous V)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : Continuous u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    (∫ x : ℝ^n, semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t x) ≤
      semilinearWaveSpatialEnergy (n := n) V u t := by
  exact integral_semilinearWaveSpatialPotentialEnergyDensity_le_spatialEnergy_of_le
      (n := n) V V hV hVnonneg (fun _ ↦ le_rfl) hu t henergyIntegrable

/-- The normalized kinetic and spatial-gradient components together are
bounded by the total energy. -/
theorem integral_semilinearWaveDerivativeEnergy_le_spatialEnergy (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    (∫ x : ℝ^n, semilinearWaveSpatialKineticEnergyDensity (n := n) u t x +
      semilinearWaveSpatialGradientEnergyDensity (n := n) u t x) ≤
      semilinearWaveSpatialEnergy (n := n) V u t := by
  unfold semilinearWaveSpatialEnergy
  apply integral_mono ((integrable_semilinearWaveSpatialKineticEnergyDensity
        (n := n) V hVnonneg hu t henergyIntegrable).add
      (integrable_semilinearWaveSpatialGradientEnergyDensity
        (n := n) V hVnonneg hu t henergyIntegrable)) henergyIntegrable
  intro x
  change semilinearWaveSpatialKineticEnergyDensity (n := n) u t x +
        semilinearWaveSpatialGradientEnergyDensity (n := n) u t x ≤
      semilinearWaveSpatialEnergyDensity (n := n) V u t x
  rw [semilinearWaveSpatialEnergyDensity_eq_components]
  simpa only [add_assoc] using le_add_of_nonneg_right (a :=
        semilinearWaveSpatialKineticEnergyDensity (n := n) u t x +
          semilinearWaveSpatialGradientEnergyDensity (n := n) u t x)
      (semilinearWaveSpatialPotentialEnergyDensity_nonneg (n := n) V hVnonneg u t x)

/-- The total spatial energy controls the unnormalized squared time
derivative by `2E(t)`. -/
theorem integral_semilinearWaveTimeDerivativeSq_le_two_mul_spatialEnergy (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    (∫ x : ℝ^n, ((∂[0] u) (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2) ≤
      2 * semilinearWaveSpatialEnergy (n := n) V u t := by
  have hnormalized := integral_semilinearWaveKineticEnergy_le_spatialEnergy
      (n := n) V hVnonneg hu t henergyIntegrable
  unfold semilinearWaveSpatialKineticEnergyDensity at hnormalized
  rw [integral_const_mul] at hnormalized
  linarith

/-- The total spatial energy controls the unnormalized squared spatial
gradient by `2E(t)`. -/
theorem integral_semilinearWaveGradientSq_le_two_mul_spatialEnergy (V : ℝ → ℝ)
    (hVnonneg : ∀ z, 0 ≤ V z) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (henergyIntegrable : Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)) :
    (∫ x : ℝ^n, ‖classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t x)‖ ^
      2) ≤ 2 * semilinearWaveSpatialEnergy (n := n) V u t := by
  have hnormalized := integral_semilinearWaveGradientEnergy_le_spatialEnergy
      (n := n) V hVnonneg hu t henergyIntegrable
  unfold semilinearWaveSpatialGradientEnergyDensity at hnormalized
  rw [integral_const_mul] at hnormalized
  linarith

end WaveEquation
