/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.CoercivePotential

/-!
# Continuation from coercive semilinear wave energy

Energy conservation for a semilinear wave equation controls an explicit
spatial integral. A local well-posedness theorem, however, usually continues
solutions using a norm on a model-specific state space. We connect the two
statements. The comparison between that state norm and the coercive spatial
energy, and the continuation theorem for the chosen solution class, are hypotheses.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Eventual control of a model-specific state norm by the coercive wave
energy gives a uniform bound in terms of the conserved reference energy. -/
theorem eventually_norm_le_sqrt_two_mul_referenceEnergy_of_coercive {E : Type*} [Norm E] (V : ℝ → ℝ)
    (μ : ℝ) (hμ : 0 ≤ μ) (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (t₀ : ℝ) {state : ℝ → E} {times : Set ℝ} {T : ℝ}
    (henergyIntegrable : ∀ᶠ t in nhdsWithin T times,
      Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : ∀ᶠ t in nhdsWithin T times, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (hnormSq : ∀ᶠ t in nhdsWithin T times, ‖state t‖ ^ 2 ≤
      semilinearWaveCoerciveEnergy (n := n) μ u t) :
    ∀ᶠ t in nhdsWithin T times, ‖state t‖ ≤
      Real.sqrt (2 * semilinearWaveSpatialEnergy (n := n) V u t₀) := by
  filter_upwards [henergyIntegrable, henergy, hnormSq] with
    t htIntegrable htEnergy htNormSq
  exact norm_le_sqrt_two_mul_referenceEnergy_of_sq_le_coerciveEnergy
      V μ hμ hVcoercive hu t₀ t htIntegrable htEnergy htNormSq

/-- A model-specific continuation criterion applies whenever its controlling
state norm is eventually bounded by a conserved coercive wave energy. -/
theorem extendable_of_eventually_norm_sq_le_semilinearWaveCoerciveEnergy {E : Type*} [Norm E]
    (V : ℝ → ℝ) (μ : ℝ) (hμ : 0 ≤ μ) (hVcoercive : ∀ z, μ * z ^ 2 ≤ V z) {u : ℝ^(n + 1) → ℝ}
    (hu : ContDiff ℝ 2 u) (t₀ : ℝ) {state : ℝ → E} {times : Set ℝ} {T : ℝ} {extendable : Prop}
    (henergyIntegrable : ∀ᶠ t in nhdsWithin T times,
      Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (henergy : ∀ᶠ t in nhdsWithin T times, semilinearWaveSpatialEnergy (n := n) V u t =
      semilinearWaveSpatialEnergy (n := n) V u t₀)
    (hnormSq : ∀ᶠ t in nhdsWithin T times, ‖state t‖ ^ 2 ≤
      semilinearWaveCoerciveEnergy (n := n) μ u t)
    (hcontinuation : (∃ C : ℝ, ∀ᶠ t in nhdsWithin T times, ‖state t‖ ≤ C) → extendable) :
    extendable :=
  hcontinuation ⟨Real.sqrt (2 * semilinearWaveSpatialEnergy (n := n) V u t₀),
      eventually_norm_le_sqrt_two_mul_referenceEnergy_of_coercive
        V μ hμ hVcoercive hu t₀ henergyIntegrable henergy hnormSq⟩

end WaveEquation
