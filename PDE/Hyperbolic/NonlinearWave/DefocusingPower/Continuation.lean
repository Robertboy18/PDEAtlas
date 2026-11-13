/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Scalar.OddPower
public import PDE.Hyperbolic.NonlinearWave.CoercivePotential
public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Differentiation
import PDE.Hyperbolic.NonlinearWave.Continuation.CoerciveEnergy
import PDE.Hyperbolic.NonlinearWave.DefocusingPower.Conservation

/-!
# Continuation for defocusing odd-power waves

Four ingredients combine here:

* the odd-power semilinear wave equation;
* conservation of its global spatial energy;
* coercivity of the defocusing potential;
* a continuation criterion supplied by the chosen local solution theory.

The state-norm comparison and the continuation criterion are hypotheses.
The theorem derives the norm bound needed by that criterion from the energy of a
supplied globally `C²` field satisfying the equation. Its conclusion is the given
proposition `extendable`; no extended trajectory is constructed.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open PDE.Analysis.Scalar
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Conserved defocusing energy supplies the eventual norm bound required by a
model-specific continuation criterion.

The globally `C²` field and the analytic hypotheses for energy conservation are
supplied. `hnormSq` compares the chosen state norm with its coercive energy, and
`hcontinuation` turns eventual boundedness into the proposition `extendable`.
-/
theorem extendable_of_defocusingPowerEnergy {E : Type*} [Norm E] (massSq coupling : ℝ) (k : ℕ)
    (hmassSq : 0 ≤ massSq) (hcoupling : 0 ≤ coupling) {u : ℝ^(n + 1) → ℝ} (hu : ContDiff ℝ 2 u)
    (hwave : ∀ p, waveOperator (n := n) u p + massSq * u p + coupling * (u p) ^ (2 * k + 1) = 0)
    (henergyIntegrable : ∀ t, Integrable
      (semilinearWaveSpatialEnergyDensity (n := n) (oddPowerPotential massSq coupling k) u t))
    {s : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ} (hs : ∀ t, s t ∈ 𝓝 t)
    (hdominated : ∀ t, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s t,
      ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) (oddPowerPotential massSq coupling k) u r
      x‖ ≤ bound t x)
    (hboundIntegrable : ∀ t, Integrable (bound t))
    (hfluxCompact : ∀ t i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t))
    (t₀ : ℝ) {state : ℝ → E} {times : Set ℝ} {T : ℝ} {extendable : Prop}
    (hnormSq : ∀ᶠ t in nhdsWithin T times, ‖state t‖ ^ 2 ≤
      semilinearWaveCoerciveEnergy (n := n) (massSq / 2) u t)
    (hcontinuation : (∃ C : ℝ, ∀ᶠ t in nhdsWithin T times, ‖state t‖ ≤ C) → extendable) :
    extendable := by
  apply extendable_of_eventually_norm_sq_le_semilinearWaveCoerciveEnergy (E := E)
      (oddPowerPotential massSq coupling k) (massSq / 2)
      (div_nonneg hmassSq (by norm_num)) (oddPowerPotential_quadratic_le k hcoupling) hu t₀
  · exact Filter.Eventually.of_forall henergyIntegrable
  · filter_upwards [] with t
    exact oddPowerSpatialEnergy_conserved massSq coupling k hu hwave henergyIntegrable hs hdominated
          hboundIntegrable hfluxCompact t t₀
  · exact hnormSq
  · exact hcontinuation

end WaveEquation
