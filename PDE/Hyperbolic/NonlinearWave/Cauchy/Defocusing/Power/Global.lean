/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Equations

/-!
# Global energy waves for real defocusing powers on ℝ³

Every real exponent `1 < p ≤ 3` and arbitrary H¹ × L² datum give a global
energy solution of `uₜₜ − Δu + |u|^(p-1)u = 0`. The constructor derives the
source estimates, potential identity, conservation, and finite-horizon state
bound. Both initial data are attained strongly. Uniqueness holds among all
forward energy-continuous trajectories satisfying the integrated PDE.

The continuous map is extended constantly before zero. The PDE, uniqueness, and conservation
assertions concern forward time.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power

variable {p : ℝ} (hp : 1 < p) (hp3 : p ≤ 3)

/-- Arbitrary energy data give a global unique real-power wave with both strong
traces, conserved physical energy, and a derived finite-horizon full state bound. -/
theorem exists_global_energySolution (x : H¹(ℝ^3) × DerivLp 3 2 univ) :
    ∃ u : C(ℝ, H¹(ℝ^3) × DerivLp 3 2 univ),
      (nonlinearity hp hp3).IsEnergySolution x u ∧
      Filter.Tendsto (fun t ↦ (u t).1) (𝓝[≥] (0 : ℝ)) (𝓝 x.1) ∧
      Filter.Tendsto (fun t ↦ (u t).2) (𝓝[≥] (0 : ℝ)) (𝓝 x.2) ∧
      (∀ t : ℝ, 0 ≤ t → physicalEnergy p (u t) = physicalEnergy p x) ∧
      (∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤
        ‖(energyTriple 3).inclusion x.1‖ + (t + 1) * Real.sqrt (2 * physicalEnergy p x)) ∧
      ∀ v : ℝ → H¹(ℝ^3) × DerivLp 3 2 univ,
        (nonlinearity hp hp3).IsEnergySolution x v → EqOn u v (Ici 0) := by
  let N := nonlinearity hp hp3
  have hu := N.globalSolution_isEnergySolution x
  refine ⟨N.globalSolution x, hu, (continuous_fst.tendsto x).comp hu.tendsto_initial,
    (continuous_snd.tendsto x).comp hu.tendsto_initial, ?_, ?_, fun _ hv ↦ hu.eqOn hv⟩
  · intro t ht
    simpa only [N, ← energy_eq_physicalEnergy hp hp3] using N.energy_globalSolution x ht
  · intro t ht
    simpa only [N, energy_eq_physicalEnergy hp hp3] using N.norm_globalSolution_le x ht

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power
