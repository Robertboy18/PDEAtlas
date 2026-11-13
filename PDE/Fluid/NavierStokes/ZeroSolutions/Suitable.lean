/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Suitable
public import PDE.Fluid.NavierStokes.ZeroSolutions.LerayHopf

/-!
# Zero suitable Navier–Stokes solutions

All local energy pairings vanish for zero velocity and zero pressure. Together
with the existing zero energy-class solution, this gives a suitable solution
on any prescribed positive finite slab.
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory

set_option linter.missingDocs true

/-- Zero velocity and gradient satisfy the local energy inequality for any pressure
and any forcing, since each tested energy pairing vanishes. -/
theorem localEnergyInequality_zero {n : ℕ} (nse : Problem n)
    (p : ℝ^(n + 1) → ℝ) (T : ℝ) :
    LocalEnergyInequality nse (fun _ ↦ 0) p (fun _ ↦ 0) T := by
  intro φ _
  have hd : localEnergyDissipationDensity nse (fun _ ↦ 0) φ = 0 := by
    funext z
    simp [localEnergyDissipationDensity]
  have he : localEnergyDiffusionDensity nse (fun _ ↦ 0) φ = 0 := by
    funext z
    simp [localEnergyDiffusionDensity, IncompressibleFlow.specificKineticEnergy]
  have hp : localEnergyFluxDensity (fun _ ↦ 0) p φ = 0 := by
    funext z
    simp [localEnergyFluxDensity]
  have hf : localEnergyForceDensity nse (fun _ ↦ 0) φ = 0 := by
    funext z
    simp [localEnergyForceDensity]
  simp [LocalEnergyIntegrable, localEnergyDissipation, localEnergyInput, hd, he, hp, hf]

/-- The zero energy-class solution is suitable on every positive finite slab. -/
def zeroSuitableLerayHopfSolution {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (T : ℝ) (hT : 0 < T) : SuitableLerayHopfSolution (zeroProblem n viscosity hviscosity) where
  toPressureRepresentativeLerayHopfSolution :=
    zeroPressureRepresentativeLerayHopfSolution viscosity hviscosity T hT
  velocity_local_memLp_three := by
    intro K _ _
    exact MemLp.zero
  pressure_local_memLp_three_halves := by
    intro K _ _
    exact MemLp.zero
  local_energy_inequality := localEnergyInequality_zero _ _ _

/-- A zero-data suitable Leray–Hopf solution exists on each positive finite slab. -/
theorem exists_zero_suitableLerayHopfSolution_on {n : ℕ}
    (viscosity : ℝ) (hviscosity : 0 < viscosity) (T : ℝ) (hT : 0 < T) :
    ∃ sol : SuitableLerayHopfSolution (zeroProblem n viscosity hviscosity), (sol.T : ℝ) = T :=
  ⟨zeroSuitableLerayHopfSolution viscosity hviscosity T hT, rfl⟩

end NavierStokes
