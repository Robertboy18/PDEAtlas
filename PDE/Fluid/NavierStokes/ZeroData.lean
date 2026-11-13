/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Energy

/-!
# Zero Navier-Stokes data

The zero-data problem `zeroProblem`, with the vanishing of the energy, enstrophy and dissipation
of the zero velocity and of the power supplied by the zero force. These facts are used by its
classical and weak solutions.
-/

@[expose] public section

open PDE (partialDeriv)

namespace NavierStokes

open EuclideanSpace MeasureTheory Order

set_option linter.missingDocs true

/-- The zero force and zero initial velocity define a Navier-Stokes problem for any positive
viscosity. -/
def zeroProblem (n : ℕ) (viscosity : ℝ) (hviscosity : 0 < viscosity) : Problem n where
  toInitialValueData := IncompressibleFlow.zeroInitialValueData n
  kinematicViscosity := ⟨viscosity, hviscosity⟩

/-- The zero velocity field has zero kinetic energy at every time. -/
theorem kineticEnergy_zero {n : ℕ} (t : ℝ) :
    kineticEnergy (n := n)
      (fun _ : ℝ^(n + 1) ↦ (0 : ℝ^n)) t = 0 := by
  simp [kineticEnergy, kineticEnergyDensity,
    IncompressibleFlow.specificKineticEnergy]

/-- The zero-data forcing supplies no power to any velocity field. -/
@[simp]
theorem forcePowerDensity_zeroProblem {n : ℕ}
    (viscosity : ℝ) (hviscosity : 0 < viscosity)
    (u : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) :
    forcePowerDensity (zeroProblem n viscosity hviscosity) u t x = 0 := by
  simp [forcePowerDensity, zeroProblem,
    IncompressibleFlow.zeroInitialValueData]

/-- The zero velocity field has zero enstrophy at every time. -/
theorem enstrophy_zero {n : ℕ} (t : ℝ) :
    enstrophy (n := n)
      (fun _ : ℝ^(n + 1) ↦ (0 : ℝ^n)) t = 0 := by
  have hvor (x : ℝ^n) :
      IncompressibleFlow.vorticityTensor n
          (fun _ : ℝ^(n + 1) ↦ (0 : ℝ^n))
          (PDE.Common.timeSpaceCons t x) = 0 := by
    ext ⟨i, j⟩
    simp [partialDeriv]
  simp [enstrophy, enstrophyDensity, hvor]

/-- The zero velocity field has zero classical gradient dissipation at every time. -/
theorem classicalVelocityGradientDissipation_zero {n : ℕ} (t : ℝ) :
    classicalVelocityGradientDissipation (n := n)
      (fun _ : ℝ^(n + 1) ↦ (0 : ℝ^n)) t = 0 := by
  have hgradient (x : ℝ^n) :
      IncompressibleFlow.spatialVelocityGradient n
          (fun _ : ℝ^(n + 1) ↦ (0 : ℝ^n))
          (PDE.Common.timeSpaceCons t x) = 0 := by
    ext ⟨i, j⟩
    simp [partialDeriv]
  simp [classicalVelocityGradientDissipation,
    classicalVelocityGradientDissipationDensity,
    IncompressibleFlow.classicalVelocityGradientSlice, hgradient]

/-- The zero weak-gradient field has zero dissipation at every time. -/
theorem weakGradientDissipation_zero {n : ℕ} (t : ℝ) :
    weakGradientDissipation (n := n)
      (fun _ : ℝ^(n + 1) ↦
        (0 : IncompressibleFlow.SpatialMatrix n)) t = 0 := by
  simp [weakGradientDissipation, weakGradientDissipationDensity,
    IncompressibleFlow.spatialGradientSlice]

/-- The zero-data problem has zero initial kinetic energy. -/
theorem initialKineticEnergy_zeroProblem {n : ℕ} (viscosity : ℝ) (hviscosity : 0 < viscosity) :
    initialKineticEnergy (zeroProblem n viscosity hviscosity) = 0 := by
  simp [initialKineticEnergy, initialKineticEnergyDensity, zeroProblem,
    IncompressibleFlow.specificKineticEnergy,
    IncompressibleFlow.zeroInitialValueData]

end NavierStokes
