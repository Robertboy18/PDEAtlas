/-
Copyright (c) 2026 LeanPDE Team.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Axisymmetric.TimeProfile
public import PDE.Fluid.Axisymmetric.ReducedNavierStokes
import CAS.ExactTactic

/-!
# Time-profile Laplacian for the reduced axisymmetric equations

The time-profile Laplacian `axisymmetricTimeLaplacian` built from the classical differential
`classicalAxisymmetricTimeDifferential` assigns the same axis value `4∂rr + ∂zz` as the reduced
equations, so on every time slice it equals `axisExtendedRadialFourAxialLaplacian`
(`axisymmetricTimeLaplacian_classical_eq_axisExtended`). Away from the axis both are the ordinary
formula `∂rr + 3r⁻¹∂r + ∂zz`. This is an identity of total expressions; reading the axis value
as a limit requires the regularity and radial parity of
`PDE.Fluid.Axisymmetric.TimeProfileRegularity`.
-/

@[expose] public section

open PDE.FDeriv
open PDE.CoordinateSystems (meridianR)

namespace AxisymmetricFlow

/-- The concrete classical Laplacian agrees with LeanPDE's axis-extended
radial-four-plus-axial operator on every time slice. -/
theorem axisymmetricTimeLaplacian_classical_eq_axisExtended
    (f : TimeProfile) (x : ℝ^2) (t : ℝ) :
    axisymmetricTimeLaplacian classicalAxisymmetricTimeDifferential f x t =
      axisExtendedRadialFourAxialLaplacian
        (fun y ↦ f y t) x := by
  by_cases hx : meridianR x = 0
  · change x (0 : Fin 2) = 0 at hx
    simp only [axisymmetricTimeLaplacian, classicalAxisymmetricTimeDifferential,
      axisExtendedRadialFourAxialLaplacian, meridianR, hx, ↓reduceIte]
    cas
  · change x (0 : Fin 2) ≠ 0 at hx
    simp only [axisymmetricTimeLaplacian, classicalAxisymmetricTimeDifferential,
      axisExtendedRadialFourAxialLaplacian, radialFourAxialLaplacian, meridianR, hx, ↓reduceIte]
    cas using hx

end AxisymmetricFlow
