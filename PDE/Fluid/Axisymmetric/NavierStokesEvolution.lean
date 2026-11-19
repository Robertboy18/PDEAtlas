/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.CartesianDiffusion

/-!
# Cartesian Navier–Stokes evolution from squared-radius variables

The division-free Euler reconstruction of `PhysicalEvolution` extends to the viscous equations. In
the squared-radius spacetime variables `(t, s, z)`, `s = r²`, the reduced unknowns are the swirl
coefficient `U = u_θ / r`, the azimuthal-vorticity coefficient `Ω = ω_θ / r`, and the normalised
streamfunction `Ψ = ψ / r²`. The reduced Navier–Stokes system reads

```text
D_t U = 2 U Ψ_z + ν (8 ∂_s + 4 s ∂_ss + ∂_zz) U,
D_t Ω = 2 U U_z + ν (8 ∂_s + 4 s ∂_ss + ∂_zz) Ω,
```

where `D_t = ∂_t - 2 s Ψ_z ∂_s + (2Ψ + 2 s Ψ_s) ∂_z` is the material derivative along the
reconstructed meridional velocity written in `(s, z)`, and the operator in parentheses is the
radial-four-plus-axial Laplacian `∂ᵣᵣ + 3r⁻¹∂ᵣ + ∂_zz` of `ReducedNavierStokes` expressed in
`s` (`spacetimeSquaredRadiusDiffusion`). The two residuals below are the differences of the two
sides; they are the Euler residuals of `PhysicalEvolution` minus `ν` times the diffusion.

The main theorem shows that if both residuals vanish identically for globally smooth profiles,
then the Cartesian Navier–Stokes vorticity transport residual of the reconstructed velocity and
the independently reconstructed vorticity `spacetimeAxisymmetricVorticityFromCoefficients U Ω`
vanishes on all of `ℝ^4`. Because the profiles are globally smooth functions of `(t, s, z)`, they
are in particular defined and smooth for negative `s`, which is what makes the formulas valid on
the symmetry axis; see `LocalEvolution` for the corresponding condition on open profile domains.
The stream equation `Ω = -spacetimeSquaredRadiusDiffusion Ψ` is not assumed here; it is needed
separately to identify the reconstructed vorticity with the curl of the reconstructed velocity.

## Main results

* `squaredRadiusNavierStokesSwirlResidual`, `squaredRadiusNavierStokesVorticityResidual`: the
  two reduced viscous residuals.
* `navierStokesVorticityTransportResidual_axisymmetric`: the Cartesian viscous vorticity residual
  is the two-coefficient reconstruction of the reduced residuals.
* `navierStokesVorticityTransportResidual_axisymmetric_eq_zero`: smooth solutions of the two
  reduced viscous equations give the Cartesian vorticity transport equation.

## References

* T. Y. Hou and C. Li, "Dynamic stability of the three-dimensional axisymmetric Navier-Stokes
  equations with swirl", Comm. Pure Appl. Math. 61 (2008), no. 5, 661-697, for the reduced
  equations, which we rewrite in the squared radius.
  <https://doi.org/10.1002/cpa.20212>
-/

@[expose] public section

open PDE (SpaceTime)

namespace AxisymmetricFlow

open EuclideanSpace
open PDE.Common
open PDE.CoordinateSystems

set_option linter.missingDocs true

noncomputable section

/-- Reduced Navier–Stokes swirl residual in squared-radius spacetime
coordinates. -/
def squaredRadiusNavierStokesSwirlResidual
    (ν : ℝ) (U Ψ : SpaceTime 2 → ℝ) (q : SpaceTime 2) : ℝ :=
  squaredRadiusEulerSwirlResidual U Ψ q -
    ν * spacetimeSquaredRadiusDiffusion U q

/-- Reduced Navier–Stokes azimuthal-vorticity residual in squared-radius
spacetime coordinates. -/
def squaredRadiusNavierStokesVorticityResidual
    (ν : ℝ) (U Ω Ψ : SpaceTime 2 → ℝ) (q : SpaceTime 2) : ℝ :=
  squaredRadiusEulerVorticityResidual U Ω Ψ q -
    ν * spacetimeSquaredRadiusDiffusion Ω q

/-- The reduced Euler swirl residual preserves smoothness. -/
theorem contDiff_squaredRadiusEulerSwirlResidual
    {U Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (squaredRadiusEulerSwirlResidual U Ψ) := by
  unfold squaredRadiusEulerSwirlResidual
  exact (contDiff_squaredRadiusMaterialDerivative (m := ⊤) hΨ hU).sub
    ((contDiff_const.mul hU).mul (PDE.contDiff_top_partialDeriv hΨ))

/-- The reduced Navier–Stokes swirl residual preserves smoothness. -/
theorem contDiff_squaredRadiusNavierStokesSwirlResidual
    {ν : ℝ} {U Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (squaredRadiusNavierStokesSwirlResidual ν U Ψ) := by
  unfold squaredRadiusNavierStokesSwirlResidual
  exact (contDiff_squaredRadiusEulerSwirlResidual hU hΨ).sub
    (contDiff_const.mul (contDiff_spacetimeSquaredRadiusDiffusion hU))

/-- Differentiating the viscous swirl residual separates the Euler and
diffusion contributions. -/
theorem partialDeriv_squaredRadiusNavierStokesSwirlResidual
    {ν : ℝ} {U Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (i : Fin 3) (q : SpaceTime 2) :
    (∂[i] (squaredRadiusNavierStokesSwirlResidual ν U Ψ)) q =
      (∂[i] (squaredRadiusEulerSwirlResidual U Ψ)) q -
        ν * (∂[i] (spacetimeSquaredRadiusDiffusion U)) q := by
  unfold squaredRadiusNavierStokesSwirlResidual
  rw [PDE.partialDeriv_sub
    ((contDiff_squaredRadiusEulerSwirlResidual hU hΨ).differentiable
      (by simp)).differentiableAt
    ((contDiff_const.mul
      (contDiff_spacetimeSquaredRadiusDiffusion hU)).differentiable
        (by simp)).differentiableAt]
  have hscale : (∂[i]
      (fun p ↦ ν * spacetimeSquaredRadiusDiffusion U p)) q =
      ν * (∂[i] (spacetimeSquaredRadiusDiffusion U)) q := by
    simpa [smul_eq_mul] using
      (PDE.partialDeriv_const_smul (n := 3) (E := ℝ) (c := ν)
        (i := i) (f := spacetimeSquaredRadiusDiffusion U) (x := q))
  rw [hscale]

/-- First Cartesian component of the Navier–Stokes vorticity residual. -/
theorem navierStokesVorticityTransportResidual_axisymmetric_apply_zero
    {ν : ℝ} {U Ω Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.vorticityTransportResidual 3 ν
        (spacetimeAxisymmetricVelocity U Ψ)
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
        (timeSpaceCons t x) 0 =
      -x 0 * (∂[(2 : Fin 3)]
          (squaredRadiusNavierStokesSwirlResidual ν U Ψ))
          (timeSpaceCons t (squaredCylindricalMap x)) -
        x 1 * squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ
          (timeSpaceCons t (squaredCylindricalMap x)) := by
  have heuler := eulerVorticityTransportResidual_axisymmetric_apply_zero
    (hU.of_le (by simp)) (hΩ.of_le (by simp)) (hΨ.of_le (by simp)) t x
  have hlap := spatialVectorLaplacian_vorticityFromCoefficients_apply_zero
    hU hΩ t x
  have hsplit :
      IncompressibleFlow.vorticityTransportResidual 3 ν
          (spacetimeAxisymmetricVelocity U Ψ)
          (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
          (timeSpaceCons t x) 0 =
        IncompressibleFlow.vorticityTransportResidual 3 0
            (spacetimeAxisymmetricVelocity U Ψ)
            (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
            (timeSpaceCons t x) 0 -
          ν * IncompressibleFlow.spatialVectorLaplacian 3
            (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
            (timeSpaceCons t x) 0 := by
    simp [IncompressibleFlow.vorticityTransportResidual]
  rw [hsplit, heuler, hlap]
  rw [spacetimeSquaredRadiusDiffusion_partialDeriv_two hU]
  rw [partialDeriv_squaredRadiusNavierStokesSwirlResidual hU hΨ]
  unfold squaredRadiusNavierStokesVorticityResidual
  ring

/-- Second Cartesian component of the Navier–Stokes vorticity residual. -/
theorem navierStokesVorticityTransportResidual_axisymmetric_apply_one
    {ν : ℝ} {U Ω Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.vorticityTransportResidual 3 ν
        (spacetimeAxisymmetricVelocity U Ψ)
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
        (timeSpaceCons t x) 1 =
      -x 1 * (∂[(2 : Fin 3)]
          (squaredRadiusNavierStokesSwirlResidual ν U Ψ))
          (timeSpaceCons t (squaredCylindricalMap x)) +
        x 0 * squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ
          (timeSpaceCons t (squaredCylindricalMap x)) := by
  have heuler := eulerVorticityTransportResidual_axisymmetric_apply_one
    (hU.of_le (by simp)) (hΩ.of_le (by simp)) (hΨ.of_le (by simp)) t x
  have hlap := spatialVectorLaplacian_vorticityFromCoefficients_apply_one
    hU hΩ t x
  have hsplit :
      IncompressibleFlow.vorticityTransportResidual 3 ν
          (spacetimeAxisymmetricVelocity U Ψ)
          (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
          (timeSpaceCons t x) 1 =
        IncompressibleFlow.vorticityTransportResidual 3 0
            (spacetimeAxisymmetricVelocity U Ψ)
            (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
            (timeSpaceCons t x) 1 -
          ν * IncompressibleFlow.spatialVectorLaplacian 3
            (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
            (timeSpaceCons t x) 1 := by
    simp [IncompressibleFlow.vorticityTransportResidual]
  rw [hsplit, heuler, hlap]
  rw [spacetimeSquaredRadiusDiffusion_partialDeriv_two hU]
  rw [partialDeriv_squaredRadiusNavierStokesSwirlResidual hU hΨ]
  unfold squaredRadiusNavierStokesVorticityResidual
  ring

/-- Axial Cartesian component of the Navier–Stokes vorticity residual. -/
theorem navierStokesVorticityTransportResidual_axisymmetric_apply_two
    {ν : ℝ} {U Ω Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.vorticityTransportResidual 3 ν
        (spacetimeAxisymmetricVelocity U Ψ)
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
        (timeSpaceCons t x) 2 =
      2 * squaredRadiusNavierStokesSwirlResidual ν U Ψ
          (timeSpaceCons t (squaredCylindricalMap x)) +
        2 * cylindricalRadiusSq x * (∂[(1 : Fin 3)]
          (squaredRadiusNavierStokesSwirlResidual ν U Ψ))
          (timeSpaceCons t (squaredCylindricalMap x)) := by
  have heuler := eulerVorticityTransportResidual_axisymmetric_apply_two
    (Ω := Ω) (hU.of_le (by simp)) (hΨ.of_le (by simp)) t x
  have hlap := spatialVectorLaplacian_vorticityFromCoefficients_apply_two
    (U := U) (Ω := Ω) hU t x
  have hsplit :
      IncompressibleFlow.vorticityTransportResidual 3 ν
          (spacetimeAxisymmetricVelocity U Ψ)
          (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
          (timeSpaceCons t x) 2 =
        IncompressibleFlow.vorticityTransportResidual 3 0
            (spacetimeAxisymmetricVelocity U Ψ)
            (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
            (timeSpaceCons t x) 2 -
          ν * IncompressibleFlow.spatialVectorLaplacian 3
            (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
            (timeSpaceCons t x) 2 := by
    simp [IncompressibleFlow.vorticityTransportResidual]
  rw [hsplit, heuler, hlap]
  rw [partialDeriv_squaredRadiusNavierStokesSwirlResidual hU hΨ]
  unfold squaredRadiusNavierStokesSwirlResidual
  ring

/-- The full Cartesian Navier–Stokes vorticity residual is the division-free
reconstruction of the two viscous reduced residuals. -/
theorem navierStokesVorticityTransportResidual_axisymmetric
    {ν : ℝ} {U Ω Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.vorticityTransportResidual 3 ν
        (spacetimeAxisymmetricVelocity U Ψ)
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
        (timeSpaceCons t x) =
      spacetimeAxisymmetricVorticityFromCoefficients
        (squaredRadiusNavierStokesSwirlResidual ν U Ψ)
        (squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ)
        (timeSpaceCons t x) := by
  ext i
  fin_cases i
  · change IncompressibleFlow.vorticityTransportResidual 3 ν
      (spacetimeAxisymmetricVelocity U Ψ)
      (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
      (timeSpaceCons t x) 0 =
        spacetimeAxisymmetricVorticityFromCoefficients
          (squaredRadiusNavierStokesSwirlResidual ν U Ψ)
          (squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ)
          (timeSpaceCons t x) 0
    rw [spacetimeAxisymmetricVorticityFromCoefficients_timeSpaceCons_apply_zero]
    simp only [spacetimeSquaredCylindricalLift_timeSpaceCons,
      squaredCylindricalLift, profileSlice_apply]
    exact navierStokesVorticityTransportResidual_axisymmetric_apply_zero
      hU hΩ hΨ t x
  · change IncompressibleFlow.vorticityTransportResidual 3 ν
      (spacetimeAxisymmetricVelocity U Ψ)
      (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
      (timeSpaceCons t x) 1 =
        spacetimeAxisymmetricVorticityFromCoefficients
          (squaredRadiusNavierStokesSwirlResidual ν U Ψ)
          (squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ)
          (timeSpaceCons t x) 1
    rw [spacetimeAxisymmetricVorticityFromCoefficients_timeSpaceCons_apply_one]
    simp only [spacetimeSquaredCylindricalLift_timeSpaceCons,
      squaredCylindricalLift, profileSlice_apply]
    exact navierStokesVorticityTransportResidual_axisymmetric_apply_one
      hU hΩ hΨ t x
  · change IncompressibleFlow.vorticityTransportResidual 3 ν
      (spacetimeAxisymmetricVelocity U Ψ)
      (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
      (timeSpaceCons t x) 2 =
        spacetimeAxisymmetricVorticityFromCoefficients
          (squaredRadiusNavierStokesSwirlResidual ν U Ψ)
          (squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ)
          (timeSpaceCons t x) 2
    rw [spacetimeAxisymmetricVorticityFromCoefficients_timeSpaceCons_apply_two]
    simp only [spacetimeSquaredCylindricalLift_timeSpaceCons,
      squaredCylindricalLift, profileSlice_apply]
    exact navierStokesVorticityTransportResidual_axisymmetric_apply_two
      (Ω := Ω) (hU.of_le (by simp)) (hΨ.of_le (by simp)) t x

/-- Smooth solutions of the two reduced viscous equations give the Cartesian
transport equation for the independently reconstructed vorticity. Identifying
this field with the velocity's curl requires the reduced stream equation. -/
theorem navierStokesVorticityTransportResidual_axisymmetric_eq_zero
    {ν : ℝ} {U Ω Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hSwirl : squaredRadiusNavierStokesSwirlResidual ν U Ψ = 0)
    (hVorticity : squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ = 0) :
    IncompressibleFlow.vorticityTransportResidual 3 ν
        (spacetimeAxisymmetricVelocity U Ψ)
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω) = 0 := by
  funext xt
  rw [← timeSpaceCons_spatialPart xt]
  rw [navierStokesVorticityTransportResidual_axisymmetric hU hΩ hΨ]
  rw [hSwirl, hVorticity]
  have hzero (i : Fin 3) (q : SpaceTime 2) :
      (∂[i] (0 : SpaceTime 2 → ℝ)) q = 0 := by
    change (∂[i] (fun _ : SpaceTime 2 ↦ (0 : ℝ))) q = 0
    exact PDE.partialDeriv_const 0
  have hzeroFunction (i : Fin 3) :
      (∂[i] (0 : SpaceTime 2 → ℝ)) = 0 := by
    funext q
    exact hzero i q
  unfold spacetimeAxisymmetricVorticityFromCoefficients
  rw [hzeroFunction (1 : Fin 3), hzeroFunction (2 : Fin 3)]
  ext i
  fin_cases i <;> simp [spacetimeSquaredCylindricalLift]

end

end AxisymmetricFlow
