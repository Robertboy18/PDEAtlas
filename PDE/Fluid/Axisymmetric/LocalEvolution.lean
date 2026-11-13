/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.NavierStokesEvolution
public import PDE.Fluid.NavierStokes.Operators
import PDE.Analysis.Calculus.LocalExtension
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import PDE.Fluid.Incompressible.Locality
import PDE.Fluid.NavierStokes.PressureFromVorticity

/-!
# Local Cartesian evolution from squared-radius profiles

The bridge from the reduced axisymmetric equations in `(t, s, z)` to the Cartesian Navier–Stokes
vorticity equation on `ℝ^4` is proved in `NavierStokesEvolution` for profiles that are globally
`C^∞`. Here the profiles are only assumed smooth on an open set `D` of `(t, s, z)` space,
typically `(-∞, T) × ℝ × ℝ`, so they need not extend through a singular time `T`. The Euler
transport identities require only C² swirl and streamfunction and C¹ vorticity; the viscous
identities assume `C^∞` on `D`. The reduced operators, the diffusion operator, and the Cartesian
vorticity reconstruction all depend only on the germ of the profiles at the evaluation point, so
a profile that is `C^∞` on an open set `D` may be replaced near any point of `D` by a globally
smooth, compactly supported function with the same germ (Mathlib's
`ContDiffOn.exists_contDiff_compactSupport_eventuallyEq`). The global identities then apply
pointwise on `D`.

A Cartesian point `xt = (t, x)` is covered when `(t, |x'|², x₃) ∈ D`, where `x' = (x₁, x₂)`. Axis
points are therefore reached only if `D` contains a neighbourhood of `s = 0`, so that the
profiles are defined and smooth for slightly negative squared radius as well. For profiles that
arise from a smooth axisymmetric flow this is the classical requirement that the meridional
fields be even in `r`, since a smooth even function of `r` is a smooth function of `r²`.

## Main results

* `*_eventuallyEq`: the reduced residuals, the diffusion operator, and the vorticity
  reconstruction respect eventual equality of profiles.
* `spatialFieldDivergence_velocitySlice_eq_zero_of_contDiffOn`: the reconstructed velocity is
  divergence free at every covered point.
* `spatialCurl_velocitySlice_eq_vorticityFromCoefficients_of_contDiffOn`: under the reduced
  stream equation `Ω = -(8Ψ_s + 4sΨ_ss + Ψ_zz)` on `D`, the independent vorticity
  reconstruction is the curl of the reconstructed velocity.
* `eulerVorticityTransportResidual_axisymmetric_eq_zero_on`: finite regularity and the reduced
  Euler equations give Cartesian transport, without taking the viscous branch.
* `navierStokesVorticityTransportResidual_axisymmetric_eq_zero_on`: the reduced viscous swirl
  and vorticity equations on `D` give the Cartesian vorticity transport equation at every covered
  point; `ν = 0` is the Euler case.
* `exists_pressure_momentum_equation_of_reducedEquationsOn`: with the stream equation as well, a
  pressure exists on each open convex spatial slice for which the Navier–Stokes momentum equation
  holds there.
-/

open scoped Gradient

@[expose] public section

open PDE (time)

namespace AxisymmetricFlow

open EuclideanSpace Filter
open PDE.Common
open scoped Topology

/-- The squared-radius material derivative depends only on the two profile germs. -/
theorem squaredRadiusMaterialDerivative_eventuallyEq
    {Ψ Ψ' F F' : ℝ^3 → ℝ} {q : ℝ^3}
    (hΨ : Ψ =ᶠ[𝓝 q] Ψ') (hF : F =ᶠ[𝓝 q] F') :
    squaredRadiusMaterialDerivative Ψ F =ᶠ[𝓝 q] squaredRadiusMaterialDerivative Ψ' F' := by
  filter_upwards [hΨ, hΨ.partialDeriv 1, hΨ.partialDeriv 2,
    hF.partialDeriv 0, hF.partialDeriv 1, hF.partialDeriv 2]
    with y hyΨ hyΨS hyΨZ hyFt hyFS hyFZ
  simp only [squaredRadiusMaterialDerivative, hyΨ, hyΨS, hyΨZ, hyFt, hyFS, hyFZ]

/-- The reduced Euler swirl residual depends only on the profile germs. -/
theorem squaredRadiusEulerSwirlResidual_eventuallyEq
    {U U' Ψ Ψ' : ℝ^3 → ℝ} {q : ℝ^3}
    (hU : U =ᶠ[𝓝 q] U') (hΨ : Ψ =ᶠ[𝓝 q] Ψ') :
    squaredRadiusEulerSwirlResidual U Ψ =ᶠ[𝓝 q] squaredRadiusEulerSwirlResidual U' Ψ' := by
  filter_upwards [squaredRadiusMaterialDerivative_eventuallyEq hΨ hU,
    hU, hΨ.partialDeriv 2] with y hmat hyU hyΨZ
  simp only [squaredRadiusEulerSwirlResidual, hmat, hyU, hyΨZ]

/-- The reduced Euler vorticity residual depends only on the profile germs. -/
theorem squaredRadiusEulerVorticityResidual_eventuallyEq
    {U U' Ω Ω' Ψ Ψ' : ℝ^3 → ℝ} {q : ℝ^3}
    (hU : U =ᶠ[𝓝 q] U') (hΩ : Ω =ᶠ[𝓝 q] Ω') (hΨ : Ψ =ᶠ[𝓝 q] Ψ') :
    squaredRadiusEulerVorticityResidual U Ω Ψ =ᶠ[𝓝 q]
      squaredRadiusEulerVorticityResidual U' Ω' Ψ' := by
  filter_upwards [squaredRadiusMaterialDerivative_eventuallyEq hΨ hΩ,
    hU, hU.partialDeriv 2] with y hmat hyU hyUZ
  simp only [squaredRadiusEulerVorticityResidual, hmat, hyU, hyUZ]

/-- The regular squared-radius diffusion operator depends only on the profile germ. -/
theorem spacetimeSquaredRadiusDiffusion_eventuallyEq
    {F G : ℝ^3 → ℝ} {q : ℝ^3} (h : F =ᶠ[𝓝 q] G) :
    spacetimeSquaredRadiusDiffusion F =ᶠ[𝓝 q] spacetimeSquaredRadiusDiffusion G := by
  filter_upwards [h.partialDeriv 1, (h.partialDeriv 1).partialDeriv 1,
    (h.partialDeriv 2).partialDeriv 2] with y hyS hySS hyZZ
  simp only [spacetimeSquaredRadiusDiffusion, hyS, hySS, hyZZ]

/-- The reduced viscous swirl residual depends only on the profile germs. -/
theorem squaredRadiusNavierStokesSwirlResidual_eventuallyEq
    (ν : ℝ) {U U' Ψ Ψ' : ℝ^3 → ℝ} {q : ℝ^3}
    (hU : U =ᶠ[𝓝 q] U') (hΨ : Ψ =ᶠ[𝓝 q] Ψ') :
    squaredRadiusNavierStokesSwirlResidual ν U Ψ =ᶠ[𝓝 q]
      squaredRadiusNavierStokesSwirlResidual ν U' Ψ' := by
  filter_upwards [squaredRadiusEulerSwirlResidual_eventuallyEq hU hΨ,
    spacetimeSquaredRadiusDiffusion_eventuallyEq hU] with y heuler hdiff
  simp only [squaredRadiusNavierStokesSwirlResidual, heuler, hdiff]

/-- The reduced viscous vorticity residual depends only on the profile germs. -/
theorem squaredRadiusNavierStokesVorticityResidual_eventuallyEq
    (ν : ℝ) {U U' Ω Ω' Ψ Ψ' : ℝ^3 → ℝ} {q : ℝ^3}
    (hU : U =ᶠ[𝓝 q] U') (hΩ : Ω =ᶠ[𝓝 q] Ω') (hΨ : Ψ =ᶠ[𝓝 q] Ψ') :
    squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ =ᶠ[𝓝 q]
      squaredRadiusNavierStokesVorticityResidual ν U' Ω' Ψ' := by
  filter_upwards [squaredRadiusEulerVorticityResidual_eventuallyEq hU hΩ hΨ,
    spacetimeSquaredRadiusDiffusion_eventuallyEq hΩ] with y heuler hdiff
  simp only [squaredRadiusNavierStokesVorticityResidual, heuler, hdiff]

/-- Equal swirl and vorticity coefficient germs reconstruct equal Cartesian vorticity germs. -/
theorem spacetimeAxisymmetricVorticityFromCoefficients_eventuallyEq
    {U U' Ω Ω' : ℝ^3 → ℝ} {xt : ℝ^4}
    (hU : U =ᶠ[𝓝 (spacetimeSquaredCylindricalMap xt)] U')
    (hΩ : Ω =ᶠ[𝓝 (spacetimeSquaredCylindricalMap xt)] Ω') :
    spacetimeAxisymmetricVorticityFromCoefficients U Ω =ᶠ[𝓝 xt]
      spacetimeAxisymmetricVorticityFromCoefficients U' Ω' := by
  have hmap : ContinuousAt spacetimeSquaredCylindricalMap xt :=
    (contDiff_spacetimeSquaredCylindricalMap (n := 0)).continuous.continuousAt
  filter_upwards [hU.comp_tendsto hmap, hΩ.comp_tendsto hmap,
    (hU.partialDeriv 1).comp_tendsto hmap, (hU.partialDeriv 2).comp_tendsto hmap]
    with y hyU hyΩ hyUS hyUZ
  simp only [Function.comp_def] at hyU hyΩ hyUS hyUZ
  simp only [spacetimeAxisymmetricVorticityFromCoefficients,
    spacetimeSquaredCylindricalLift, hyU, hyΩ, hyUS, hyUZ]

/-- A reconstruction with C¹ swirl and C² streamfunction on an open set `D` is divergence free
on each spatial slice at every point whose squared-radius image lies in `D`. Axis points are
included only when `D` contains a neighbourhood of `s = 0`, that is, when the profiles extend
smoothly to negative squared radius. -/
theorem spatialFieldDivergence_velocitySlice_eq_zero_of_contDiffOn
    {U Ψ : ℝ^3 → ℝ} {D : Set (ℝ^3)}
    (hD : IsOpen D) (hU : ContDiffOn ℝ 1 U D)
    (hΨ : ContDiffOn ℝ 2 Ψ D)
    (t : ℝ) (x : ℝ^3) (hx : timeSpaceCons t (squaredCylindricalMap x) ∈ D) :
    ∇· (IncompressibleFlow.velocitySlice (spacetimeAxisymmetricVelocity U Ψ) t) x = 0 := by
  have hxt : spacetimeSquaredCylindricalMap (timeSpaceCons t x) ∈ D := by simpa using hx
  obtain ⟨U', hU', _hUc, hUeq⟩ :=
    hU.exists_contDiff_compactSupport_eventuallyEq hD hxt
  obtain ⟨Ψ', hΨ', _hΨc, hΨeq⟩ :=
    hΨ.exists_contDiff_compactSupport_eventuallyEq hD hxt
  have hvelocity := spacetimeAxisymmetricVelocity_eventuallyEq hUeq hΨeq
  have hslice : IncompressibleFlow.velocitySlice (spacetimeAxisymmetricVelocity U Ψ) t =ᶠ[𝓝 x]
      IncompressibleFlow.velocitySlice (spacetimeAxisymmetricVelocity U' Ψ') t :=
    hvelocity.comp_tendsto (contDiff_timeSpaceCons_spatial 3 t (m := 0)).continuous.continuousAt
  exact (IncompressibleFlow.spatialFieldDivergence_eventuallyEq hslice).eq_of_nhds.trans
    (spatialFieldDivergence_velocitySlice_spacetimeAxisymmetricVelocity_eq_zero hU' hΨ' t x)

/-- The local reduced stream equation identifies the independent vorticity coefficients with
the spatial curl of the reconstructed velocity. -/
theorem spatialCurl_velocitySlice_eq_vorticityFromCoefficients_of_contDiffOn
    {U Ω Ψ : ℝ^3 → ℝ} {D : Set (ℝ^3)}
    (hD : IsOpen D) (hU : ContDiffOn ℝ 1 U D)
    (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hstream : ∀ q ∈ D, Ω q = -spacetimeSquaredRadiusDiffusion Ψ q)
    (t : ℝ) (x : ℝ^3) (hx : timeSpaceCons t (squaredCylindricalMap x) ∈ D) :
    IncompressibleFlow.spatialCurl
        (IncompressibleFlow.velocitySlice (spacetimeAxisymmetricVelocity U Ψ) t) x =
      spacetimeAxisymmetricVorticityFromCoefficients U Ω (timeSpaceCons t x) := by
  have hxt : spacetimeSquaredCylindricalMap (timeSpaceCons t x) ∈ D := by simpa using hx
  obtain ⟨U', hU', _hUc, hUeq⟩ :=
    hU.exists_contDiff_compactSupport_eventuallyEq hD hxt
  obtain ⟨Ψ', hΨ', _hΨc, hΨeq⟩ :=
    hΨ.exists_contDiff_compactSupport_eventuallyEq hD hxt
  have hvelocity := spacetimeAxisymmetricVelocity_eventuallyEq hUeq hΨeq
  have hslice : IncompressibleFlow.velocitySlice (spacetimeAxisymmetricVelocity U Ψ) t =ᶠ[𝓝 x]
      IncompressibleFlow.velocitySlice (spacetimeAxisymmetricVelocity U' Ψ') t :=
    hvelocity.comp_tendsto (contDiff_timeSpaceCons_spatial 3 t (m := 0)).continuous.continuousAt
  have hΩeq : Ω =ᶠ[𝓝 (spacetimeSquaredCylindricalMap (timeSpaceCons t x))]
      fun q ↦ -spacetimeSquaredRadiusDiffusion Ψ' q := by
    filter_upwards [hD.mem_nhds hxt, spacetimeSquaredRadiusDiffusion_eventuallyEq hΨeq]
      with q hq hdiff
    rw [hstream q hq, hdiff]
  rw [(IncompressibleFlow.spatialCurl_eventuallyEq hslice).eq_of_nhds,
    spatialCurl_velocitySlice_spacetimeAxisymmetricVelocity,
    spacetimeAxisymmetricVorticity_eq_vorticityFromCoefficients hU' hΨ']
  exact (spacetimeAxisymmetricVorticityFromCoefficients_eventuallyEq hUeq hΩeq).eq_of_nhds.symm

/-- On an open profile domain, the Cartesian viscous vorticity residual is the reconstruction
of the reduced residuals. The profiles need not extend smoothly through the domain boundary. -/
theorem navierStokesVorticityTransportResidual_axisymmetric_of_contDiffOn
    {ν : ℝ} {U Ω Ψ : ℝ^3 → ℝ} {D : Set (ℝ^3)} {xt : ℝ^4}
    (hD : IsOpen D) (hxt : spacetimeSquaredCylindricalMap xt ∈ D)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U D)
    (hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω D)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ D) :
    IncompressibleFlow.vorticityTransportResidual 3 ν
        (spacetimeAxisymmetricVelocity U Ψ)
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω) xt =
      spacetimeAxisymmetricVorticityFromCoefficients
        (squaredRadiusNavierStokesSwirlResidual ν U Ψ)
        (squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ) xt := by
  obtain ⟨U', hU', _hUc, hUeq⟩ :=
    hU.exists_contDiff_compactSupport_eventuallyEq hD hxt
  obtain ⟨Ω', hΩ', _hΩc, hΩeq⟩ :=
    hΩ.exists_contDiff_compactSupport_eventuallyEq hD hxt
  obtain ⟨Ψ', hΨ', _hΨc, hΨeq⟩ :=
    hΨ.exists_contDiff_compactSupport_eventuallyEq hD hxt
  have hvelocity := spacetimeAxisymmetricVelocity_eventuallyEq hUeq hΨeq
  have hvorticity := spacetimeAxisymmetricVorticityFromCoefficients_eventuallyEq hUeq hΩeq
  calc
    _ = IncompressibleFlow.vorticityTransportResidual 3 ν
        (spacetimeAxisymmetricVelocity U' Ψ')
        (spacetimeAxisymmetricVorticityFromCoefficients U' Ω') xt :=
      (IncompressibleFlow.vorticityTransportResidual_eventuallyEq ν hvelocity hvorticity).eq_of_nhds
    _ = spacetimeAxisymmetricVorticityFromCoefficients
        (squaredRadiusNavierStokesSwirlResidual ν U' Ψ')
        (squaredRadiusNavierStokesVorticityResidual ν U' Ω' Ψ') xt := by
      simpa using navierStokesVorticityTransportResidual_axisymmetric
        hU' hΩ' hΨ' (time xt) (spatialPart xt)
    _ = _ := (spacetimeAxisymmetricVorticityFromCoefficients_eventuallyEq
      (squaredRadiusNavierStokesSwirlResidual_eventuallyEq ν hUeq hΨeq)
      (squaredRadiusNavierStokesVorticityResidual_eventuallyEq ν hUeq hΩeq hΨeq)).eq_of_nhds.symm

/-- Reduced viscous equations on an open profile domain `D` give the Cartesian vorticity equation
at every spacetime point whose `(t, s, z)` image lies in `D`. Axis points are covered exactly when
`D` contains a neighbourhood of `s = 0`, so the profiles must be smooth for slightly negative
squared radius as well; this is the even-in-`r` condition of classical axisymmetric flow. The
stream equation identifying this vorticity with curl is a separate condition. Setting viscosity
to zero gives the Euler transport equation. -/
theorem navierStokesVorticityTransportResidual_axisymmetric_eq_zero_on
    {ν : ℝ} {U Ω Ψ : ℝ^3 → ℝ} {D : Set (ℝ^3)}
    (hD : IsOpen D)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U D)
    (hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω D)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ D)
    (hSwirl : ∀ q ∈ D, squaredRadiusNavierStokesSwirlResidual ν U Ψ q = 0)
    (hVorticity : ∀ q ∈ D, squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ q = 0)
    {xt : ℝ^4} (hxt : spacetimeSquaredCylindricalMap xt ∈ D) :
    IncompressibleFlow.vorticityTransportResidual 3 ν
      (spacetimeAxisymmetricVelocity U Ψ)
      (spacetimeAxisymmetricVorticityFromCoefficients U Ω) xt = 0 := by
  rw [navierStokesVorticityTransportResidual_axisymmetric_of_contDiffOn hD hxt hU hΩ hΨ]
  have hs : squaredRadiusNavierStokesSwirlResidual ν U Ψ =ᶠ[
      𝓝 (spacetimeSquaredCylindricalMap xt)] fun _ ↦ 0 := by
    filter_upwards [hD.mem_nhds hxt] with q hq
    exact hSwirl q hq
  have hv : squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ =ᶠ[
      𝓝 (spacetimeSquaredCylindricalMap xt)] fun _ ↦ 0 := by
    filter_upwards [hD.mem_nhds hxt] with q hq
    exact hVorticity q hq
  rw [(spacetimeAxisymmetricVorticityFromCoefficients_eventuallyEq hs hv).eq_of_nhds]
  simp [spacetimeAxisymmetricVorticityFromCoefficients, spacetimeSquaredCylindricalLift,
    PDE.partialDeriv_const, cartesianVector]

/-- On an open profile domain, C² swirl and streamfunction and C¹ vorticity identify the
Cartesian Euler transport residual with the reconstruction of the reduced residuals. -/
theorem eulerVorticityTransportResidual_axisymmetric_of_contDiffOn
    {U Ω Ψ : ℝ^3 → ℝ} {D : Set (ℝ^3)} {xt : ℝ^4}
    (hD : IsOpen D) (hxt : spacetimeSquaredCylindricalMap xt ∈ D)
    (hU : ContDiffOn ℝ 2 U D)
    (hΩ : ContDiffOn ℝ 1 Ω D)
    (hΨ : ContDiffOn ℝ 2 Ψ D) :
    IncompressibleFlow.vorticityTransportResidual 3 0
        (spacetimeAxisymmetricVelocity U Ψ)
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω) xt =
      spacetimeAxisymmetricVorticityFromCoefficients
        (squaredRadiusEulerSwirlResidual U Ψ)
        (squaredRadiusEulerVorticityResidual U Ω Ψ) xt := by
  obtain ⟨U', hU', _hUc, hUeq⟩ :=
    hU.exists_contDiff_compactSupport_eventuallyEq hD hxt
  obtain ⟨Ω', hΩ', _hΩc, hΩeq⟩ :=
    hΩ.exists_contDiff_compactSupport_eventuallyEq hD hxt
  obtain ⟨Ψ', hΨ', _hΨc, hΨeq⟩ :=
    hΨ.exists_contDiff_compactSupport_eventuallyEq hD hxt
  have hvelocity := spacetimeAxisymmetricVelocity_eventuallyEq hUeq hΨeq
  have hvorticity := spacetimeAxisymmetricVorticityFromCoefficients_eventuallyEq hUeq hΩeq
  calc
    _ = IncompressibleFlow.vorticityTransportResidual 3 0
        (spacetimeAxisymmetricVelocity U' Ψ')
        (spacetimeAxisymmetricVorticityFromCoefficients U' Ω') xt :=
      (IncompressibleFlow.vorticityTransportResidual_eventuallyEq 0 hvelocity hvorticity).eq_of_nhds
    _ = spacetimeAxisymmetricVorticityFromCoefficients
        (squaredRadiusEulerSwirlResidual U' Ψ')
        (squaredRadiusEulerVorticityResidual U' Ω' Ψ') xt := by
      simpa only [spacetimeAxisymmetricVorticityFromCoefficients,
        spacetimeSquaredCylindricalLift, spacetimeSquaredCylindricalMap,
        time, timeSpaceCons_spatialPart] using
        eulerVorticityTransportResidual_axisymmetric
        hU' hΩ' hΨ' (time xt) (spatialPart xt)
    _ = _ := (spacetimeAxisymmetricVorticityFromCoefficients_eventuallyEq
      (squaredRadiusEulerSwirlResidual_eventuallyEq hUeq hΨeq)
      (squaredRadiusEulerVorticityResidual_eventuallyEq hUeq hΩeq hΨeq)).eq_of_nhds.symm

/-- The two reduced Euler equations on an open domain imply Cartesian vorticity transport
at finite regularity. The stream equation separately identifies this vorticity with curl. -/
theorem eulerVorticityTransportResidual_axisymmetric_eq_zero_on
    {U Ω Ψ : ℝ^3 → ℝ} {D : Set (ℝ^3)}
    (hD : IsOpen D)
    (hU : ContDiffOn ℝ 2 U D)
    (hΩ : ContDiffOn ℝ 1 Ω D)
    (hΨ : ContDiffOn ℝ 2 Ψ D)
    (hSwirl : ∀ q ∈ D, squaredRadiusEulerSwirlResidual U Ψ q = 0)
    (hVorticity : ∀ q ∈ D, squaredRadiusEulerVorticityResidual U Ω Ψ q = 0)
    {xt : ℝ^4} (hxt : spacetimeSquaredCylindricalMap xt ∈ D) :
    IncompressibleFlow.vorticityTransportResidual 3 0
      (spacetimeAxisymmetricVelocity U Ψ)
      (spacetimeAxisymmetricVorticityFromCoefficients U Ω) xt = 0 := by
  rw [eulerVorticityTransportResidual_axisymmetric_of_contDiffOn hD hxt hU hΩ hΨ]
  have hs : squaredRadiusEulerSwirlResidual U Ψ =ᶠ[
      𝓝 (spacetimeSquaredCylindricalMap xt)] fun _ ↦ 0 := by
    filter_upwards [hD.mem_nhds hxt] with q hq
    exact hSwirl q hq
  have hv : squaredRadiusEulerVorticityResidual U Ω Ψ =ᶠ[
      𝓝 (spacetimeSquaredCylindricalMap xt)] fun _ ↦ 0 := by
    filter_upwards [hD.mem_nhds hxt] with q hq
    exact hVorticity q hq
  rw [(spacetimeAxisymmetricVorticityFromCoefficients_eventuallyEq hs hv).eq_of_nhds]
  simp [spacetimeAxisymmetricVorticityFromCoefficients, spacetimeSquaredCylindricalLift,
    PDE.partialDeriv_const, cartesianVector]

/-- Smooth reduced equations on an open profile domain reconstruct a slice-wise pressure
satisfying the physical momentum equation on each selected open convex spatial slice.

The stream equation supplies the curl, and the two evolution equations supply its
transport. The time set may exclude a singular endpoint. The pressure is constructed separately
on each time slice. -/
theorem exists_pressure_momentum_equation_of_reducedEquationsOn
    {ν : ℝ} {U Ω Ψ : ℝ^3 → ℝ} {D : Set (ℝ^3)}
    (hD : IsOpen D)
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U D)
    (hΩ : ContDiffOn ℝ (⊤ : ℕ∞) Ω D)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ D)
    (hstream : ∀ q ∈ D, Ω q = -spacetimeSquaredRadiusDiffusion Ψ q)
    (hSwirl : ∀ q ∈ D, squaredRadiusNavierStokesSwirlResidual ν U Ψ q = 0)
    (hVorticity : ∀ q ∈ D, squaredRadiusNavierStokesVorticityResidual ν U Ω Ψ q = 0)
    {s : Set (ℝ^3)} (hs : Convex ℝ s) (hso : IsOpen s) (I : Set ℝ)
    (hdom : ∀ t ∈ I, ∀ x ∈ s, timeSpaceCons t (squaredCylindricalMap x) ∈ D) :
    ∃ p : ℝ → ℝ^3 → ℝ, ∀ t ∈ I, ∀ x ∈ s,
      HasGradientAt (p t)
          (NavierStokes.viscousTerm 3 ν (spacetimeAxisymmetricVelocity U Ψ)
              (timeSpaceCons t x) -
            IncompressibleFlow.materialDerivative 3 (spacetimeAxisymmetricVelocity U Ψ)
              (spacetimeAxisymmetricVelocity U Ψ) (timeSpaceCons t x)) x ∧
        IncompressibleFlow.materialDerivative 3 (spacetimeAxisymmetricVelocity U Ψ)
            (spacetimeAxisymmetricVelocity U Ψ) (timeSpaceCons t x) + ∇ (p t) x =
          NavierStokes.viscousTerm 3 ν (spacetimeAxisymmetricVelocity U Ψ)
            (timeSpaceCons t x) := by
  have hregular {xt : ℝ^4} (hxt : spacetimeSquaredCylindricalMap xt ∈ D) :
      ContDiffAt ℝ (⊤ : ℕ∞) (spacetimeAxisymmetricVelocity U Ψ) xt :=
    contDiffAt_top_spacetimeAxisymmetricVelocity
      (hU.contDiffAt (hD.mem_nhds hxt)) (hΨ.contDiffAt (hD.mem_nhds hxt))
  apply IncompressibleFlow.exists_pressure_navierStokes_momentum_equation_of_vectorVorticity
    hs hso I ν (spacetimeAxisymmetricVelocity U Ψ)
  · intro t ht x hx
    exact (hregular (by simpa using hdom t ht x hx)).of_le (WithTop.coe_le_coe.mpr le_top)
  · intro t ht x hx
    change IncompressibleFlow.spatialDivergence 3 _ _ = 0
    rw [← IncompressibleFlow.spatialFieldDivergence_velocitySlice t x
      ((hregular (by simpa using hdom t ht x hx)).differentiableAt (by simp))]
    exact spatialFieldDivergence_velocitySlice_eq_zero_of_contDiffOn
      hD (hU.of_le (by simp)) (hΨ.of_le (by simp)) t x (hdom t ht x hx)
  · intro t ht x hx
    have hxt : spacetimeSquaredCylindricalMap (timeSpaceCons t x) ∈ D := by
      simpa using hdom t ht x hx
    have hcurl : IncompressibleFlow.spacetimeSpatialCurl (spacetimeAxisymmetricVelocity U Ψ)
        =ᶠ[𝓝 (timeSpaceCons t x)] spacetimeAxisymmetricVorticityFromCoefficients U Ω := by
      have hmap : Continuous spacetimeSquaredCylindricalMap :=
        (contDiff_spacetimeSquaredCylindricalMap (n := 0)).continuous
      filter_upwards [(hD.preimage hmap).mem_nhds hxt] with y hy
      simpa [IncompressibleFlow.spacetimeSpatialCurl] using
        spatialCurl_velocitySlice_eq_vorticityFromCoefficients_of_contDiffOn
          hD (hU.of_le (by simp)) (hΨ.of_le (by simp)) hstream (time y) (spatialPart y) hy
    rw [(IncompressibleFlow.vorticityTransportResidual_eventuallyEq ν
      Filter.EventuallyEq.rfl hcurl).eq_of_nhds]
    exact navierStokesVorticityTransportResidual_axisymmetric_eq_zero_on
      hD hU hΩ hΨ hSwirl hVorticity hxt

end AxisymmetricFlow
