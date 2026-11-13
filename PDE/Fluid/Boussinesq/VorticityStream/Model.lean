/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.StreamFunction
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
import PDE.FDeriv.Calculus
import PDE.FDeriv.Reflection.Coordinate

/-!
# Upper-half-plane vorticity–streamfunction Boussinesq model

Chen–Hou's upper-half-plane formulation of the Boussinesq system uses the
following sign convention and equations:

```text
ω_t + u · ∇ω = ∂₁θ,
θ_t + u · ∇θ = 0,
-Δφ = ω,
u = (-∂₂φ, ∂₁φ),
φ(x₁, 0, t) = 0.
```

Here `ω` is the clockwise scalar curl `∂₂u₁ - ∂₁u₂`. This differs by a
sign from the standard counterclockwise planar curl, and the definitions keep
the two apart.

Fields are represented by total functions on `ℝ^2`; equations are imposed
only in the open upper half-plane. Thus the classical regularity predicate
describes finite-order classical extensions of upper-half-plane fields.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2, (2.3a)-(2.3c).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open PDE (laplacian advectiveDerivative)

namespace Boussinesq

open IncompressibleFlow
open PDE.Common
open SobolevSpace

set_option linter.missingDocs true

noncomputable section

/-- Open upper half-plane `{x ∈ ℝ^2 | 0 < x₂}`. -/
def upperHalfPlane : Set (ℝ^2) :=
  coordinateUpperHalfSpace (1 : Fin 2)

/-- The Boussinesq upper half-plane agrees with the canonical half-space in
dimension two. -/
theorem upperHalfPlane_eq_halfSpaceUpper :
    upperHalfPlane = HalfSpace.upper 2 := by
  ext x
  simp [upperHalfPlane, coordinateUpperHalfSpace, HalfSpace.upper,
    PDE.Common.lastIndex]

/-- The closure of the open upper half-plane is the closed upper half-plane. -/
theorem closure_upperHalfPlane :
    closure upperHalfPlane = {x : ℝ^2 | 0 ≤ x 1} := by
  exact closure_coordinateUpperHalfSpace (1 : Fin 2)

/-- The upper half-plane is open. -/
theorem isOpen_upperHalfPlane : IsOpen upperHalfPlane := by
  exact isOpen_coordinateUpperHalfSpace (1 : Fin 2)

/-- Point `(x₁, 0)` on the horizontal boundary. -/
def horizontalBoundaryPoint (x₁ : ℝ) : ℝ^2 :=
  WithLp.toLp 2 ![x₁, 0]

/-- The tangential coordinate of `horizontalBoundaryPoint x₁` is `x₁`. -/
@[simp]
theorem horizontalBoundaryPoint_apply_zero (x₁ : ℝ) :
    horizontalBoundaryPoint x₁ 0 = x₁ := by
  simp [horizontalBoundaryPoint]

/-- The normal coordinate of `horizontalBoundaryPoint x₁` is zero. -/
@[simp]
theorem horizontalBoundaryPoint_apply_one (x₁ : ℝ) :
    horizontalBoundaryPoint x₁ 1 = 0 := by
  simp [horizontalBoundaryPoint]

/-- A horizontal-boundary point belongs to the coordinate hyperplane
`{x₂ = 0}`. -/
theorem horizontalBoundaryPoint_mem_coordinateHyperplane (x₁ : ℝ) :
    horizontalBoundaryPoint x₁ ∈ coordinateHyperplane (1 : Fin 2) := by
  simp [coordinateHyperplane]

/-- A parametrized horizontal-boundary point belongs to the canonical
half-space boundary. -/
theorem horizontalBoundaryPoint_mem_halfSpace_boundary (x₁ : ℝ) :
    horizontalBoundaryPoint x₁ ∈ HalfSpace.boundary 2 := by
  simp [HalfSpace.boundary, PDE.Common.lastIndex]

/-- Every horizontal-boundary point lies in the closure of the open upper
half-plane. -/
theorem horizontalBoundaryPoint_mem_closure_upperHalfPlane (x₁ : ℝ) :
    horizontalBoundaryPoint x₁ ∈ closure upperHalfPlane := by
  rw [closure_upperHalfPlane]
  simp

/-- Vorticity, temperature, and streamfunction in the upper-half-plane model. -/
structure VorticityStreamFields where
  /-- Clockwise scalar vorticity. -/
  vorticity : ℝ^2 → ℝ → ℝ
  /-- Advected temperature or density. -/
  temperature : ℝ^2 → ℝ → ℝ
  /-- Streamfunction determining velocity. -/
  streamFunction : ℝ^2 → ℝ → ℝ

/-- Velocity reconstructed locally from the streamfunction. -/
def vorticityStreamVelocity
    (fields : VorticityStreamFields) (x : ℝ^2) (t : ℝ) : ℝ^2 :=
  planarStreamVelocity (fun y ↦ fields.streamFunction y t) x

/-- The zero vorticity–streamfunction fields. -/
def zeroVorticityStreamFields : VorticityStreamFields where
  vorticity := fun _ _ ↦ 0
  temperature := fun _ _ ↦ 0
  streamFunction := fun _ _ ↦ 0

/-- Classical regularity for whole-plane extensions of the three fields.

Only the upper-half-plane equations consume this regularity. Global spatial
`C¹` regularity of vorticity and temperature follows from joint regularity.
The explicit global `C²` streamfunction hypothesis is stronger and makes the
total Fréchet derivatives agree with the intended classical derivatives,
including at the boundary. -/
structure HasClassicalVorticityStreamRegularityOn
    (fields : VorticityStreamFields) (times : Set ℝ) : Prop where
  /-- Joint first-order regularity of vorticity on the admitted times. -/
  vorticity_contDiffOn :
    ContDiffOn ℝ 1
      (fun xt : ℝ^2 × ℝ ↦ fields.vorticity xt.1 xt.2)
      (Set.univ ×ˢ times)
  /-- Joint first-order regularity of temperature on the admitted times. -/
  temperature_contDiffOn :
    ContDiffOn ℝ 1
      (fun xt : ℝ^2 × ℝ ↦ fields.temperature xt.1 xt.2)
      (Set.univ ×ˢ times)
  /-- Every vorticity time slice is differentiable at admitted times. -/
  vorticity_differentiableAt_time
      {x : ℝ^2} {t : ℝ} (ht : t ∈ times) :
    DifferentiableAt ℝ (fun s ↦ fields.vorticity x s) t
  /-- Every temperature time slice is differentiable at admitted times. -/
  temperature_differentiableAt_time
      {x : ℝ^2} {t : ℝ} (ht : t ∈ times) :
    DifferentiableAt ℝ (fun s ↦ fields.temperature x s) t
  /-- Every admitted streamfunction slice is globally `C²` in space. -/
  streamFunction_spatial_contDiff {t : ℝ} (ht : t ∈ times) :
    ContDiff ℝ 2 (fun x ↦ fields.streamFunction x t)

/-- Every admitted vorticity slice is globally `C¹` in space. -/
theorem HasClassicalVorticityStreamRegularityOn.vorticity_spatial_contDiff
    {fields : VorticityStreamFields} {times : Set ℝ}
    (hregularity : HasClassicalVorticityStreamRegularityOn fields times)
    {t : ℝ} (ht : t ∈ times) :
    ContDiff ℝ 1 (fun x ↦ fields.vorticity x t) := by
  simpa only [Function.comp_def] using
    hregularity.vorticity_contDiffOn.comp_contDiff
      (contDiff_prodMk_left t) (fun x ↦ ⟨Set.mem_univ x, ht⟩)

/-- Every admitted temperature slice is globally `C¹` in space. -/
theorem HasClassicalVorticityStreamRegularityOn.temperature_spatial_contDiff
    {fields : VorticityStreamFields} {times : Set ℝ}
    (hregularity : HasClassicalVorticityStreamRegularityOn fields times)
    {t : ℝ} (ht : t ∈ times) :
    ContDiff ℝ 1 (fun x ↦ fields.temperature x t) := by
  simpa only [Function.comp_def] using
    hregularity.temperature_contDiffOn.comp_contDiff
      (contDiff_prodMk_left t) (fun x ↦ ⟨Set.mem_univ x, ht⟩)

/-- Vorticity transport equation in the open upper half-plane. -/
def SatisfiesVorticityEquationOn
    (fields : VorticityStreamFields) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ upperHalfPlane → t ∈ times →
    deriv (fun s ↦ fields.vorticity x s) t +
        advectiveDerivative
          (fun y ↦ vorticityStreamVelocity fields y t)
          (fun y ↦ fields.vorticity y t) x =
      (∂[(0 : Fin 2)] (fun y ↦ fields.temperature y t)) x

/-- Temperature transport equation in the open upper half-plane. -/
def SatisfiesTemperatureEquationOn
    (fields : VorticityStreamFields) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ upperHalfPlane → t ∈ times →
    deriv (fun s ↦ fields.temperature x s) t +
        advectiveDerivative
          (fun y ↦ vorticityStreamVelocity fields y t)
          (fun y ↦ fields.temperature y t) x = 0

/-- Streamfunction equation `-Δφ = ω` in the open upper half-plane. -/
def SatisfiesStreamFunctionEquationOn
    (fields : VorticityStreamFields) (times : Set ℝ) : Prop :=
  ∀ ⦃x : ℝ^2⦄ ⦃t : ℝ⦄, x ∈ upperHalfPlane → t ∈ times →
    -laplacian (fun y ↦ fields.streamFunction y t) x =
      fields.vorticity x t

/-- Dirichlet streamfunction condition `φ(x₁,0,t)=0`. -/
def HasZeroStreamFunctionBoundaryOn
    (fields : VorticityStreamFields) (times : Set ℝ) : Prop :=
  ∀ (x₁ : ℝ) ⦃t : ℝ⦄, t ∈ times →
    fields.streamFunction (horizontalBoundaryPoint x₁) t = 0

/-- A classical upper-half-plane solution in vorticity–streamfunction variables. -/
structure IsClassicalVorticityStreamSolutionOn
    (fields : VorticityStreamFields) (times : Set ℝ) : Prop where
  /-- Classical spacetime and spatial regularity of the fields. -/
  regularity : HasClassicalVorticityStreamRegularityOn fields times
  /-- Clockwise-vorticity transport in the open upper half-plane. -/
  vorticity_equation : SatisfiesVorticityEquationOn fields times
  /-- Temperature transport in the open upper half-plane. -/
  temperature_equation : SatisfiesTemperatureEquationOn fields times
  /-- Dirichlet Poisson equation for the streamfunction. -/
  streamFunction_equation : SatisfiesStreamFunctionEquationOn fields times
  /-- Zero streamfunction trace on the horizontal boundary. -/
  zero_streamFunction_boundary : HasZeroStreamFunctionBoundaryOn fields times

/-- A differentiable zero boundary trace implies the physical no-flow condition. -/
theorem normalVelocity_eq_zero_on_horizontalBoundary_of_zeroStreamFunction
    (fields : VorticityStreamFields) (times : Set ℝ)
    (hregularity : HasClassicalVorticityStreamRegularityOn fields times)
    (hboundary : HasZeroStreamFunctionBoundaryOn fields times) :
    ∀ (x₁ : ℝ) ⦃t : ℝ⦄, t ∈ times →
      vorticityStreamVelocity fields (horizontalBoundaryPoint x₁) t 1 = 0 := by
  intro x₁ t ht
  rw [show vorticityStreamVelocity fields (horizontalBoundaryPoint x₁) t 1 =
      (∂[(0 : Fin 2)] (fun y ↦ fields.streamFunction y t))
        (horizontalBoundaryPoint x₁) by
    simp [vorticityStreamVelocity]]
  have htrace : VanishesOnCoordinateHyperplane (1 : Fin 2)
      (fun y ↦ fields.streamFunction y t) := by
    intro x hx
    have hxrepr : x = horizontalBoundaryPoint (x 0) := by
      ext i
      fin_cases i
      · simp
      · simpa [coordinateHyperplane] using hx
    rw [hxrepr]
    exact hboundary (x 0) ht
  exact htrace.partialDeriv_eq_zero_of_ne (by decide)
    (horizontalBoundaryPoint_mem_coordinateHyperplane x₁)
    ((hregularity.streamFunction_spatial_contDiff ht).differentiable
      (by norm_num)).differentiableAt

/-- The streamfunction equation identifies `ω` with the clockwise curl of
the reconstructed velocity. -/
theorem spatialPlanarClockwiseVorticity_vorticityStreamVelocity
    (fields : VorticityStreamFields) (times : Set ℝ)
    (hstream : SatisfiesStreamFunctionEquationOn fields times)
    {x : ℝ^2} {t : ℝ} (hx : x ∈ upperHalfPlane) (ht : t ∈ times) :
    spatialPlanarClockwiseVorticity
        (fun y ↦ vorticityStreamVelocity fields y t) x =
      fields.vorticity x t := by
  rw [show (fun y ↦ vorticityStreamVelocity fields y t) =
      planarStreamVelocity (fun y ↦ fields.streamFunction y t) by rfl]
  rw [spatialPlanarClockwiseVorticity_planarStreamVelocity]
  exact hstream hx ht

/-- A classical streamfunction slice generates an incompressible velocity. -/
theorem divergence_vorticityStreamVelocity_eq_zero
    (fields : VorticityStreamFields) (times : Set ℝ)
    (hregularity : HasClassicalVorticityStreamRegularityOn fields times)
    {x : ℝ^2} {t : ℝ} (ht : t ∈ times) :
    ∇· (fun y ↦ vorticityStreamVelocity fields y t) x = 0 := by
  exact divergence_planarStreamVelocity_eq_zero
    (fun y ↦ fields.streamFunction y t)
    (hregularity.streamFunction_spatial_contDiff ht) x

/-- The zero fields solve the upper-half-plane vorticity–streamfunction system. -/
theorem zeroVorticityStreamFields_isClassicalSolutionOn (times : Set ℝ) :
    IsClassicalVorticityStreamSolutionOn zeroVorticityStreamFields times := by
  refine
    { regularity := ?_
      vorticity_equation := ?_
      temperature_equation := ?_
      streamFunction_equation := ?_
      zero_streamFunction_boundary := ?_ }
  · refine
      { vorticity_contDiffOn := by fun_prop
        temperature_contDiffOn := by fun_prop
        vorticity_differentiableAt_time := by
          intro x t ht
          fun_prop
        temperature_differentiableAt_time := by
          intro x t ht
          fun_prop
        streamFunction_spatial_contDiff := by
          intro t ht
          fun_prop }
  · intro x t hx ht
    simp [zeroVorticityStreamFields, vorticityStreamVelocity,
      planarStreamVelocity, advectiveDerivative, PDE.partialDeriv_const]
  · intro x t hx ht
    simp [zeroVorticityStreamFields, vorticityStreamVelocity,
      planarStreamVelocity, advectiveDerivative]
  · intro x t hx ht
    simp [zeroVorticityStreamFields]
  · intro x₁ t ht
    simp [zeroVorticityStreamFields]

end

end Boussinesq
