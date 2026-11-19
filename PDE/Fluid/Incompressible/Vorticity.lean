/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.SpatialFields

/-!
# Vorticity of a velocity field

Pointwise vorticity components for velocity fields on spacetime.

Spacetime is `ℝ^(n + 1)`, coordinate `0` is time, and coordinate `i.succ`
is the `i`-th spatial coordinate. The component

```text
Aᵢⱼ = ∂ⱼuᵢ - ∂ᵢuⱼ
```

of `vorticityTensor` is twice the antisymmetric part of the spatial velocity gradient.
The vorticity two-form has the opposite convention,
`Ωᵢⱼ = ∂ᵢuⱼ - ∂ⱼuᵢ`; `spatialVorticityForm_eq_neg_vorticityTensor` identifies them.
In two space dimensions, `spacetimePlanarVorticity` is the scalar curl `∂₁u₂ - ∂₂u₁`, and
`spatialPlanarVorticity`, `spatialPlanarClockwiseVorticity` are the two sign conventions for a
planar field. In three dimensions `spatialCurl` is the right-handed curl.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2, (2.3a)-(2.3c), p. 5.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace IncompressibleFlow

open EuclideanSpace

set_option linter.missingDocs true

noncomputable section

/-- Counterclockwise scalar curl `∂₁u₂ - ∂₂u₁` of a spatial planar velocity field.

Coordinates `0` and `1` represent the first and second spatial variables. -/
def spatialPlanarVorticity (u : ℝ^2 → ℝ^2) (x : ℝ^2) : ℝ :=
  (∂[(0 : Fin 2)] (fun y ↦ u y 1)) x -
    (∂[(1 : Fin 2)] (fun y ↦ u y 0)) x

/-- Clockwise scalar curl `∂₂u₁ - ∂₁u₂` of a spatial planar velocity field.

This is the sign convention for `ω` in the stream-function formulation of the two-dimensional
Boussinesq equations of Chen and Hou, Part I, (2.3c): `-Δφ = ω`, `u = -∂₂φ`, `v = ∂₁φ`. -/
def spatialPlanarClockwiseVorticity (u : ℝ^2 → ℝ^2) (x : ℝ^2) : ℝ :=
  (∂[(1 : Fin 2)] (fun y ↦ u y 0)) x -
    (∂[(0 : Fin 2)] (fun y ↦ u y 1)) x

/-- Clockwise and counterclockwise scalar vorticities differ by a sign. -/
theorem spatialPlanarClockwiseVorticity_eq_neg_spatialPlanarVorticity
    (u : ℝ^2 → ℝ^2) (x : ℝ^2) :
    spatialPlanarClockwiseVorticity u x =
      -spatialPlanarVorticity u x := by
  simp only [spatialPlanarClockwiseVorticity, spatialPlanarVorticity]
  ring

/-- Spatial vorticity two-form with components `Ωᵢⱼ = ∂ᵢuⱼ - ∂ⱼuᵢ`. -/
def spatialVorticityForm (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : SpatialMatrix n :=
  WithLp.toLp 2 fun ij ↦
    (∂[ij.1.succ] (fun y ↦ u y ij.2)) x -
      (∂[ij.2.succ] (fun y ↦ u y ij.1)) x

/-- Coordinate formula for the spatial vorticity form. -/
@[simp]
theorem spatialVorticityForm_apply (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (i j : Fin n) :
    spatialVorticityForm n u x (i, j) =
      (∂[i.succ] (fun y ↦ u y j)) x -
        (∂[j.succ] (fun y ↦ u y i)) x :=
  rfl

/-- Antisymmetric velocity-gradient tensor `A = ∇u - (∇u)ᵀ`.
It is the negative of the vorticity two-form. -/
def vorticityTensor (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    SpatialMatrix n :=
  -spatialVorticityForm n u x

/-- The exterior-derivative and velocity-gradient conventions differ by a sign. -/
theorem spatialVorticityForm_eq_neg_vorticityTensor (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    spatialVorticityForm n u x = -vorticityTensor n u x := by
  simp only [vorticityTensor, neg_neg]

/-- The vorticity two-form is the transpose of the antisymmetric velocity-gradient tensor. -/
theorem spatialVorticityForm_eq_vorticityTensor_swap (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) (i j : Fin n) :
    spatialVorticityForm n u x (i, j) = vorticityTensor n u x (j, i) := by
  simp only [vorticityTensor, PiLp.neg_apply, spatialVorticityForm_apply, neg_sub]

/-- Coordinate formula `Aᵢⱼ = ∂ⱼuᵢ - ∂ᵢuⱼ` for the vorticity tensor. -/
@[simp]
theorem vorticityTensor_apply (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (i j : Fin n) :
    vorticityTensor n u x (i, j) =
      (∂[j.succ] (fun y ↦ u y i)) x -
        (∂[i.succ] (fun y ↦ u y j)) x := by
  simp only [vorticityTensor, PiLp.neg_apply, spatialVorticityForm_apply, neg_sub]

/-- Swapping the component indices changes the sign of vorticity. -/
theorem vorticityTensor_apply_swap (n : ℕ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (i j : Fin n) :
    vorticityTensor n u x (j, i) =
      -vorticityTensor n u x (i, j) := by
  simp only [vorticityTensor_apply]
  ring

/-- Every diagonal entry of the vorticity tensor vanishes. -/
theorem vorticityTensor_apply_self (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) (i : Fin n) :
    vorticityTensor n u x (i, i) = 0 := by
  simp

/-- Scalar vorticity `∂ₓu₂ - ∂ᵧu₁` for a two-dimensional spacetime flow. -/
def spacetimePlanarVorticity (u : ℝ^3 → ℝ^2) (x : ℝ^3) : ℝ :=
  vorticityTensor 2 u x ((1 : Fin 2), (0 : Fin 2))

/-- Coordinate formula for planar vorticity of a spacetime velocity field. -/
@[simp]
theorem spacetimePlanarVorticity_apply
    (u : ℝ^3 → ℝ^2) (x : ℝ^3) :
    spacetimePlanarVorticity u x =
      (∂[(1 : Fin 3)] (fun y ↦ u y 1)) x -
        (∂[(2 : Fin 3)] (fun y ↦ u y 0)) x := by
  simp [spacetimePlanarVorticity]

/-- The standard right-handed curl of a Cartesian vector field on `ℝ^3`. -/
def spatialCurl (u : ℝ^3 → ℝ^3) (x : ℝ^3) : ℝ^3 :=
  WithLp.toLp 2 ![
    (∂[(1 : Fin 3)] (fun y ↦ u y 2)) x -
      (∂[(2 : Fin 3)] (fun y ↦ u y 1)) x,
    (∂[(2 : Fin 3)] (fun y ↦ u y 0)) x -
      (∂[(0 : Fin 3)] (fun y ↦ u y 2)) x,
    (∂[(0 : Fin 3)] (fun y ↦ u y 1)) x -
      (∂[(1 : Fin 3)] (fun y ↦ u y 0)) x]

/-- First Cartesian curl component. -/
@[simp]
theorem spatialCurl_apply_zero (u : ℝ^3 → ℝ^3) (x : ℝ^3) :
    spatialCurl u x 0 =
      (∂[(1 : Fin 3)] (fun y ↦ u y 2)) x -
        (∂[(2 : Fin 3)] (fun y ↦ u y 1)) x := by
  simp [spatialCurl]

/-- Second Cartesian curl component. -/
@[simp]
theorem spatialCurl_apply_one (u : ℝ^3 → ℝ^3) (x : ℝ^3) :
    spatialCurl u x 1 =
      (∂[(2 : Fin 3)] (fun y ↦ u y 0)) x -
        (∂[(0 : Fin 3)] (fun y ↦ u y 2)) x := by
  simp [spatialCurl]

/-- Third Cartesian curl component. -/
@[simp]
theorem spatialCurl_apply_two (u : ℝ^3 → ℝ^3) (x : ℝ^3) :
    spatialCurl u x 2 =
      (∂[(0 : Fin 3)] (fun y ↦ u y 1)) x -
        (∂[(1 : Fin 3)] (fun y ↦ u y 0)) x := by
  simp [spatialCurl]

/-- The curl component formula, with cyclic indices in `Fin 3`. -/
theorem spatialCurl_apply (u : ℝ^3 → ℝ^3) (x : ℝ^3) (i : Fin 3) :
    spatialCurl u x i =
      (∂[i + 1] (fun y ↦ u y (i + 2))) x -
        (∂[i + 2] (fun y ↦ u y (i + 1))) x := by
  fin_cases i <;> simp [spatialCurl]

/-- At a differentiability point, curl is the antisymmetric part of the vector
Jacobian. This bridges component derivatives and derivatives of the whole field. -/
theorem spatialCurl_apply_eq_fderiv {u : ℝ^3 → ℝ^3} {x : ℝ^3}
    (hu : DifferentiableAt ℝ u x) (i : Fin 3) :
    spatialCurl u x i =
      (fderiv ℝ u x (EuclideanSpace.single (i + 1) 1)) (i + 2) -
        (fderiv ℝ u x (EuclideanSpace.single (i + 2) 1)) (i + 1) := by
  rw [spatialCurl_apply, ← PDE.partialDeriv_apply _ _ hu, ← PDE.partialDeriv_apply _ _ hu]
  rfl

/-- Curl is additive at a point where both vector fields are
differentiable. -/
theorem spatialCurl_add {u v : ℝ^3 → ℝ^3} {x : ℝ^3}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    spatialCurl (fun y ↦ u y + v y) x = spatialCurl u x + spatialCurl v x := by
  have huComponent (i : Fin 3) :
      DifferentiableAt ℝ (fun y ↦ u y i) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).differentiableAt.comp x hu
  have hvComponent (i : Fin 3) :
      DifferentiableAt ℝ (fun y ↦ v y i) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 ↦ ℝ) i).differentiableAt.comp x hv
  ext i
  fin_cases i
  · change spatialCurl (fun y ↦ u y + v y) x 0 =
      spatialCurl u x 0 + spatialCurl v x 0
    simp only [spatialCurl_apply_zero, PiLp.add_apply]
    rw [PDE.partialDeriv_add (huComponent 2) (hvComponent 2)]
    rw [PDE.partialDeriv_add (huComponent 1) (hvComponent 1)]
    ring
  · change spatialCurl (fun y ↦ u y + v y) x 1 =
      spatialCurl u x 1 + spatialCurl v x 1
    simp only [spatialCurl_apply_one, PiLp.add_apply]
    rw [PDE.partialDeriv_add (huComponent 0) (hvComponent 0)]
    rw [PDE.partialDeriv_add (huComponent 2) (hvComponent 2)]
    ring
  · change spatialCurl (fun y ↦ u y + v y) x 2 =
      spatialCurl u x 2 + spatialCurl v x 2
    simp only [spatialCurl_apply_two, PiLp.add_apply]
    rw [PDE.partialDeriv_add (huComponent 1) (hvComponent 1)]
    rw [PDE.partialDeriv_add (huComponent 0) (hvComponent 0)]
    ring

end

end IncompressibleFlow
