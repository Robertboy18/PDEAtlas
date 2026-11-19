/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Axisymmetric
public import PDE.FDeriv.PartialDeriv

/-!
# Classical and abstract derivatives of meridian profiles

Axisymmetric profile equations combine radial and axial derivatives with the
quotient `(∂R f) / R`. We keep that quotient as a separate operator so that a
calculation can include the axis. The concrete realization selects `∂RR f` at
`R = 0`; identifying this choice with a limit requires regularity and a vanishing
first radial derivative. The elliptic operator built from them is
`axisymmetricLaplacian D f = ∂RR f + (3/R) ∂R f + ∂ZZ f`, where the quotient is the field
`dROverR` of the realization `D`.

`AxisymmetricDifferential` holds the operators pointwise, for the differential
formulas. `LinearAxisymmetricDifferential` holds linear maps, for coefficient
calculations on domains where linearity has been proved.
-/

@[expose] public section

noncomputable section

open PDE.CoordinateSystems (meridianR meridianZ)

namespace PDE.FDeriv

/--
Radial and axial derivative operators for axisymmetric scalar profiles.

The field `dROverR` records an interpretation of `(∂R f)/R` at the axis.
Each realization specifies its value at `R = 0`; using this value as a
removable limit also requires regularity and a vanishing radial derivative.
-/
structure AxisymmetricDifferential where
  /-- Radial first-derivative operator. -/
  dR : (ℝ^2 → ℝ) → (ℝ^2 → ℝ)
  /-- Axial first-derivative operator. -/
  dZ : (ℝ^2 → ℝ) → (ℝ^2 → ℝ)
  /-- Radial second-derivative operator. -/
  dRR : (ℝ^2 → ℝ) → (ℝ^2 → ℝ)
  /-- Axial second-derivative operator. -/
  dZZ : (ℝ^2 → ℝ) → (ℝ^2 → ℝ)
  /-- Operator representing `(∂R f)/R`, with its axis value supplied by the realization. -/
  dROverR : (ℝ^2 → ℝ) → (ℝ^2 → ℝ)

/-- Radial derivative `∂R` of a scalar profile. -/
def profileDR (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ (∂[0] f) x

/-- Axial derivative `∂Z` of a scalar profile. -/
def profileDZ (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ (∂[1] f) x

/-- Second radial derivative `∂RR` of a scalar profile. -/
def profileDRR (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ (∂[0] (profileDR f)) x

/-- Second axial derivative `∂ZZ` of a scalar profile. -/
def profileDZZ (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ (∂[1] (profileDZ f)) x

/--
The quotient `(∂R f)/R` with Lean's division, so it is `0` on the axis.
Bounds that include the axis may instead use a removable-limit realization
of the `dROverR` field of `AxisymmetricDifferential`.
-/
def rawProfileDROverR (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ profileDR f x / meridianR x

/-- Euclidean profile derivatives with the quotient `rawProfileDROverR`, zero on the axis. -/
def rawEuclideanAxisymmetricDifferential : AxisymmetricDifferential where
  dR := profileDR
  dZ := profileDZ
  dRR := profileDRR
  dZZ := profileDZZ
  dROverR := rawProfileDROverR

/--
Axis-regular realization of `(∂R f) / R`.

Away from the axis this is the ordinary quotient. At `R = 0` it selects
`∂RR f`. This selected branch is the removable value for a sufficiently
regular profile with vanishing first radial trace. Stronger evenness, such as
squared-radius factorization, is still needed for smooth three-dimensional
reconstruction.
-/
def regularizedProfileDROverR (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦
    if meridianR x = 0 then profileDRR f x
    else (meridianR x)⁻¹ * profileDR f x

/-- Classical profile derivatives with the axis-regular quotient `regularizedProfileDROverR`. -/
def classicalAxisymmetricDifferential : AxisymmetricDifferential where
  dR := profileDR
  dZ := profileDZ
  dRR := profileDRR
  dZZ := profileDZZ
  dROverR := regularizedProfileDROverR

/-- An operator family has classical axis-regular semantics when it equals
`classicalAxisymmetricDifferential`. -/
def HasClassicalAxisymmetricSemantics (D : AxisymmetricDifferential) : Prop :=
  D = classicalAxisymmetricDifferential

/-- `classicalAxisymmetricDifferential` has classical semantics, by definition. -/
theorem classicalAxisymmetricDifferential_hasSemantics :
    HasClassicalAxisymmetricSemantics classicalAxisymmetricDifferential :=
  rfl

/-- Off the axis, the classical `dROverR` field is the quotient `(∂_R f)/R`,
written with `(meridianR x)⁻¹`. -/
@[simp]
theorem classical_dROverR_of_ne_zero
    (f : (ℝ^2 → ℝ)) (x : (ℝ^2)) (hx : meridianR x ≠ 0) :
    classicalAxisymmetricDifferential.dROverR f x =
      (meridianR x)⁻¹ * classicalAxisymmetricDifferential.dR f x := by
  simp [classicalAxisymmetricDifferential, regularizedProfileDROverR, hx]

/-- On the axis, the classical `dROverR` field is `∂_RR f`. This is the removable value of
`(∂_R f)/R` for a smooth profile whose radial derivative vanishes at `R = 0`. The lemma
only records which branch is chosen. -/
@[simp]
theorem classical_dROverR_of_eq_zero
    (f : (ℝ^2 → ℝ)) (x : (ℝ^2)) (hx : meridianR x = 0) :
    classicalAxisymmetricDifferential.dROverR f x =
      classicalAxisymmetricDifferential.dRR f x := by
  simp [classicalAxisymmetricDifferential, regularizedProfileDROverR, hx]

/-- The unsigned axisymmetric elliptic operator `∂RR + (3/R)∂R + ∂ZZ`. -/
def axisymmetricLaplacian (D : AxisymmetricDifferential) (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ D.dRR f x + 3 * D.dROverR f x + D.dZZ f x

/-- The signed elliptic operator `-L_ax`, as in the stream equation `-L_ax Ψ = Ω`. -/
def signedElliptic (D : AxisymmetricDifferential) (f : (ℝ^2 → ℝ)) : (ℝ^2 → ℝ) :=
  fun x ↦ -axisymmetricLaplacian D f x

/--
Axisymmetric derivative operators, each an `ℝ`-linear map.

`AxisymmetricDifferential` is more convenient for writing the PDE formulas
pointwise. We use this version when the elliptic operator enters
coefficient-space algebra: each derivative is linear, so the signed Poisson
operator is linear too.
-/
structure LinearAxisymmetricDifferential where
  /-- Linear radial first-derivative operator. -/
  dR : (ℝ^2 → ℝ) →ₗ[ℝ] (ℝ^2 → ℝ)
  /-- Linear axial first-derivative operator. -/
  dZ : (ℝ^2 → ℝ) →ₗ[ℝ] (ℝ^2 → ℝ)
  /-- Linear radial second-derivative operator. -/
  dRR : (ℝ^2 → ℝ) →ₗ[ℝ] (ℝ^2 → ℝ)
  /-- Linear axial second-derivative operator. -/
  dZZ : (ℝ^2 → ℝ) →ₗ[ℝ] (ℝ^2 → ℝ)
  /-- Linear realization of `(∂R f)/R`, including its chosen value at the axis. -/
  dROverR : (ℝ^2 → ℝ) →ₗ[ℝ] (ℝ^2 → ℝ)

/-- The underlying pointwise operators of a linear family. -/
def LinearAxisymmetricDifferential.toAxisymmetricDifferential
    (D : LinearAxisymmetricDifferential) : AxisymmetricDifferential where
  dR := fun f ↦ D.dR f
  dZ := fun f ↦ D.dZ f
  dRR := fun f ↦ D.dRR f
  dZZ := fun f ↦ D.dZZ f
  dROverR := fun f ↦ D.dROverR f

/-- The unsigned axisymmetric elliptic operator as a linear map. -/
def axisymmetricLaplacianLinearMap
    (D : LinearAxisymmetricDifferential) : (ℝ^2 → ℝ) →ₗ[ℝ] (ℝ^2 → ℝ) where
  toFun := fun f ↦ fun x ↦ D.dRR f x + 3 * D.dROverR f x + D.dZZ f x
  map_add' := by
    intro f g
    ext x
    simp [map_add]
    ring
  map_smul' := by
    intro c f
    ext x
    simp [map_smul]
    ring

/-- The signed elliptic operator `-(∂RR + 3/R ∂R + ∂ZZ)` as a linear map. -/
def signedEllipticLinearMap
    (D : LinearAxisymmetricDifferential) : (ℝ^2 → ℝ) →ₗ[ℝ] (ℝ^2 → ℝ) :=
  -axisymmetricLaplacianLinearMap D

/-- The linear-map elliptic operator agrees with the pointwise PDE definition. -/
theorem signedEllipticLinearMap_apply
    (D : LinearAxisymmetricDifferential) (f : (ℝ^2 → ℝ)) :
    signedEllipticLinearMap D f =
      signedElliptic D.toAxisymmetricDifferential f := by
  ext x
  simp [signedEllipticLinearMap, axisymmetricLaplacianLinearMap,
    signedElliptic, axisymmetricLaplacian,
    LinearAxisymmetricDifferential.toAxisymmetricDifferential]

end PDE.FDeriv
