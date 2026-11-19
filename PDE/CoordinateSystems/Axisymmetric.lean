/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

/-!
# Axisymmetric Coordinates in Three Dimensions

The elementary geometry of rotations around the third coordinate axis:

* cylindrical radius and axial coordinate;
* the rotation action around the symmetry axis;
* invariant scalar or tensor-valued fields and equivariant vector fields;
* meridian lifts and the symmetry axis.

The definitions are purely geometric. Differential formulas that divide by the cylindrical
radius carry explicit off-axis hypotheses. Meridian parameters are signed: `meridianR` and
`meridianPoint r z` accept every real `r`, and statements that recover `r` as the cylindrical
radius assume `0 ≤ r`.

The conventions follow the standard cylindrical-coordinate treatment of axisymmetric flow in
Majda and Bertozzi and in Ukhovskii and Yudovich.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001.
  <https://doi.org/10.1017/CBO9780511613203>
* M. R. Ukhovskii and V. I. Yudovich, "Axially symmetric flows of ideal and viscous fluids filling
  the whole space", *Journal of Applied Mathematics and Mechanics* 32 (1968), no. 1, 52-62.
  <https://doi.org/10.1016/0021-8928(68)90147-0>
-/

@[expose] public section

noncomputable section

namespace PDE.CoordinateSystems

attribute [local instance 2000] WithLp.instAddCommGroup WithLp.instModule

/-- The signed radial coordinate of a point in the meridian plane. -/
def meridianR (x : ℝ^2) : ℝ := x 0

/-- The axial coordinate of a point in the meridian plane. -/
def meridianZ (x : ℝ^2) : ℝ := x 1

/-- The square of the cylindrical radius of `x ∈ ℝ^3`. -/
def cylindricalRadiusSq (x : ℝ^3) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2

/-- The cylindrical radius `sqrt ((x 0)² + (x 1)²)` of `x ∈ ℝ^3`, using the
first two coordinates; coordinate `2` is the axial direction. -/
def cylindricalRadius (x : ℝ^3) : ℝ :=
  √(cylindricalRadiusSq x)

/-- The squared cylindrical radius is nonnegative. -/
theorem cylindricalRadiusSq_nonneg (x : ℝ^3) : 0 ≤ cylindricalRadiusSq x :=
  add_nonneg (sq_nonneg (x 0)) (sq_nonneg (x 1))

/-- The cylindrical radius is nonnegative. -/
theorem cylindricalRadius_nonneg (x : ℝ^3) : 0 ≤ cylindricalRadius x :=
  Real.sqrt_nonneg _

/-- Squaring the cylindrical radius recovers the sum of squares of the transverse
coordinates. -/
@[simp]
theorem cylindricalRadius_sq (x : ℝ^3) : cylindricalRadius x ^ 2 = cylindricalRadiusSq x := by
  rw [cylindricalRadius, Real.sq_sqrt (cylindricalRadiusSq_nonneg x)]

/-- The coordinate along the symmetry axis. -/
def axialCoordinate (x : ℝ^3) : ℝ :=
  x 2

/-- Rotation through angle `θ` around the third coordinate axis. -/
def axisRotation (θ : ℝ) (x : ℝ^3) : ℝ^3 :=
  WithLp.toLp 2 ![
    Real.cos θ * x 0 - Real.sin θ * x 1,
    Real.sin θ * x 0 + Real.cos θ * x 1,
    x 2
  ]

/-- First coordinate of the rotated point: `x ↦ cos θ · x₀ − sin θ · x₁`. -/
@[simp]
theorem axisRotation_apply_zero (θ : ℝ) (x : ℝ^3) :
    axisRotation θ x 0 = Real.cos θ * x 0 - Real.sin θ * x 1 := by
  simp [axisRotation]

/-- Second coordinate of the rotated point: `x ↦ sin θ · x₀ + cos θ · x₁`. -/
@[simp]
theorem axisRotation_apply_one (θ : ℝ) (x : ℝ^3) :
    axisRotation θ x 1 = Real.sin θ * x 0 + Real.cos θ * x 1 := by
  simp [axisRotation]

/-- Rotation about the third axis leaves the axial coordinate `x 2` unchanged. -/
@[simp]
theorem axisRotation_apply_two (θ : ℝ) (x : ℝ^3) :
    axisRotation θ x 2 = x 2 := by
  simp [axisRotation]

/-- Rotation through angle zero is the identity. -/
@[simp]
theorem axisRotation_zero (x : ℝ^3) : axisRotation 0 x = x := by
  ext i
  fin_cases i <;> simp [axisRotation]

/-- Rotations around the symmetry axis form an additive action of the angle. -/
theorem axisRotation_add (θ φ : ℝ) (x : ℝ^3) :
    axisRotation (θ + φ) x = axisRotation θ (axisRotation φ x) := by
  ext i
  fin_cases i <;> simp [axisRotation, Real.sin_add, Real.cos_add] <;> ring

/-- Rotation by the negative angle is the inverse rotation. -/
@[simp]
theorem axisRotation_neg_apply (θ : ℝ) (x : ℝ^3) :
    axisRotation (-θ) (axisRotation θ x) = x := by
  rw [← axisRotation_add]
  simp

/-- The squared cylindrical radius is invariant under rotation about the axis; this is `sin² θ +
cos² θ = 1` applied to the transverse coordinates. -/
@[simp]
theorem cylindricalRadiusSq_axisRotation (θ : ℝ) (x : ℝ^3) :
    cylindricalRadiusSq (axisRotation θ x) = cylindricalRadiusSq x := by
  simp only [cylindricalRadiusSq, axisRotation_apply_zero, axisRotation_apply_one]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The cylindrical radius is invariant under rotation about the axis. -/
@[simp]
theorem cylindricalRadius_axisRotation (θ : ℝ) (x : ℝ^3) :
    cylindricalRadius (axisRotation θ x) = cylindricalRadius x := by
  simp [cylindricalRadius]

/-- The axial coordinate is invariant under rotation about the axis. -/
@[simp]
theorem axialCoordinate_axisRotation (θ : ℝ) (x : ℝ^3) :
    axialCoordinate (axisRotation θ x) = axialCoordinate x := by
  simp [axialCoordinate]

/-- A field with trivial codomain action is invariant under rotations about the symmetry axis. -/
def IsInvariantUnderAxisRotation {E : Type*} (f : ℝ^3 → E) : Prop :=
  ∀ θ x, f (axisRotation θ x) = f x

/-- A vector field is equivariant when rotating its input rotates its value equally. -/
def IsEquivariantUnderAxisRotation (u : ℝ^3 → ℝ^3) : Prop :=
  ∀ θ x, u (axisRotation θ x) = axisRotation θ (u x)

/-- Meridian coordinates `(r,z)` associated to a point of `ℝ^3`. -/
def meridianCoordinates (x : ℝ^3) : ℝ^2 :=
  WithLp.toLp 2 ![cylindricalRadius x, axialCoordinate x]

/-- The first meridian coordinate is the cylindrical radius `r`. -/
@[simp]
theorem meridianCoordinates_apply_zero (x : ℝ^3) :
    meridianCoordinates x 0 = cylindricalRadius x := by
  simp [meridianCoordinates]

/-- The second meridian coordinate is the axial coordinate `z`. -/
@[simp]
theorem meridianCoordinates_apply_one (x : ℝ^3) :
    meridianCoordinates x 1 = axialCoordinate x := by
  simp [meridianCoordinates]

/-- Lift a meridian profile on `(r,z)` coordinates to a rotation-invariant
function on `ℝ^3`. -/
def meridianLift {E : Type*} (g : ℝ^2 → E) (x : ℝ^3) : E :=
  g (meridianCoordinates x)

/-- Every meridian lift is invariant under rotations around the symmetry axis. -/
theorem isInvariantUnderAxisRotation_meridianLift {E : Type*} (g : ℝ^2 → E) :
    IsInvariantUnderAxisRotation (meridianLift g) := by
  intro θ x
  simp [meridianLift, meridianCoordinates]

/-- Embed signed meridian parameters `(r,z)` into the plane of angle zero.

When `r ≥ 0`, this is the canonical representative of the cylindrical half-plane. -/
def meridianPoint (r z : ℝ) : ℝ^3 :=
  WithLp.toLp 2 ![r, 0, z]

/-- The axial coordinate of `meridianPoint r z` is `z`, with no sign condition on `r`. -/
@[simp]
theorem axialCoordinate_meridianPoint (r z : ℝ) :
    axialCoordinate (meridianPoint r z) = z := by
  simp [axialCoordinate, meridianPoint]

/-- For `r ≥ 0` the cylindrical radius of `meridianPoint r z` is `r`. Without the sign
hypothesis the radius would be `|r|`, since `meridianPoint` embeds `(r, 0, z)` literally. -/
@[simp]
theorem cylindricalRadius_meridianPoint (r z : ℝ) (hr : 0 ≤ r) :
    cylindricalRadius (meridianPoint r z) = r := by
  simp [cylindricalRadius, cylindricalRadiusSq, meridianPoint, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hr]

/-- For `r ≥ 0`, `meridianPoint` is a section of `meridianCoordinates`: the meridian coordinates
of `meridianPoint r z` are `(r, z)`. -/
@[simp]
theorem meridianCoordinates_meridianPoint (r z : ℝ) (hr : 0 ≤ r) :
    meridianCoordinates (meridianPoint r z) = WithLp.toLp 2 ![r, z] := by
  ext i
  fin_cases i <;> simp [meridianCoordinates, hr]

/-- Evaluating a meridian lift at `meridianPoint r z` with `r ≥ 0` recovers the profile value
`g (r, z)`. -/
@[simp]
theorem meridianLift_meridianPoint {E : Type*} (g : ℝ^2 → E) (r z : ℝ)
    (hr : 0 ≤ r) :
    meridianLift g (meridianPoint r z) = g (WithLp.toLp 2 ![r, z]) := by
  simp [meridianLift, hr]

/-- The symmetry axis, characterized by vanishing cylindrical radius. -/
def symmetryAxis : Set ℝ^3 :=
  {x | cylindricalRadius x = 0}

/-- The cylindrical radius vanishes exactly when both transverse coordinates vanish. -/
theorem cylindricalRadius_eq_zero_iff (x : ℝ^3) :
    cylindricalRadius x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  constructor
  · intro h
    have hsum : cylindricalRadiusSq x = 0 := by
      rw [← cylindricalRadius_sq, h]
      norm_num
    have h0 : x 0 ^ 2 = 0 := by
      unfold cylindricalRadiusSq at hsum
      nlinarith [sq_nonneg (x 1)]
    have h1 : x 1 ^ 2 = 0 := by
      unfold cylindricalRadiusSq at hsum
      nlinarith [sq_nonneg (x 0)]
    exact ⟨sq_eq_zero_iff.mp h0, sq_eq_zero_iff.mp h1⟩
  · rintro ⟨h0, h1⟩
    simp [cylindricalRadius, cylindricalRadiusSq, h0, h1]

/-- A point lies on the symmetry axis iff its two transverse coordinates are zero. -/
@[simp]
theorem mem_symmetryAxis_iff (x : ℝ^3) :
    x ∈ symmetryAxis ↔ x 0 = 0 ∧ x 1 = 0 := by
  exact cylindricalRadius_eq_zero_iff x

/-- A point off the symmetry axis has a positive cylindrical radius. -/
theorem cylindricalRadius_pos {x : ℝ^3} (hx : x ∉ symmetryAxis) : 0 < cylindricalRadius x :=
  lt_of_le_of_ne (cylindricalRadius_nonneg x) (Ne.symm hx)

/-- A point off the symmetry axis is not the origin. -/
theorem ne_zero_of_notMem_symmetryAxis {x : ℝ^3} (hx : x ∉ symmetryAxis) : x ≠ 0 := by
  rintro rfl
  exact hx ((mem_symmetryAxis_iff 0).mpr ⟨rfl, rfl⟩)

/-- The symmetry axis is closed, so its complement is open. -/
theorem isClosed_symmetryAxis : IsClosed symmetryAxis := by
  have h : symmetryAxis = {x : ℝ^3 | x 0 = 0} ∩ {x | x 1 = 0} := by
    ext x
    simp [mem_symmetryAxis_iff]
  rw [h]
  exact (isClosed_eq (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).continuous continuous_const).inter
    (isClosed_eq (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous continuous_const)

end PDE.CoordinateSystems

end
