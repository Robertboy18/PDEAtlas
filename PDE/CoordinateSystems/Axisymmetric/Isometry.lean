/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Axisymmetric
public import PDE.Common.Euclidean.CoordinateReflection
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Axial rotations and the equatorial reflection as isometries

`axialRotation θ` is the rotation `axisRotation θ` through angle `θ` about the third coordinate
axis, as a linear isometry equivalence of `ℝ^3`. `equatorialReflection` is the reflection
`diag(1, 1, -1)` in the equatorial plane, where the axial coordinate vanishes, that is the
coordinate reflection `PDE.Common.coordinateReflection 2`. Both preserve Lebesgue measure, so
symmetry conditions on vector fields can be stated almost everywhere. The rotations form an
additive action of the angle, `2π`-periodic and jointly smooth in the angle and the point, the
reflection is an involution, and the two commute. The rotations fix the axis direction `e_z`,
the reflection negates it, and the symmetry axis is a Lebesgue null set (`volume_symmetryAxis`).
-/

@[expose] public section

noncomputable section

namespace PDE.CoordinateSystems

open MeasureTheory

/-- Rotation through angle `θ` about the third coordinate axis, as a linear isometry
equivalence of `ℝ^3`. Its underlying map is `axisRotation θ` and its inverse is the rotation
through `-θ`. -/
def axialRotation (θ : ℝ) : ℝ^3 ≃ₗᵢ[ℝ] ℝ^3 where
  toFun := axisRotation θ
  invFun := axisRotation (-θ)
  map_add' x y := by
    ext i
    fin_cases i <;> simp [axisRotation] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [axisRotation] <;> ring
  left_inv x := axisRotation_neg_apply θ x
  right_inv x := by simpa using axisRotation_neg_apply (-θ) x
  norm_map' x := by
    change ‖axisRotation θ x‖ = ‖x‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, axisRotation_apply_zero,
      axisRotation_apply_one, axisRotation_apply_two]
    linear_combination (x 0 ^ 2 + x 1 ^ 2) * Real.sin_sq_add_cos_sq θ

/-- The underlying map of `axialRotation θ` is `axisRotation θ`. -/
theorem coe_axialRotation (θ : ℝ) : ⇑(axialRotation θ) = axisRotation θ :=
  rfl

/-- Evaluation of `axialRotation θ` is the rotation `axisRotation θ`. -/
theorem axialRotation_apply (θ : ℝ) (x : ℝ^3) : axialRotation θ x = axisRotation θ x :=
  rfl

/-- First coordinate of a rotated point: `cos θ · x₀ - sin θ · x₁`. -/
@[simp]
theorem axialRotation_apply_zero (θ : ℝ) (x : ℝ^3) :
    axialRotation θ x 0 = Real.cos θ * x 0 - Real.sin θ * x 1 :=
  axisRotation_apply_zero θ x

/-- Second coordinate of a rotated point: `sin θ · x₀ + cos θ · x₁`. -/
@[simp]
theorem axialRotation_apply_one (θ : ℝ) (x : ℝ^3) :
    axialRotation θ x 1 = Real.sin θ * x 0 + Real.cos θ * x 1 :=
  axisRotation_apply_one θ x

/-- A rotation about the axis keeps the axial coordinate. -/
@[simp]
theorem axialRotation_apply_two (θ : ℝ) (x : ℝ^3) : axialRotation θ x 2 = x 2 :=
  axisRotation_apply_two θ x

/-- The inverse of the rotation through `θ` is the rotation through `-θ`. -/
@[simp]
theorem axialRotation_symm (θ : ℝ) : (axialRotation θ).symm = axialRotation (-θ) :=
  LinearIsometryEquiv.ext fun _ ↦ rfl

/-- The rotation through angle zero is the identity. -/
@[simp]
theorem axialRotation_zero : axialRotation 0 = LinearIsometryEquiv.refl ℝ (ℝ^3) := by
  ext x : 1
  exact axisRotation_zero x

/-- Rotations about the axis form an additive action of the angle. -/
theorem axialRotation_add (θ φ : ℝ) :
    axialRotation (θ + φ) = (axialRotation φ).trans (axialRotation θ) := by
  ext x : 1
  exact axisRotation_add θ φ x

/-- Rotations about the axis preserve Lebesgue measure. -/
theorem measurePreserving_axialRotation (θ : ℝ) :
    MeasurePreserving (axialRotation θ) volume volume :=
  (axialRotation θ).measurePreserving

/-- Reflection `diag(1, 1, -1)` in the plane orthogonal to the symmetry axis, as a linear
isometry equivalence of `ℝ^3`: the reflection in the coordinate hyperplane `{x | x 2 = 0}`. It
fixes the first two coordinates and negates the third. -/
def equatorialReflection : ℝ^3 ≃ₗᵢ[ℝ] ℝ^3 :=
  PDE.Common.coordinateReflectionLinearIsometryEquiv 2

/-- The underlying map of `equatorialReflection` is the reflection in the third coordinate. -/
theorem coe_equatorialReflection :
    ⇑equatorialReflection = PDE.Common.coordinateReflection 2 :=
  rfl

/-- The equatorial reflection keeps the first coordinate. -/
@[simp]
theorem equatorialReflection_apply_zero (x : ℝ^3) : equatorialReflection x 0 = x 0 :=
  PDE.Common.coordinateReflection_apply_of_ne 2 0 (by decide) x

/-- The equatorial reflection keeps the second coordinate. -/
@[simp]
theorem equatorialReflection_apply_one (x : ℝ^3) : equatorialReflection x 1 = x 1 :=
  PDE.Common.coordinateReflection_apply_of_ne 2 1 (by decide) x

/-- The equatorial reflection negates the axial coordinate. -/
@[simp]
theorem equatorialReflection_apply_two (x : ℝ^3) : equatorialReflection x 2 = -x 2 :=
  PDE.Common.coordinateReflection_apply_same 2 x

/-- Applying the equatorial reflection twice gives the identity. -/
@[simp]
theorem equatorialReflection_equatorialReflection (x : ℝ^3) :
    equatorialReflection (equatorialReflection x) = x :=
  PDE.Common.coordinateReflection_involutive 2 x

/-- The equatorial reflection is its own inverse. -/
@[simp]
theorem equatorialReflection_symm : equatorialReflection.symm = equatorialReflection :=
  LinearIsometryEquiv.ext fun x ↦ by
    rw [LinearIsometryEquiv.symm_apply_eq, equatorialReflection_equatorialReflection]

/-- The equatorial reflection commutes with every rotation about the axis. -/
theorem equatorialReflection_axialRotation (θ : ℝ) (x : ℝ^3) :
    equatorialReflection (axialRotation θ x) = axialRotation θ (equatorialReflection x) := by
  ext i
  fin_cases i <;> simp

/-- The equatorial reflection preserves Lebesgue measure. -/
theorem measurePreserving_equatorialReflection :
    MeasurePreserving equatorialReflection volume volume :=
  equatorialReflection.measurePreserving

/-- The cylindrical radius is invariant under the equatorial reflection. -/
@[simp]
theorem cylindricalRadius_equatorialReflection (x : ℝ^3) :
    cylindricalRadius (equatorialReflection x) = cylindricalRadius x := by
  simp [cylindricalRadius, cylindricalRadiusSq]

/-- The equatorial reflection negates the axial coordinate. -/
@[simp]
theorem axialCoordinate_equatorialReflection (x : ℝ^3) :
    axialCoordinate (equatorialReflection x) = -axialCoordinate x := by
  simp [axialCoordinate]

/-- The equatorial reflection commutes with the inverse rotations. -/
theorem equatorialReflection_axialRotation_symm (θ : ℝ) (x : ℝ^3) :
    equatorialReflection ((axialRotation θ).symm x) =
      (axialRotation θ).symm (equatorialReflection x) := by
  rw [axialRotation_symm, equatorialReflection_axialRotation]

/-- Rotations through angles differing by `2π` agree. -/
theorem axialRotation_add_two_pi (θ : ℝ) :
    axialRotation (θ + 2 * Real.pi) = axialRotation θ := by
  refine LinearIsometryEquiv.ext fun x ↦ ?_
  ext i
  fin_cases i <;>
    simp [axialRotation_apply_zero, axialRotation_apply_one, Real.cos_add_two_pi,
      Real.sin_add_two_pi]

/-- The rotation about the third axis is jointly smooth in the angle and the point. -/
theorem contDiff_axialRotation_apply :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ^3 ↦ axialRotation q.1 q.2) := by
  have hc (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ^3 ↦ q.2 i) :=
    (contDiff_piLp_apply (p := 2)).comp contDiff_snd
  refine (contDiff_piLp 2).mpr fun i ↦ ?_
  fin_cases i
  · simp only [Fin.zero_eta, axialRotation_apply_zero]
    exact ((Real.contDiff_cos.comp contDiff_fst).mul (hc 0)).sub
      ((Real.contDiff_sin.comp contDiff_fst).mul (hc 1))
  · simp only [Fin.mk_one, axialRotation_apply_one]
    exact ((Real.contDiff_sin.comp contDiff_fst).mul (hc 0)).add
      ((Real.contDiff_cos.comp contDiff_fst).mul (hc 1))
  · simp only [Fin.reduceFinMk, axialRotation_apply_two]
    exact hc 2

/-- Rotations about the axis fix the axis direction. -/
theorem axialRotation_single_two (θ : ℝ) :
    axialRotation θ (EuclideanSpace.single (2 : Fin 3) 1) = EuclideanSpace.single 2 1 := by
  ext i
  fin_cases i <;> simp [axialRotation_apply_zero, axialRotation_apply_one]

/-- The equatorial reflection negates the axis direction. -/
theorem equatorialReflection_single_two :
    equatorialReflection (EuclideanSpace.single (2 : Fin 3) 1) = -EuclideanSpace.single 2 1 := by
  ext i
  fin_cases i <;> simp

/-- The symmetry axis is a Lebesgue null set. -/
theorem volume_symmetryAxis : volume symmetryAxis = 0 := by
  let S : Submodule ℝ (ℝ^3) := Submodule.span ℝ {EuclideanSpace.single (2 : Fin 3) (1 : ℝ)}
  have hsub : symmetryAxis ⊆ (S : Set (ℝ^3)) := by
    intro x hx
    rw [mem_symmetryAxis_iff] at hx
    have hx' : x = x 2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
      ext i
      fin_cases i <;> simp [hx.1, hx.2]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  have hS : S ≠ ⊤ := by
    intro htop
    have hmem : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) ∈ S := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h0 := congrArg (fun v : ℝ^3 ↦ v 0) hc
    simp at h0
  exact measure_mono_null hsub (Measure.addHaar_submodule volume S hS)

end PDE.CoordinateSystems

end
