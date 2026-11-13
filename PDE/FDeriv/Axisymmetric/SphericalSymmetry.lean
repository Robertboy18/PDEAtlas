/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Axisymmetric.Spherical
public import PDE.CoordinateSystems.Axisymmetric.Isometry

/-!
# Symmetries of spherical meridional and azimuthal fields

Rotations about the third axis keep the norm and the polar cosine `x₃ / ‖x‖` and fix the axis
direction, so every meridional field `meridionalField F G S T` and every azimuthal field
`azimuthalField H A` is rotation equivariant. The equatorial reflection keeps the norm, negates
the polar cosine and the axis direction. A meridional field with even `S` and odd `T` and an
azimuthal field with even `A` are therefore equivariant under the reflection as well; with the
opposite parities they change sign, `u(σ x) = -σ u(x)`.
-/

@[expose] public noncomputable section

namespace PDE.FDeriv.Spherical

open PDE.CoordinateSystems (axialRotation equatorialReflection axialRotation_single_two
  equatorialReflection_single_two)

/-- The polar cosine is invariant under rotations about the axis. -/
theorem polarCosine_axialRotation (θ : ℝ) (x : ℝ^3) :
    polarCosine (axialRotation θ x) = polarCosine x := by
  simp only [polarCosine, PDE.CoordinateSystems.axialRotation_apply_two,
    LinearIsometryEquiv.norm_map]

/-- The equatorial reflection negates the polar cosine. -/
theorem polarCosine_equatorialReflection (x : ℝ^3) :
    polarCosine (equatorialReflection x) = -polarCosine x := by
  simp only [polarCosine, PDE.CoordinateSystems.equatorialReflection_apply_two,
    LinearIsometryEquiv.norm_map, neg_div]

/-- Meridional fields are equivariant under rotations about the axis. -/
theorem meridionalField_axialRotation (F G S T : ℝ → ℝ) (θ : ℝ) (x : ℝ^3) :
    meridionalField F G S T (axialRotation θ x) =
      axialRotation θ (meridionalField F G S T x) := by
  simp only [meridionalField, polarCosine_axialRotation, LinearIsometryEquiv.norm_map, map_add,
    map_smul, axialRotation_single_two]

/-- A meridional field with even `S` and odd `T` is equivariant under the equatorial
reflection. -/
theorem meridionalField_equatorialReflection {F G S T : ℝ → ℝ} (hS : ∀ c, S (-c) = S c)
    (hT : ∀ c, T (-c) = -T c) (x : ℝ^3) :
    meridionalField F G S T (equatorialReflection x) =
      equatorialReflection (meridionalField F G S T x) := by
  simp only [meridionalField, polarCosine_equatorialReflection, LinearIsometryEquiv.norm_map,
    map_add, map_smul, equatorialReflection_single_two, hS, hT, smul_neg, ← neg_smul]
  congr 2
  · ring
  · ring

/-- A meridional field with odd `S` and even `T` changes sign under the equatorial
reflection. -/
theorem meridionalField_equatorialReflection_of_odd {F G S T : ℝ → ℝ}
    (hS : ∀ c, S (-c) = -S c) (hT : ∀ c, T (-c) = T c) (x : ℝ^3) :
    meridionalField F G S T (equatorialReflection x) =
      -equatorialReflection (meridionalField F G S T x) := by
  simp only [meridionalField, polarCosine_equatorialReflection, LinearIsometryEquiv.norm_map,
    map_add, map_smul, equatorialReflection_single_two, hS, hT, smul_neg, neg_add, neg_neg,
    ← neg_smul]
  congr 2
  ring

/-- Azimuthal fields are equivariant under rotations about the axis. -/
theorem azimuthalField_axialRotation (H A : ℝ → ℝ) (θ : ℝ) (x : ℝ^3) :
    azimuthalField H A (axialRotation θ x) = axialRotation θ (azimuthalField H A x) := by
  set q := H ‖x‖ * A (polarCosine x) * ‖x‖⁻¹
  have hq : H ‖axialRotation θ x‖ * A (polarCosine (axialRotation θ x)) *
      ‖axialRotation θ x‖⁻¹ = q := by
    rw [polarCosine_axialRotation, LinearIsometryEquiv.norm_map]
  have h0 : azimuthalField H A (axialRotation θ x) 0 =
      axialRotation θ (azimuthalField H A x) 0 := by
    simp only [azimuthalField, hq, PDE.CoordinateSystems.axialRotation_apply_zero,
      PDE.CoordinateSystems.axialRotation_apply_one]
    simp only [Fin.isValue, Matrix.cons_val_zero, mul_neg, Matrix.cons_val_one]
    ring
  have h1 : azimuthalField H A (axialRotation θ x) 1 =
      axialRotation θ (azimuthalField H A x) 1 := by
    simp only [azimuthalField, hq, PDE.CoordinateSystems.axialRotation_apply_zero,
      PDE.CoordinateSystems.axialRotation_apply_one]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, mul_neg]
    ring
  have h2 : azimuthalField H A (axialRotation θ x) 2 =
      axialRotation θ (azimuthalField H A x) 2 := by
    simp only [azimuthalField, hq, PDE.CoordinateSystems.axialRotation_apply_two]
    simp
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- An azimuthal field with even polar coefficient is equivariant under the equatorial
reflection. -/
theorem azimuthalField_equatorialReflection {H A : ℝ → ℝ} (hA : ∀ c, A (-c) = A c)
    (x : ℝ^3) :
    azimuthalField H A (equatorialReflection x) =
      equatorialReflection (azimuthalField H A x) := by
  set q := H ‖x‖ * A (polarCosine x) * ‖x‖⁻¹
  have hq : H ‖equatorialReflection x‖ * A (polarCosine (equatorialReflection x)) *
      ‖equatorialReflection x‖⁻¹ = q := by
    rw [polarCosine_equatorialReflection, LinearIsometryEquiv.norm_map, hA]
  have h0 : azimuthalField H A (equatorialReflection x) 0 =
      equatorialReflection (azimuthalField H A x) 0 := by
    simp only [azimuthalField, hq, PDE.CoordinateSystems.equatorialReflection_apply_zero,
      PDE.CoordinateSystems.equatorialReflection_apply_one]
    rfl
  have h1 : azimuthalField H A (equatorialReflection x) 1 =
      equatorialReflection (azimuthalField H A x) 1 := by
    simp only [azimuthalField, hq, PDE.CoordinateSystems.equatorialReflection_apply_zero,
      PDE.CoordinateSystems.equatorialReflection_apply_one]
    rfl
  have h2 : azimuthalField H A (equatorialReflection x) 2 =
      equatorialReflection (azimuthalField H A x) 2 := by
    simp only [azimuthalField, PDE.CoordinateSystems.equatorialReflection_apply_two]
    simp
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- An azimuthal field with odd polar coefficient changes sign under the equatorial
reflection. -/
theorem azimuthalField_equatorialReflection_of_odd {H A : ℝ → ℝ} (hA : ∀ c, A (-c) = -A c)
    (x : ℝ^3) :
    azimuthalField H A (equatorialReflection x) =
      -equatorialReflection (azimuthalField H A x) := by
  set q := H ‖x‖ * A (polarCosine x) * ‖x‖⁻¹
  have hq : H ‖equatorialReflection x‖ * A (polarCosine (equatorialReflection x)) *
      ‖equatorialReflection x‖⁻¹ = -q := by
    rw [polarCosine_equatorialReflection, LinearIsometryEquiv.norm_map, hA]
    ring
  have h0 : azimuthalField H A (equatorialReflection x) 0 =
      (-equatorialReflection (azimuthalField H A x)) 0 := by
    simp only [azimuthalField, hq, PDE.CoordinateSystems.equatorialReflection_apply_zero,
      PDE.CoordinateSystems.equatorialReflection_apply_one, PiLp.neg_apply]
    simp [q]
  have h1 : azimuthalField H A (equatorialReflection x) 1 =
      (-equatorialReflection (azimuthalField H A x)) 1 := by
    simp only [azimuthalField, hq, PDE.CoordinateSystems.equatorialReflection_apply_zero,
      PDE.CoordinateSystems.equatorialReflection_apply_one, PiLp.neg_apply]
    simp [q]
  have h2 : azimuthalField H A (equatorialReflection x) 2 =
      (-equatorialReflection (azimuthalField H A x)) 2 := by
    simp only [azimuthalField, PDE.CoordinateSystems.equatorialReflection_apply_two,
      PiLp.neg_apply]
    simp
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end PDE.FDeriv.Spherical
