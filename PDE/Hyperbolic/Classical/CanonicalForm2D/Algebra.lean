/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.CanonicalForm2D
import CAS.ExactTactic

/-!
# Algebra for characteristic coordinates

The characteristic slopes solve the principal quadratic equation. Two independent
null covectors have nonzero mixed coefficient. A constant shear supplies a
noncharacteristic first coordinate even when the original pure coefficient vanishes.
-/

@[expose] public noncomputable section

namespace Hyperbolic.CanonicalForm2D.PrincipalPart

/-- The slope of either characteristic family, with sign `ε = ±1`. -/
def characteristicSlope (A : PrincipalPart) (ε : ℝ) : ℝ :=
  (A.a12 + ε * Real.sqrt A.discriminant) / A.a11

/-- Each square-root branch solves the characteristic equation. -/
theorem characteristicSlope_equation (A : PrincipalPart) (ε : ℝ)
    (hε : ε ^ 2 = 1) (ha : A.a11 ≠ 0) (hD : 0 ≤ A.discriminant) :
    A.a11 * A.characteristicSlope ε ^ 2 - 2 * A.a12 * A.characteristicSlope ε + A.a22 = 0 := by
  have hs := Real.sq_sqrt hD
  unfold characteristicSlope
  unfold discriminant at hs ⊢
  cas using [hε, hs]

/-- The two characteristic directions differ under strict hyperbolicity. -/
theorem characteristicSlope_ne (A : PrincipalPart) (ha : A.a11 ≠ 0) (hD : 0 < A.discriminant) :
    A.characteristicSlope 1 ≠ A.characteristicSlope (-1) := by
  have hs : 0 < Real.sqrt A.discriminant := Real.sqrt_pos.mpr hD
  intro h
  have he := (div_left_inj' ha).mp h
  simp only [one_mul, neg_one_mul] at he
  linarith

/-- A solution of the transport equation gives a null covector. -/
theorem quadratic_eq_zero_of_transport (A : PrincipalPart) (c v₀ v₁ : ℝ)
    (hc : A.a11 * c ^ 2 - 2 * A.a12 * c + A.a22 = 0) (hv : v₀ + c * v₁ = 0) :
    A.quadratic v₀ v₁ = 0 := by
  have he : v₀ = -(c * v₁) := eq_neg_of_add_eq_zero_left hv
  rw [he]
  unfold quadratic
  cas using hc

/-- Determinant congruence for the principal form under two covectors. -/
theorem quadratic_mul_quadratic_sub_mixed_sq (A : PrincipalPart) (v₀ v₁ w₀ w₁ : ℝ) :
    A.quadratic v₀ v₁ * A.quadratic w₀ w₁ - A.mixed v₀ v₁ w₀ w₁ ^ 2 =
      A.determinant * covectorDeterminant v₀ v₁ w₀ w₁ ^ 2 := by
  unfold quadratic mixed determinant covectorDeterminant
  cas

/-- Independent null covectors of a nondegenerate form have nonzero polarization. -/
theorem mixed_ne_zero_of_null (A : PrincipalPart) (v₀ v₁ w₀ w₁ : ℝ) (hA : A.determinant ≠ 0)
    (hv : A.quadratic v₀ v₁ = 0) (hw : A.quadratic w₀ w₁ = 0)
    (hvw : covectorDeterminant v₀ v₁ w₀ w₁ ≠ 0) :
    A.mixed v₀ v₁ w₀ w₁ ≠ 0 := by
  intro h
  have he := A.quadratic_mul_quadratic_sub_mixed_sq v₀ v₁ w₀ w₁
  rw [hv, hw, h, zero_mul, zero_pow (by norm_num), sub_zero] at he
  exact (mul_ne_zero hA (pow_ne_zero 2 hvw)) he.symm

/-- Principal coefficients after the shear `(x,y) ↦ (x+k*y,y)`. -/
def shear (A : PrincipalPart) (k : ℝ) : PrincipalPart where
  a11 := A.a11 + 2 * k * A.a12 + k ^ 2 * A.a22
  a12 := A.a12 + k * A.a22
  a22 := A.a22

/-- A shear preserves the characteristic discriminant. -/
theorem discriminant_shear (A : PrincipalPart) (k : ℝ) :
    (A.shear k).discriminant = A.discriminant := by
  unfold shear discriminant
  cas

/-- Pulling a covector through a shear preserves its principal quadratic value. -/
theorem quadratic_shear (A : PrincipalPart) (k v₀ v₁ : ℝ) :
    (A.shear k).quadratic v₀ v₁ = A.quadratic v₀ (k * v₀ + v₁) := by
  unfold shear quadratic
  cas

/-- A hyperbolic principal form admits a shear with nonzero first pure coefficient. -/
theorem exists_shear_a11_ne_zero (A : PrincipalPart) (hA : A.IsHyperbolic) :
    ∃ k : ℝ, (A.shear k).a11 ≠ 0 := by
  by_cases ha : A.a11 = 0
  · have hb : A.a12 ≠ 0 := by
      intro hb
      simp [IsHyperbolic, determinant, ha, hb] at hA
    by_cases hplus : 2 * A.a12 + A.a22 = 0
    · refine ⟨-1, ?_⟩
      simp only [shear, ha, zero_add, neg_one_sq, one_mul]
      intro hm
      have hz : A.a12 = 0 := by linarith
      exact hb hz
    · refine ⟨1, ?_⟩
      simpa only [shear, ha, zero_add, mul_one, one_pow, one_mul] using hplus
  · exact ⟨0, by simpa [shear] using ha⟩

end Hyperbolic.CanonicalForm2D.PrincipalPart
