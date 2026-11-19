/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CoordinateSystems.Axisymmetric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Cylindrical parametrizations

The standard chart uses `(r, θ, z)`. The scaled chart uses `(q, θ, z)` with
`q = a r²`: `a = 1` is the squared radius and `a = 1/2` is half the squared
radius. The standard chart is smooth everywhere; the scaled chart is smooth
where `q/a > 0`. Neither construction chooses a global inverse angle.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems

open EuclideanSpace

/-- The cylindrical chart `(r, θ, z) ↦ (r cos θ, r sin θ, z)`. -/
def cylindricalMap (q : ℝ^3) : ℝ^3 :=
  (q 0 * Real.cos (q 1)) • single (0 : Fin 3) 1 +
    (q 0 * Real.sin (q 1)) • single (1 : Fin 3) 1 + q 2 • single (2 : Fin 3) 1

/-- Cartesian components of the cylindrical chart. -/
theorem cylindricalMap_apply (q : ℝ^3) :
    cylindricalMap q =
      WithLp.toLp 2 ![q 0 * Real.cos (q 1), q 0 * Real.sin (q 1), q 2] := by
  ext i
  fin_cases i <;> simp [cylindricalMap]

/-- The derivative of the cylindrical chart as a continuous linear map. -/
def cylindricalJacobian (q : ℝ^3) : ℝ^3 →L[ℝ] ℝ^3 :=
  (Real.cos (q 1) • (proj 0 : ℝ^3 →L[ℝ] ℝ) -
    (q 0 * Real.sin (q 1)) • proj 1).smulRight (single (0 : Fin 3) (1 : ℝ)) +
    (Real.sin (q 1) • (proj 0 : ℝ^3 →L[ℝ] ℝ) +
      (q 0 * Real.cos (q 1)) • proj 1).smulRight (single (1 : Fin 3) (1 : ℝ)) +
      (proj 2 : ℝ^3 →L[ℝ] ℝ).smulRight (single (2 : Fin 3) 1)

/-- The cylindrical Jacobian rotates `(v₀, r v₁, v₂)` into Cartesian coordinates. -/
theorem cylindricalJacobian_apply (q v : ℝ^3) :
    cylindricalJacobian q v =
      (Real.cos (q 1) * v 0 - q 0 * Real.sin (q 1) * v 1) • single (0 : Fin 3) 1 +
        (Real.sin (q 1) * v 0 + q 0 * Real.cos (q 1) * v 1) • single (1 : Fin 3) 1 +
          v 2 • single (2 : Fin 3) 1 := by
  simp [cylindricalJacobian]

/-- The cylindrical Jacobian is the Fréchet derivative of the chart. -/
theorem hasFDerivAt_cylindricalMap (q : ℝ^3) :
    HasFDerivAt cylindricalMap (cylindricalJacobian q) q := by
  have h0 := (proj 0 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt (x := q)
  have h1 := (proj 1 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt (x := q)
  have h2 := (proj 2 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt (x := q)
  have h : HasFDerivAt cylindricalMap _ q :=
    (((h0.mul h1.cos).smul_const (single (0 : Fin 3) (1 : ℝ))).add
    ((h0.mul h1.sin).smul_const (single (1 : Fin 3) (1 : ℝ)))).add
      (h2.smul_const (single (2 : Fin 3) (1 : ℝ)))
  apply h.congr_fderiv
  ext v i
  fin_cases i <;> simp [cylindricalJacobian] <;> ring

/-- The standard cylindrical chart is smooth, including on the parameter axis. -/
theorem contDiff_cylindricalMap {k : WithTop ℕ∞} : ContDiff ℝ k cylindricalMap :=
  ((((proj 0 : ℝ^3 →L[ℝ] ℝ).contDiff.mul
    (proj 1 : ℝ^3 →L[ℝ] ℝ).contDiff.cos).smul contDiff_const).add
    (((proj 0 : ℝ^3 →L[ℝ] ℝ).contDiff.mul
      (proj 1 : ℝ^3 →L[ℝ] ℝ).contDiff.sin).smul contDiff_const)).add
      ((proj 2 : ℝ^3 →L[ℝ] ℝ).contDiff.smul contDiff_const)

/-- Change from radius to scaled squared radius, keeping angle and height. -/
def squaredRadiusMap (a : ℝ) (q : ℝ^3) : ℝ^3 :=
  (a * q 0 ^ 2) • single (0 : Fin 3) 1 + q 1 • single (1 : Fin 3) 1 + q 2 • single (2 : Fin 3) 1

/-- The squared-radius change of parameters is smooth. -/
theorem contDiff_squaredRadiusMap (a : ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (squaredRadiusMap a) :=
  (((contDiff_const.mul (((proj 0 : ℝ^3 →L[ℝ] ℝ)).contDiff.pow 2)).smul contDiff_const).add
    (((proj 1 : ℝ^3 →L[ℝ] ℝ)).contDiff.smul contDiff_const)).add
      (((proj 2 : ℝ^3 →L[ℝ] ℝ)).contDiff.smul contDiff_const)

/-- Recover the positive radius from the scaled squared radius. -/
def sqrtRadiusMap (a : ℝ) (q : ℝ^3) : ℝ^3 :=
  Real.sqrt (q 0 / a) • single (0 : Fin 3) 1 +
    q 1 • single (1 : Fin 3) 1 + q 2 • single (2 : Fin 3) 1

/-- The inverse radius substitution is smooth where its radicand is positive. -/
theorem contDiffAt_sqrtRadiusMap (a : ℝ) {q : ℝ^3} (hq : 0 < q 0 / a)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (sqrtRadiusMap a) q :=
  ((((((proj 0 : ℝ^3 →L[ℝ] ℝ)).contDiff.contDiffAt.div_const a).sqrt hq.ne').smul
    contDiffAt_const).add (((proj 1 : ℝ^3 →L[ℝ] ℝ)).contDiff.contDiffAt.smul contDiffAt_const)).add
      (((proj 2 : ℝ^3 →L[ℝ] ℝ)).contDiff.contDiffAt.smul contDiffAt_const)

/-- Cylindrical coordinates with `q = a r²`. -/
def scaledCylindricalMap (a : ℝ) : ℝ^3 → ℝ^3 :=
  cylindricalMap ∘ sqrtRadiusMap a

/-- The scaled cylindrical chart is smooth away from its radial singularity. -/
theorem contDiffAt_scaledCylindricalMap (a : ℝ) {q : ℝ^3} (hq : 0 < q 0 / a)
    {k : WithTop ℕ∞} : ContDiffAt ℝ k (scaledCylindricalMap a) q :=
  contDiff_cylindricalMap.contDiffAt.comp q (contDiffAt_sqrtRadiusMap a hq)

/-- The Jacobian for scaled squared-radius coordinates. Its radial column is
`1 / (2 a r)` times the radial unit vector and its angular column has length `r`. -/
def scaledCylindricalJacobian (a : ℝ) (q : ℝ^3) : ℝ^3 →L[ℝ] ℝ^3 :=
  (cylindricalJacobian (sqrtRadiusMap a q)).comp
    ((((1 / (2 * a * Real.sqrt (q 0 / a))) •
      (proj 0 : ℝ^3 →L[ℝ] ℝ)).smulRight (single (0 : Fin 3) 1) +
      (proj 1 : ℝ^3 →L[ℝ] ℝ).smulRight (single (1 : Fin 3) 1)) +
        (proj 2 : ℝ^3 →L[ℝ] ℝ).smulRight (single (2 : Fin 3) 1))

/-- The scaled cylindrical Jacobian follows from the square-root chain rule. -/
theorem hasFDerivAt_scaledCylindricalMap (a : ℝ) {q : ℝ^3} (hq : 0 < q 0 / a) :
    HasFDerivAt (scaledCylindricalMap a) (scaledCylindricalJacobian a q) q := by
  have h0 : HasFDerivAt (fun y : ℝ^3 ↦ y 0 / a)
      (a⁻¹ • (proj 0 : ℝ^3 →L[ℝ] ℝ)) q := by
    have h := ((proj 0 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt (x := q)).const_smul a⁻¹
    change HasFDerivAt (fun y : ℝ^3 ↦ a⁻¹ * y 0) _ q at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  have hr := h0.sqrt hq.ne'
  have hrad : HasFDerivAt (sqrtRadiusMap a)
      ((((1 / (2 * a * Real.sqrt (q 0 / a))) •
        (proj 0 : ℝ^3 →L[ℝ] ℝ)).smulRight (single (0 : Fin 3) 1) +
        (proj 1 : ℝ^3 →L[ℝ] ℝ).smulRight (single (1 : Fin 3) 1)) +
          (proj 2 : ℝ^3 →L[ℝ] ℝ).smulRight (single (2 : Fin 3) 1)) q := by
    have h : HasFDerivAt (sqrtRadiusMap a) _ q :=
      ((hr.smul_const (single (0 : Fin 3) (1 : ℝ))).add
        ((proj 1 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt.smul_const
          (single (1 : Fin 3) (1 : ℝ)))).add
          ((proj 2 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt.smul_const (single (2 : Fin 3) (1 : ℝ)))
    apply h.congr_fderiv
    ext v i
    fin_cases i <;> simp [smul_smul, div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm]
  exact (hasFDerivAt_cylindricalMap _).comp q hrad

/-- The squared-radius substitution has diagonal derivative `(2 a r, 1, 1)`. -/
theorem hasFDerivAt_squaredRadiusMap (a : ℝ) (q : ℝ^3) :
    HasFDerivAt (squaredRadiusMap a)
      ((((2 * a * q 0) • (proj 0 : ℝ^3 →L[ℝ] ℝ)).smulRight
        (single (0 : Fin 3) (1 : ℝ)) +
        (proj 1 : ℝ^3 →L[ℝ] ℝ).smulRight (single (1 : Fin 3) (1 : ℝ))) +
          (proj 2 : ℝ^3 →L[ℝ] ℝ).smulRight (single (2 : Fin 3) (1 : ℝ))) q := by
  have h0 := (proj 0 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt (x := q)
  have h : HasFDerivAt (squaredRadiusMap a) _ q :=
    ((((h0.pow 2).const_mul a).smul_const (single (0 : Fin 3) (1 : ℝ))).add
      ((proj 1 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt.smul_const
        (single (1 : Fin 3) (1 : ℝ)))).add
        ((proj 2 : ℝ^3 →L[ℝ] ℝ).hasFDerivAt.smul_const (single (2 : Fin 3) (1 : ℝ)))
  apply h.congr_fderiv
  ext v i
  fin_cases i <;> simp
  ring

/-- Components of the squared-radius substitution. -/
theorem squaredRadiusMap_apply (a : ℝ) (q : ℝ^3) :
    squaredRadiusMap a q = WithLp.toLp 2 ![a * q 0 ^ 2, q 1, q 2] := by
  ext i
  fin_cases i <;> simp [squaredRadiusMap]

/-- Components of the positive-radius substitution. -/
theorem sqrtRadiusMap_apply (a : ℝ) (q : ℝ^3) :
    sqrtRadiusMap a q = WithLp.toLp 2 ![Real.sqrt (q 0 / a), q 1, q 2] := by
  ext i
  fin_cases i <;> simp [sqrtRadiusMap]

/-- Squaring the positive radius recovers the scaled squared-radius parameter. -/
theorem squaredRadiusMap_sqrtRadiusMap (a : ℝ) {q : ℝ^3} (hq : 0 < q 0 / a) :
    squaredRadiusMap a (sqrtRadiusMap a q) = q := by
  have ha : a ≠ 0 := by rintro rfl; simp at hq
  ext i
  fin_cases i <;> simp [squaredRadiusMap, sqrtRadiusMap, Real.sq_sqrt hq.le,
    mul_div_cancel₀, ha]

/-- The inverse radius substitution recovers nonnegative radii. -/
theorem sqrtRadiusMap_squaredRadiusMap {a : ℝ} (ha : a ≠ 0) {q : ℝ^3}
    (hq : 0 ≤ q 0) : sqrtRadiusMap a (squaredRadiusMap a q) = q := by
  ext i
  fin_cases i <;> simp [squaredRadiusMap, sqrtRadiusMap, ha, Real.sqrt_sq hq]

/-- The two cylindrical parametrizations agree after the squared-radius substitution. -/
theorem scaledCylindricalMap_squaredRadiusMap {a : ℝ} (ha : a ≠ 0) {q : ℝ^3}
    (hq : 0 ≤ q 0) :
    scaledCylindricalMap a (squaredRadiusMap a q) = cylindricalMap q := by
  simp only [scaledCylindricalMap, Function.comp_apply,
    sqrtRadiusMap_squaredRadiusMap ha hq]

end PDE.CoordinateSystems
