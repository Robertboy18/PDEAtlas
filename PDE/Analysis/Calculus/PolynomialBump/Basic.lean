/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PositivePartPower
public import PDE.Analysis.Calculus.SecondDirectionalDerivative
public import Mathlib.Analysis.InnerProductSpace.Calculus
import CAS.ExactTactic

/-!
# Cubic polynomial ball bumps

The positive-part cube of `R² - ‖x - z‖²` is globally C². Its first and
second derivatives vanish on the sphere, allowing smooth moving and expanding
profiles to share the same spatial derivative formulas.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A cubic polynomial bump supported in the closed ball of radius `|R|`. -/
def polynomialBallBump (z : E) (R : ℝ) (x : E) : ℝ :=
  (R ^ 2 - ‖x - z‖ ^ 2)⁺ ^ 3

/-- The polynomial bump is twice continuously differentiable across its sphere. -/
theorem contDiff_polynomialBallBump (z : E) (R : ℝ) :
    ContDiff ℝ 2 (polynomialBallBump z R) :=
  contDiff_two_posPart_cube.comp
    (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ))

/-- The first derivative of the bump, valid both inside and outside its support. -/
theorem hasFDerivAt_polynomialBallBump (z : E) (R : ℝ) (x : E) :
    HasFDerivAt (polynomialBallBump z R)
      ((-6 * (R ^ 2 - ‖x - z‖ ^ 2)⁺ ^ 2) • innerSL ℝ (x - z)) x := by
  have hnorm : HasFDerivAt (fun y : E ↦ ‖y - z‖ ^ 2)
      (2 • innerSL ℝ (x - z)) x := by
    simpa using ((hasFDerivAt_id x).sub_const z).norm_sq
  have hgap := hnorm.const_sub (R ^ 2)
  have hcube :=
    (hasDerivAt_posPart_pow 1 (R ^ 2 - ‖x - z‖ ^ 2)).comp_hasFDerivAt x hgap
  convert! hcube using 1
  ext v
  simp only [smul_apply, neg_apply,
    innerSL_apply_apply, smul_eq_mul, Nat.reduceAdd, Nat.cast_ofNat]
  cas

/-- Evaluate the first derivative in a direction. -/
theorem fderiv_polynomialBallBump_apply (z : E) (R : ℝ) (x v : E) :
    fderiv ℝ (polynomialBallBump z R) x v =
      -6 * (R ^ 2 - ‖x - z‖ ^ 2)⁺ ^ 2 * ⟪x - z, v⟫_ℝ := by
  rw [(hasFDerivAt_polynomialBallBump z R x).fderiv]
  rfl

/-- The curvature of the polynomial bump along every affine line. -/
theorem secondDirectionalDerivative_polynomialBallBump (z : E) (R : ℝ) (x v : E) :
    secondDirectionalDerivative (polynomialBallBump z R) x v =
      24 * (R ^ 2 - ‖x - z‖ ^ 2)⁺ * ⟪x - z, v⟫_ℝ ^ 2 -
        6 * (R ^ 2 - ‖x - z‖ ^ 2)⁺ ^ 2 * ‖v‖ ^ 2 := by
  have hline (s : ℝ) : HasDerivAt (fun t : ℝ ↦ x + t • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hfirst (s : ℝ) :
      deriv (fun t : ℝ ↦ polynomialBallBump z R (x + t • v)) s =
        -6 * (R ^ 2 - ‖x + s • v - z‖ ^ 2)⁺ ^ 2 * ⟪x + s • v - z, v⟫_ℝ := by
    exact ((hasFDerivAt_polynomialBallBump z R (x + s • v)).comp_hasDerivAt
      s (hline s)).deriv
  have hgap : HasDerivAt (fun s : ℝ ↦ R ^ 2 - ‖x + s • v - z‖ ^ 2)
      (-2 * ⟪x - z, v⟫_ℝ) 0 := by
    simpa using (((hline 0).sub_const z).norm_sq).const_sub (R ^ 2)
  have hsquare := (hasDerivAt_posPart_pow 0 _).comp 0 hgap
  have hinner : HasDerivAt (fun s : ℝ ↦ ⟪x + s • v - z, v⟫_ℝ) (‖v‖ ^ 2) 0 := by
    simpa using ((hline 0).sub_const z).inner ℝ (hasDerivAt_const 0 v)
  have hsecond := (hsquare.const_mul (-6)).mul hinner
  rw [secondDirectionalDerivative, funext hfirst]
  convert! hsecond.deriv using 1
  simp only [Function.comp_apply, zero_smul, add_zero, Nat.reduceAdd, Nat.cast_ofNat, pow_one]
  cas

omit [InnerProductSpace ℝ E] in
/-- The bump vanishes on and outside its sphere. -/
theorem polynomialBallBump_eq_zero {z x : E} {R : ℝ}
    (hR : 0 ≤ R) (hx : R ≤ ‖x - z‖) : polynomialBallBump z R x = 0 := by
  have hgap : R ^ 2 - ‖x - z‖ ^ 2 ≤ 0 :=
    sub_nonpos.mpr ((sq_le_sq₀ hR (norm_nonneg _)).mpr hx)
  simp [polynomialBallBump, posPart_eq_zero.mpr hgap]

omit [InnerProductSpace ℝ E] in
/-- The polynomial bump is nonnegative. -/
theorem polynomialBallBump_nonneg (z : E) (R : ℝ) (x : E) :
    0 ≤ polynomialBallBump z R x :=
  pow_nonneg (posPart_nonneg _) _

omit [InnerProductSpace ℝ E] in
/-- The value at the center bounds the whole polynomial bump. -/
theorem polynomialBallBump_le (z : E) (R : ℝ) (x : E) :
    polynomialBallBump z R x ≤ R ^ 6 := by
  have hgap : (R ^ 2 - ‖x - z‖ ^ 2)⁺ ≤ R ^ 2 :=
    sup_le (sub_le_self _ (sq_nonneg _)) (sq_nonneg _)
  calc
    polynomialBallBump z R x ≤ (R ^ 2) ^ 3 :=
      pow_le_pow_left₀ (posPart_nonneg _) hgap _
    _ = R ^ 6 := by cas

omit [InnerProductSpace ℝ E] in
/-- The center value is the sixth power of the radius. -/
@[simp]
theorem polynomialBallBump_self (z : E) (R : ℝ) :
    polynomialBallBump z R z = R ^ 6 := by
  simp only [polynomialBallBump, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, posPart_eq_self.mpr (sq_nonneg R)]
  cas

end PDE.Analysis
