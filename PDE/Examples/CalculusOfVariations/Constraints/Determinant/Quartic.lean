/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.CalculusOfVariations.Constraints.Determinant.Shear
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Mul
import CAS.ExactTactic

/-!
# Signed quartic densities on the determinant-one class

The Frobenius quartic minus an arbitrary real constant is smooth and convex
in the full gradient. It is coercive both at exponent four and at smaller
positive real exponents. On the nonaffine shear its density is a
bounded polynomial, so the finite-energy form of the existence theorem
applies even when the Sobolev exponent is `7 / 2`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.CalculusOfVariations
open SobolevSpace.Boundary.Atlas.UnitBall
open scoped ENNReal Matrix.Norms.Elementwise Sobolev

namespace PDE.Examples.Constraints.Determinant

/-- A full-matrix convex quartic with any signed lower shift. -/
def quarticDensity {n : ℕ} (β : ℝ)
    (t : Matrix (Fin n) (Fin n) ℝ × ℝ^n) : ℝ :=
  ‖Matrix.euclideanEquiv t.1‖ ^ 4 - β

/-- The quartic density is smooth. -/
theorem quarticDensity_contDiff (n : ℕ) (β : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (quarticDensity (n := n) β) := by
  have hP : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : Matrix (Fin n) (Fin n) ℝ × ℝ^n ↦ Matrix.euclideanEquiv t.1) :=
    Matrix.euclideanEquiv.contDiff.comp contDiff_fst
  have h := ((hP.norm_sq ℝ).pow 2).sub (contDiff_const (c := β))
  convert! h using 1
  ext t
  simp only [quarticDensity, ← pow_mul]

/-- The quartic density is convex in the matrix variable. -/
theorem quarticDensity_convex {n : ℕ} (β : ℝ) (x : ℝ^n) :
    ConvexOn ℝ univ (fun P : Matrix (Fin n) (Fin n) ℝ ↦ quarticDensity β (P, x)) := by
  have h := ((convexOn_univ_norm : ConvexOn ℝ univ (norm : ℝ^(n * n) → ℝ)).pow
    (fun _ _ ↦ norm_nonneg _) 4).add_const (-β)
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ t r ht hr htr
  change ‖Matrix.euclideanEquiv (t • a + r • b)‖ ^ 4 - β ≤
    t • (‖Matrix.euclideanEquiv a‖ ^ 4 - β) +
      r • (‖Matrix.euclideanEquiv b‖ ^ 4 - β)
  rw [map_add, map_smul, map_smul]
  simpa only [Pi.add_apply, Pi.pow_apply, sub_eq_add_neg] using
    h.2 (mem_univ (Matrix.euclideanEquiv a)) (mem_univ (Matrix.euclideanEquiv b))
      ht hr htr

/-- Coercivity at exponent four, with shift `β`. -/
theorem quarticDensity_coercive_four {n : ℕ} (β : ℝ)
    (x : ℝ^n) (P : Matrix (Fin n) (Fin n) ℝ) :
    1 * ‖Matrix.euclideanEquiv P‖ ^ (4 : ℝ) - β ≤ quarticDensity β (P, x) := by
  simp only [quarticDensity, Real.rpow_ofNat, one_mul, le_refl]

/-- Coercivity at every exponent `0 ≤ q ≤ 4`, with shift `β + 1`. -/
theorem quarticDensity_coercive {n : ℕ} (β : ℝ) {q : ℝ} (hq : 0 ≤ q) (hq4 : q ≤ 4)
    (x : ℝ^n) (P : Matrix (Fin n) (Fin n) ℝ) :
    1 * ‖Matrix.euclideanEquiv P‖ ^ q - (β + 1) ≤ quarticDensity β (P, x) := by
  have hpow : ‖Matrix.euclideanEquiv P‖ ^ q ≤ 1 + ‖Matrix.euclideanEquiv P‖ ^ (4 : ℝ) := by
    by_cases h : ‖Matrix.euclideanEquiv P‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg _) h hq).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hq4).trans
        (le_add_of_nonneg_left zero_le_one)
  linarith [quarticDensity_coercive_four β x P]

/-- On the derivative matrix of the shear, the density is `(3 + 4 x₁²)² - β`. -/
theorem quarticDensity_shear_derivative (β : ℝ) (x : ℝ^3) :
    quarticDensity β (!![(1 : ℝ), 2 * x 1, 0; 0, 1, 0; 0, 0, 1], x) =
      (3 + 4 * x 1 ^ 2) ^ 2 - β := by
  change ‖Matrix.euclideanEquiv _‖ ^ 4 - β = _
  rw [show ‖Matrix.euclideanEquiv
      (!![(1 : ℝ), 2 * x 1, 0; 0, 1, 0; 0, 0, 1])‖ ^ 4 =
      (‖Matrix.euclideanEquiv
        (!![(1 : ℝ), 2 * x 1, 0; 0, 1, 0; 0, 0, 1])‖ ^ 2) ^ 2 by cas,
    Matrix.norm_euclideanEquiv_sq]
  simp only [Fin.sum_univ_three]
  cas

/-- The density of the shear's Sobolev field equals the computed polynomial. -/
theorem quarticDensity_shearData_ae (β : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (fun x ↦ quarticDensity β (Matrix.euclideanEquiv.symm
      (∇ (shearData p) x), x)) =ᵐ[domainMeasure 3 (domain 3)]
        fun x ↦ (3 + 4 * x 1 ^ 2) ^ 2 - β := by
  filter_upwards [shearData_gradient_ae p] with x hx
  rw [hx, quarticDensity_shear_derivative]

/-- The shear has finite quartic energy. -/
theorem quarticDensity_shearData_finite (β : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    vectorWkpIntegral (fun x z ↦ quarticDensity β (Matrix.euclideanEquiv.symm z.2, x))
      (shearData p) ≠ ⊤ := by
  let := isFiniteMeasure_domainMeasure_of_isBounded (bounded_domain 3)
  have hc : Continuous (fun x : ℝ^3 ↦ (3 + 4 * x 1 ^ 2) ^ 2 - β) := by fun_prop
  have hp := WeakChangeOfVariables.memLp_top_on_bounded_of_continuous (bounded_domain 3) hc
  have hint := (hp.mono_exponent (show (1 : ℝ≥0∞) ≤ ⊤ from le_top)).integrable le_rfl
  rw [vectorWkpIntegral_eq_integral (hint.congr (quarticDensity_shearData_ae β p).symm)]
  exact EReal.coe_ne_top _

end PDE.Examples.Constraints.Determinant
