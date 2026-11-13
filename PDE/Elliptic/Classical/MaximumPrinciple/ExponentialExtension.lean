/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ExponentialExtension
public import PDE.Analysis.LinearAlgebra.ScalarBlock
public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixOperator

/-!
# Exponential extension of a matrix operator

Multiplication by the exponential of an extra coordinate absorbs a signed
potential into the drift. The exact operator identity takes no derivatives
of the coefficients and is reusable for time-dependent spatial operators.
-/

@[expose] public noncomputable section

namespace EllipticHarnack

open PDE.Analysis PDE.Common EllipticMaximum
open PDE (time)
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The principal matrix of the exponential lift. -/
def liftedPrincipal (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (p : ℝ^(n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  prependScalarBlock 1 (a (spatialPart p))

/-- The signed potential becomes the zeroth component of the lifted drift. -/
def liftedDrift (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ) (p : ℝ^(n + 1)) : ℝ^(n + 1) :=
  timeSpaceCons (1 + c (spatialPart p)) (b (spatialPart p))

/-- Exact cancellation for the matrix operator, with arbitrary signed potential. -/
theorem matrixOperator_exponentialExtension
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ)
    {u : ℝ^n → ℝ} {p : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u (spatialPart p)) :
    matrixOperator (liftedPrincipal a) (liftedDrift b c) (fun _ ↦ 0)
        (exponentialExtension u) p =
      Real.exp (time p) * matrixOperator a b c u (spatialPart p) := by
  have hd := hu.differentiableAt (by norm_num)
  have hprincipal :
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        liftedPrincipal a p i j * (∂[i] (∂[j] (exponentialExtension u))) p) =
      Real.exp (time p) *
        (u (spatialPart p) +
          ∑ i : Fin n, ∑ j : Fin n, a (spatialPart p) i j *
            (∂[i] (∂[j] u)) (spatialPart p)) := by
    simp only [liftedPrincipal, Fin.sum_univ_succ,
      prependScalarBlock_zero_zero, prependScalarBlock_zero_succ,
      prependScalarBlock_succ_zero, prependScalarBlock_succ_succ,
      zero_mul, Finset.sum_const_zero, add_zero, zero_add, one_mul,
      secondPartialDeriv_zero_exponentialExtension hu,
      secondPartialDeriv_succ_exponentialExtension, exponentialExtension]
    simp only [mul_left_comm _ (Real.exp (time p)), ← Finset.mul_sum, mul_add]
  have hdrift :
      fderiv ℝ (exponentialExtension u) p (liftedDrift b c p) =
      Real.exp (time p) *
        (u (spatialPart p) * (1 + c (spatialPart p)) +
          fderiv ℝ u (spatialPart p) (b (spatialPart p))) := by
    rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul, Fin.sum_univ_succ]
    simp only [liftedDrift, timeSpaceCons_zero, timeSpaceCons_succ,
      partialDeriv_zero_exponentialExtension hd, partialDeriv_succ_exponentialExtension,
      exponentialExtension, mul_assoc, ← Finset.mul_sum]
    simp only [PDE.fderiv_apply_eq_sum_partialDeriv_mul, mul_add]
  rw [matrixOperator_apply, hprincipal, hdrift, matrixOperator_apply]
  ring

/-- The lifted drift is bounded by the original drift and the absolute potential bound. -/
theorem norm_liftedDrift_le
    (b : ℝ^n → ℝ^n) (c : ℝ^n → ℝ) (p : ℝ^(n + 1))
    {B K : ℝ} (hb : ‖b (spatialPart p)‖ ≤ B) (hc : |c (spatialPart p)| ≤ K) :
    ‖liftedDrift b c p‖ ≤ B + 1 + K := by
  have h := norm_timeSpaceCons_le (1 + c (spatialPart p)) (b (spatialPart p))
  have habs := abs_add_le (1 : ℝ) (c (spatialPart p))
  norm_num only [abs_one] at habs
  change ‖timeSpaceCons (1 + c (spatialPart p)) (b (spatialPart p))‖ ≤ B + 1 + K
  linarith

end EllipticHarnack
