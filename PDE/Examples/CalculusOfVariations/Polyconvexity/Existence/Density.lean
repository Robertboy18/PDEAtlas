/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Polyconvexity.Determinant.Existence
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Mul
import CAS.ExactTactic

import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Coercive quartic energies that are not convex in the gradient

The lift `F(P,r) = |P|⁴ + 4r - 7` is convex in the independent matrix and scalar.
On the determinant graph it violates midpoint convexity, but a polynomial
sum-of-squares identity gives Frobenius coercivity at exponent four
(`quarticDensity_coercive_four`) and at exponent `5 / 2`.
-/

@[expose] public noncomputable section

open Set
open scoped Matrix.Norms.Elementwise

namespace PDE.Examples.Polyconvexity.Existence

/-- The five independent coordinates of the quartic convex lift. -/
def quarticPolynomial (v : ℝ^5) : ℝ :=
  (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) ^ 2 + 4 * v 4 - 7

/-- `quarticPolynomial` is `C¹`. -/
theorem quarticPolynomial_contDiff : ContDiff ℝ 1 quarticPolynomial := by
  cas

/-- The density `F(P, r) = ‖P‖⁴ + 4r - 7`, written through the four entries of `P` and
the independent scalar `r`. -/
def quarticDensity
    (t : (ℝ^2 × ℝ^2) × (Matrix (Fin 2) (Fin 2) ℝ × ℝ)) : ℝ :=
  quarticPolynomial (WithLp.toLp 2
    ![t.2.1 0 0, t.2.1 0 1, t.2.1 1 0, t.2.1 1 1, t.2.2])

/-- The density is `C¹` in all variables. -/
theorem quarticDensity_contDiff : ContDiff ℝ 1 quarticDensity := by
  apply quarticPolynomial_contDiff.comp
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i <;> dsimp <;> fun_prop

/-- Squared Frobenius norm is the sum of the four squared entries. -/
theorem norm_euclideanEquiv_two_sq (P : Matrix (Fin 2) (Fin 2) ℝ) :
    ‖Matrix.euclideanEquiv P‖ ^ 2 =
      P 0 0 ^ 2 + P 0 1 ^ 2 + P 1 0 ^ 2 + P 1 1 ^ 2 := by
  simpa only [Fin.sum_univ_two, add_assoc] using Matrix.norm_euclideanEquiv_sq P

/-- The density is `‖P‖⁴ + 4r - 7`. -/
theorem quarticDensity_eq (x s : ℝ^2) (P : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) :
    quarticDensity ((x, s), (P, r)) = ‖Matrix.euclideanEquiv P‖ ^ 4 + 4 * r - 7 := by
  change (P 0 0 ^ 2 + P 0 1 ^ 2 + P 1 0 ^ 2 + P 1 1 ^ 2) ^ 2 + 4 * r - 7 = _
  rw [← norm_euclideanEquiv_two_sq]
  cas

/-- The density is convex in the pair `(P, r)`. -/
theorem quarticDensity_convex (x s : ℝ^2) :
    ConvexOn ℝ univ (fun R : Matrix (Fin 2) (Fin 2) ℝ × ℝ ↦
      quarticDensity ((x, s), R)) := by
  let a : (Matrix (Fin 2) (Fin 2) ℝ × ℝ) →ₗ[ℝ] ℝ^4 :=
    Matrix.euclideanEquiv.toLinearMap.comp (LinearMap.fst ℝ _ _)
  have hn : ConvexOn ℝ univ (fun R : Matrix (Fin 2) (Fin 2) ℝ × ℝ ↦
      ‖Matrix.euclideanEquiv R.1‖ ^ 4) := by
    convert ((convexOn_univ_norm : ConvexOn ℝ univ (norm : ℝ^4 → ℝ)).pow
      (fun _ _ ↦ norm_nonneg _) 4).comp_linearMap a using 1
    · exact preimage_univ.symm
    · rfl
  have hr := ((LinearMap.snd ℝ (Matrix (Fin 2) (Fin 2) ℝ) ℝ).convexOn
    convex_univ).smul (by norm_num : 0 ≤ (4 : ℝ))
  have heq : (fun R : Matrix (Fin 2) (Fin 2) ℝ × ℝ ↦ quarticDensity ((x, s), R)) =
      fun R ↦ ‖Matrix.euclideanEquiv R.1‖ ^ 4 + 4 * R.2 - 7 :=
    funext fun R ↦ quarticDensity_eq x s R.1 R.2
  rw [heq]
  convert (hn.add hr).add_const (-7) using 1
  funext R
  exact sub_eq_add_neg _ _

/-- On the determinant graph, `F(P, det P) - (‖P‖⁴ / 2 - 9)` is a sum of squares. -/
theorem quarticDensity_coercivity_identity (x s : ℝ^2)
    (P : Matrix (Fin 2) (Fin 2) ℝ) :
    quarticDensity ((x, s), (P, P.det)) - (‖Matrix.euclideanEquiv P‖ ^ 4 / 2 - 9) =
      (‖Matrix.euclideanEquiv P‖ ^ 2 - 2) ^ 2 / 2 +
        2 * ((P 0 0 + P 1 1) ^ 2 + (P 0 1 - P 1 0) ^ 2) := by
  rw [quarticDensity_eq, Matrix.det_fin_two]
  rw [show ‖Matrix.euclideanEquiv P‖ ^ 4 = (‖Matrix.euclideanEquiv P‖ ^ 2) ^ 2 by cas,
    norm_euclideanEquiv_two_sq]
  cas

/-- Frobenius fourth-power coercivity holds on the full determinant graph. -/
theorem quarticDensity_coercive_four (x s : ℝ^2) (P : Matrix (Fin 2) (Fin 2) ℝ) :
    (1 / 2 : ℝ) * ‖Matrix.euclideanEquiv P‖ ^ (4 : ℝ) - 9 ≤
      quarticDensity ((x, s), (P, P.det)) := by
  rw [Real.rpow_ofNat]
  have h := quarticDensity_coercivity_identity x s P
  have h₁ := sq_nonneg (‖Matrix.euclideanEquiv P‖ ^ 2 - 2)
  have h₂ := sq_nonneg (P 0 0 + P 1 1)
  have h₃ := sq_nonneg (P 0 1 - P 1 0)
  linarith

/-- Coercivity on the determinant graph at exponent `5 / 2`, with shift `19 / 2`. -/
theorem quarticDensity_coercive_five_halves (x s : ℝ^2)
    (P : Matrix (Fin 2) (Fin 2) ℝ) :
    (1 / 2 : ℝ) * ‖Matrix.euclideanEquiv P‖ ^ (5 / 2 : ℝ) - 19 / 2 ≤
      quarticDensity ((x, s), (P, P.det)) := by
  have hpow : ‖Matrix.euclideanEquiv P‖ ^ (5 / 2 : ℝ) ≤
      1 + ‖Matrix.euclideanEquiv P‖ ^ (4 : ℝ) := by
    by_cases h : ‖Matrix.euclideanEquiv P‖ ≤ 1
    · exact (Real.rpow_le_one (norm_nonneg _) h (by norm_num)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (norm_nonneg _) _))
    · exact (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (by norm_num :
        (5 / 2 : ℝ) ≤ 4)).trans (le_add_of_nonneg_left zero_le_one)
  linarith [quarticDensity_coercive_four x s P]

/-- The determinant-graph density is not convex in the gradient. -/
theorem quarticDensity_not_convex :
    ¬ ConvexOn ℝ univ (fun P : Matrix (Fin 2) (Fin 2) ℝ ↦
      quarticDensity ((0, 0), (P, P.det))) := by
  intro h
  have hconv := h.2
  have hmid := hconv (x := !![(1 / 2 : ℝ), 0; 0, -1 / 2]) (mem_univ _)
    (y := !![(-1 / 2 : ℝ), 0; 0, 1 / 2]) (mem_univ _)
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  norm_num [quarticDensity, quarticPolynomial, Matrix.det_fin_two,
    Matrix.add_apply, Matrix.smul_apply] at hmid

/-- The lift has no lower bound on independent matrix–scalar pairs. -/
theorem quarticDensity_no_global_lower_bound (b : ℝ) :
    ∃ r : ℝ, quarticDensity ((0, 0), ((0 : Matrix (Fin 2) (Fin 2) ℝ), r)) < b := by
  refine ⟨(b + 6) / 4, ?_⟩
  change (0 ^ 2 + 0 ^ 2 + 0 ^ 2 + 0 ^ 2) ^ 2 + 4 * ((b + 6) / 4) - 7 < b
  have h : (0 : ℝ) ^ 2 + 4 * ((b + 6) / 4) - 7 = b - 1 := by cas
  norm_num at h ⊢
  linarith

end PDE.Examples.Polyconvexity.Existence
