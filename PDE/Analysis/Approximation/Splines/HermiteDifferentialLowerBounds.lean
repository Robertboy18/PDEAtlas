/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.HermiteDifferentialControls
import CAS.ExactTactic

/-!
# Affine lower bounds for Hermite differential expressions

An affine comparison keeps a vanishing endpoint in the estimate. This is useful
when a positive constant lower bound would fail at the endpoint itself.
The proof uses the affine reproduction property of the cubic Bernstein basis.
-/

@[expose] public section

noncomputable section

open Polynomial Set

namespace CAS.Splines

/-- Lower controls for an affine function bound the differential expression
throughout a closed Hermite panel. The differential controls carry a factor of
three, which appears on both sides of the control comparison. -/
theorem affine_le_hermite_differential_of_controls
    (a b d center left h A B da db s r : ℝ) (hh : h ≠ 0) {z : ℝ}
    (hz : z ∈ Icc 0 1)
    (hc : ∀ k : Fin 4, 3 * (s * (left + (k.val : ℝ) * h / 3) + r) ≤
      hermiteDifferentialControl a b d ((left - center) / h)
        A B (h * da) (h * db) k) :
    let p := hermitePolynomial left h A B da db
    let x := left + h * z
    s * x + r ≤ a * p.eval x + b * (x - center) * polynomialJet 1 p x +
      d * (x - center) ^ 2 * polynomialJet 2 p x := by
  dsimp only
  have hc' (k : Fin 4) : (3 * s) * (left + (k.val : ℝ) * h / 3) + 3 * r ≤
      hermiteDifferentialControl a b d ((left - center) / h)
        A B (h * da) (h * db) k := by
    nlinarith [hc k]
  have hb := affine_le_bernstein_cubic hz hc'
  simp only [hermiteDifferentialControl] at hb
  rw [← cubicDifferentialControl_identity] at hb
  rw [hermitePolynomial_eval, hermitePolynomial_first_bernstein _ _ _ _ _ _ _ hh,
    hermitePolynomial_second_affine _ _ _ _ _ _ _ hh]
  have hn : s * (left + h * z) + r ≤
      a * (A + h * da * z + (3 * (B - A) - 2 * (h * da) - h * db) * z ^ 2 +
        (2 * (A - B) + h * da + h * db) * z ^ 3) +
      b * ((left - center) / h + z) *
        (h * da + 2 * (3 * (B - A) - 2 * (h * da) - h * db) * z +
          3 * (2 * (A - B) + h * da + h * db) * z ^ 2) +
      d * ((left - center) / h + z) ^ 2 *
        (2 * (3 * (B - A) - 2 * (h * da) - h * db) +
          6 * (2 * (A - B) + h * da + h * db) * z) := by linarith
  convert hn using 1
  unfold hermiteValue
  cas using hh

end CAS.Splines
