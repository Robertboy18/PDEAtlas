/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Proximal.Yosida.Basic

/-!
# Comparing two Yosida parameters

Subgradient monotonicity at the two resolvent points controls the defect between
different regularization parameters. Completing two squares gives the factor `1/4`. This is
the estimate in step 3 of Evans's proof of Theorem 3 of §9.6.2, with a common bound `M` on the
two Yosida values in place of his `|A⁰[u]|`; integrating the squared-distance derivative, as
in `PDE.Analysis.Evolution.norm_yosidaFlow_sub_sq_le`, then gives the factor `1/2` of his (23).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.2, step 3 of the proof of Theorem 3, (21)-(23),
  pp. 567-568. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {I : H → EReal}

/-- Yosida values of norm at most `M` satisfy a uniform two-parameter lower bound.
The coefficient is independent of the energy and the two state points. -/
theorem neg_mul_sq_le_inner_yosidaApproximation_sub
    (hproper : IsProper I) (hconvex : Convex ℝ (realEpigraph I))
    (hlsc : LowerSemicontinuous I) {lambda mu M : ℝ}
    (hlambda : 0 < lambda) (hmu : 0 < mu) (x y : H)
    (hx : ‖yosidaApproximation I hproper hconvex hlsc lambda hlambda x‖ ≤ M)
    (hy : ‖yosidaApproximation I hproper hconvex hlsc mu hmu y‖ ≤ M) :
    -(lambda + mu) / 4 * M ^ 2 ≤
      inner ℝ
        (yosidaApproximation I hproper hconvex hlsc lambda hlambda x -
          yosidaApproximation I hproper hconvex hlsc mu hmu y) (x - y) := by
  let p := yosidaApproximation I hproper hconvex hlsc lambda hlambda x
  let q := yosidaApproximation I hproper hconvex hlsc mu hmu y
  let z := resolvent I hproper hconvex hlsc lambda hlambda x
  let w := resolvent I hproper hconvex hlsc mu hmu y
  have hx' : z + lambda • p = x :=
    resolvent_add_smul_yosidaApproximation hproper hconvex hlsc hlambda x
  have hy' : w + mu • q = y :=
    resolvent_add_smul_yosidaApproximation hproper hconvex hlsc hmu y
  have hmono : 0 ≤ inner ℝ (p - q) (z - w) :=
    subdifferential_monotone hproper
      (yosidaApproximation_mem_subdifferential hproper hconvex hlsc hlambda x)
      (yosidaApproximation_mem_subdifferential hproper hconvex hlsc hmu y)
  have hdecomp : x - y = (z - w) + (lambda • p - mu • q) := by
    rw [← hx', ← hy']
    abel
  have hM : 0 ≤ M := (norm_nonneg p).trans hx
  have hp : ‖p‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg p]
  have hq : ‖q‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg q]
  have hpq := real_inner_le_norm p q
  have hleft : -M ^ 2 / 4 ≤ ‖p‖ ^ 2 - inner ℝ p q := by
    nlinarith [sq_nonneg (‖p‖ - ‖q‖ / 2)]
  have hright : -M ^ 2 / 4 ≤ ‖q‖ ^ 2 - inner ℝ p q := by
    nlinarith [sq_nonneg (‖q‖ - ‖p‖ / 2)]
  change _ ≤ inner ℝ (p - q) (x - y)
  have hcalc : inner ℝ (p - q) (x - y) = inner ℝ (p - q) (z - w) +
      lambda * (‖p‖ ^ 2 - inner ℝ p q) + mu * (‖q‖ ^ 2 - inner ℝ p q) := by
    rw [hdecomp]
    simp only [inner_add_right, inner_sub_right, real_inner_smul_right, inner_sub_left,
      real_inner_self_eq_norm_sq, real_inner_comm q p]
    ring
  rw [hcalc]
  nlinarith [mul_le_mul_of_nonneg_left hleft hlambda.le,
    mul_le_mul_of_nonneg_left hright hmu.le]

end PDE.Analysis.Convex
