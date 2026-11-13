/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
import PDE.Analysis.Variational.LaxMilgram

/-!
# Stability of variational inequalities

Test each solution with the other one and add the two inequalities. Strong
monotonicity then controls the distance between solutions by the difference of
their loads. The argument works in any real normed space, and the admissible
set need not be convex.

For the obstacle problem of Evans, §8.4.2, take `A u = ∫ Du · D(·) dx` on `H¹₀(U)`,
`ell = ∫ f (·) dx` and for `K` the admissible set (25); the hypotheses on `u` are then the
variational inequality (26) of his Theorem 4. Equal loads give uniqueness of the solution,
which Evans proves for the minimizer by strict convexity in his Theorem 3.

## Main results

* `norm_sub_le_of_variationalInequalities`: `‖u - v‖ ≤ ‖ell₁ - ell₂‖ / c` for solutions `u`
  and `v` with loads `ell₁` and `ell₂`, when `A` is strongly monotone at `u` and `v` with
  constant `c`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.2, (24) and (25), Theorem 3 (Existence of
  minimizer) and Theorem 4 (Variational characterization of minimizer), pp. 492-493.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis.Variational

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Solutions of variational inequalities on the same admissible set depend
Lipschitz-continuously on their loads whenever the operator is strongly
monotone at the two solutions. -/
theorem norm_sub_le_of_variationalInequalities
    (A : V → StrongDual ℝ V) (c : ℝ) (hc : 0 < c)
    {K : Set V} {u v : V} (huK : u ∈ K) (hvK : v ∈ K)
    (hmono : c * ‖u - v‖ * ‖u - v‖ ≤ (A u - A v) (u - v))
    (ell₁ ell₂ : StrongDual ℝ V)
    (hu : ∀ w ∈ K, ell₁ (w - u) ≤ A u (w - u))
    (hv : ∀ w ∈ K, ell₂ (w - v) ≤ A v (w - v)) :
    ‖u - v‖ ≤ ‖ell₁ - ell₂‖ / c := by
  have hu' := hu v hvK
  have hv' := hv u huK
  rw [← neg_sub u v, map_neg, map_neg] at hu'
  have hupper : (A u - A v) (u - v) ≤ (ell₁ - ell₂) (u - v) := by
    simp only [sub_apply]
    linarith
  exact norm_le_dual_norm_div_of_pairing (ell₁ - ell₂) c hc (u - v)
    (hmono.trans hupper)

end PDE.Analysis.Variational
