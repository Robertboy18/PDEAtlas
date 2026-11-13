/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.LagrangeMultipliers

/-!
# Normal multipliers for a scalar constraint

Mathlib's multiplier theorem, `IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d`,
supplies a nonzero pair of coefficients. A
nonzero constraint derivative makes the objective coefficient nonzero, giving
the usual normalized Lagrange multiplier. This is a local statement on an
arbitrary real Banach space.

The conclusion `F' = lam • J'` has the form of the identity (10) in Evans, §8.4.1, Theorem 2,
where `F` is the Dirichlet energy (1) and `J` the integral constraint (2) on `H¹₀(U)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.1, (1)-(2), p. 488, and Theorem 2 (Lagrange
  multiplier), (10), p. 489.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.CalculusOfVariations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- At a constrained local extremum with nonzero constraint derivative, the
objective derivative is a scalar multiple of the constraint derivative. -/
theorem exists_multiplier_of_hasStrictFDerivAt
    {F J : E → ℝ} {F' J' : StrongDual ℝ E} {u : E}
    (hmin : IsLocalExtrOn F {v | J v = J u} u)
    (hF : HasStrictFDerivAt F F' u) (hJ : HasStrictFDerivAt J J' u)
    (hJne : J' ≠ 0) :
    ∃ lam : ℝ, F' = lam • J' := by
  obtain ⟨a, b, hab, heq⟩ := hmin.exists_multipliers_of_hasStrictFDerivAt_1d hJ hF
  have hb : b ≠ 0 := by
    intro hb
    have ha : a = 0 := by
      have hz : a • J' = 0 := by simpa [hb] using heq
      exact (smul_eq_zero.mp hz).resolve_right hJne
    exact hab (by simp [ha, hb])
  refine ⟨-a / b, ?_⟩
  ext v
  have hv := DFunLike.congr_fun heq v
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply] at hv ⊢
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hb).mpr
  nlinarith

end PDE.CalculusOfVariations
