/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.HamiltonJacobi.HopfLax.Variational
public import PDE.Hyperbolic.HamiltonJacobi.OneDimensional.HopfLax

/-!
# Identification with the scalar formula

On `ℝ`, the velocity form of `value` agrees with the scalar Hopf–Lax formula
at positive time.

Both are the Hopf–Lax formula (21) of Evans, §3.3.2(b), Theorem 4, with the cost the Legendre
transform (13) of `H`: `value` minimizes over velocities `(x - y)/t`, and the scalar formula over
footpoints `y`. `superlinear_scalar_legendre` gives the superlinearity (12) that `value` assumes
of the cost.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.3.2(a), equations (12)-(13); §3.3.2(b),
  Theorem 4, formula (21).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace HamiltonJacobi.HopfLax

set_option linter.missingDocs true

/-- The velocity parametrization reproduces the scalar
Hopf–Lax formula after the footpoint change of variables. -/
theorem value_scalar_legendre_eq (H g : ℝ → ℝ) {t : ℝ} (ht : t ≠ 0) (x : ℝ) :
    value (HopfLax1D.legendreTransform H) g t x = HopfLax1D.hopfLax H g t x := by
  rw [value_eq_inf_footpoints _ _ ht]
  simp only [HopfLax1D.hopfLax, HopfLax1D.hopfLaxIntegrand,
    smul_eq_mul, div_eq_mul_inv, mul_comm t⁻¹]

/-- Scalar Legendre finiteness gives the multidimensional growth hypothesis. -/
theorem superlinear_scalar_legendre {H : ℝ → ℝ} (hH : HopfLax1D.LegendreFinite H) :
    Superlinear (HopfLax1D.legendreTransform H) := by
  intro A
  refine ⟨max (H A) (H (-A)), fun q ↦ ?_⟩
  simpa only [Real.norm_eq_abs] using HopfLax1D.legendreTransform_lower_bound_abs hH A q

end HamiltonJacobi.HopfLax

end
