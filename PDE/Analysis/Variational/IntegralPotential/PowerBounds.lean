/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Variational.IntegralPotential.Hilbert
public import PDE.Analysis.MeasureTheory.LpNorm

/-!
# Power bounds for integral energies

Pointwise upper and lower power bounds for a scalar potential give the
corresponding norm bounds for the pulled-back Hilbert energy. The inclusion is
an arbitrary continuous linear map into `Lᵖ`. These are the two estimates that Evans derives
from (25) in step 5 of the proof of §8.5.2, Theorem 3: `energy_lower_bound_opNorm` is
`I[u] ≥ ‖u‖² / 2 - C ‖u‖^{p+1}`, with the operator norm of `J` in place of his Sobolev
constant, and `energy_upper_bound` is `I[v] ≤ ‖v‖² / 2 - a ∫ |v|^{p+1} dx`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.5.2, the hypothesis (25), p. 507, and step 5 of the
  proof of Theorem 3 (Existence), p. 511. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PDE.Analysis.Variational.IntegralPotential

variable {α H : Type*} [MeasurableSpace α]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {G : ℝ → ℝ} {a A : ℝ}

omit [Fact (1 ≤ p)] in
/-- A homogeneous power bound makes the scalar potential integrable at each
`Lᵖ` function, even when the underlying measure is infinite. -/
theorem integrable_of_power_bound (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    (hc : Continuous G) (hG : ∀ z, |G z| ≤ A * |z| ^ p.toReal) (u : Lp ℝ p μ) :
    Integrable (fun x ↦ G (u x)) μ := by
  apply (Lp.memLp u).integrable_comp_of_norm_rpow_le hp_zero hp_top
    (G := fun _ ↦ G) (C := A)
    (hc.measurable.comp measurable_snd) (integrable_zero α ℝ μ)
  refine ae_of_all μ ?_
  intro x z
  simpa only [Real.norm_eq_abs, Pi.zero_apply, zero_add] using hG z

/-- The upper potential bound gives a lower bound for the Hilbert energy. -/
theorem energy_lower_bound
    (J : H →L[ℝ] Lp ℝ p μ) (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    (hc : Continuous G) (hG : ∀ z, |G z| ≤ A * |z| ^ p.toReal) (u : H) :
    (1 / 2 : ℝ) * ‖u‖ ^ 2 - A * ‖J u‖ ^ p.toReal ≤ energy J G u := by
  apply sub_le_sub_left
  rw [Lp.norm_rpow_eq_integral hp_zero hp_top, ← integral_const_mul]
  exact integral_mono_ae (integrable_of_power_bound hp_zero hp_top hc hG (J u))
    (((Lp.memLp (J u)).integrable_norm_rpow hp_zero hp_top).const_mul A)
    (ae_of_all μ fun x ↦ (le_abs_self _).trans (hG (J u x)))

/-- The inclusion norm supplies a lower bound in the Hilbert norm alone. -/
theorem energy_lower_bound_opNorm
    (J : H →L[ℝ] Lp ℝ p μ) (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    (hc : Continuous G) (hA : 0 ≤ A)
    (hG : ∀ z, |G z| ≤ A * |z| ^ p.toReal) (u : H) :
    (1 / 2 : ℝ) * ‖u‖ ^ 2 - (A * ‖J‖ ^ p.toReal) * ‖u‖ ^ p.toReal ≤
      energy J G u := by
  apply le_trans _ (energy_lower_bound J hp_zero hp_top hc hG u)
  apply sub_le_sub_left
  rw [mul_assoc, ← Real.mul_rpow (norm_nonneg J) (norm_nonneg u)]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (norm_nonneg _) (J.le_opNorm u) ENNReal.toReal_nonneg) hA

/-- The lower potential bound gives an upper bound for the energy along every
vector, using the nonzero `Lᵖ` norm in the escape argument. -/
theorem energy_upper_bound
    (J : H →L[ℝ] Lp ℝ p μ) (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    (hc : Continuous G) (hG : ∀ z, |G z| ≤ A * |z| ^ p.toReal)
    (hlower : ∀ z, a * |z| ^ p.toReal ≤ G z) (u : H) :
    energy J G u ≤ (1 / 2 : ℝ) * ‖u‖ ^ 2 - a * ‖J u‖ ^ p.toReal := by
  apply sub_le_sub_left
  rw [Lp.norm_rpow_eq_integral hp_zero hp_top, ← integral_const_mul]
  exact integral_mono_ae
    (((Lp.memLp (J u)).integrable_norm_rpow hp_zero hp_top).const_mul a)
    (integrable_of_power_bound hp_zero hp_top hc hG (J u))
    (ae_of_all μ fun x ↦ hlower (J u x))

end PDE.Analysis.Variational.IntegralPotential
