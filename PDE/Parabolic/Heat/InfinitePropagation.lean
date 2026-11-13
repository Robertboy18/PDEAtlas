/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.InitialValue
import Mathlib.MeasureTheory.Measure.Haar.Unique
import PDE.Parabolic.Heat.Kernel.Integrability

/-!
# Infinite propagation for the heat equation

Strict positivity at every positive time for nonnegative, nontrivial bounded continuous initial
data. This is the infinite propagation speed of Evans's §2.3.1(b): the Gaussian kernel is positive
everywhere, so the heat-kernel solution is positive at every point once `g ≥ 0` is positive
somewhere.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.1(b), Infinite propagation speed, pp. 48-49.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise
open PDE.Common

variable {n : ℕ}

/-- A nonnegative, nontrivial bounded continuous datum produces an everywhere-positive heat
profile at every positive time. This is Evans's infinite-propagation phenomenon for the
heat-kernel solution. -/
theorem initialValueSolution_pos_of_nonneg_of_exists_pos (g : ℝ^n → ℝ)
    (hg_cont : Continuous g) (hg_bdd : ∃ M, ∀ x, |g x| ≤ M)
    (hg_nonneg : ∀ x, 0 ≤ g x) (hg_pos : ∃ x₀, 0 < g x₀) :
    ∀ x t, 0 < t → 0 < initialValueSolution (n := n) g x t := by
  intro x t ht
  obtain ⟨M, hM⟩ := hg_bdd
  obtain ⟨x₀, hx₀⟩ := hg_pos
  have hkernel := (fundamentalSolutionHeat_integrable (n := n) t ht).comp_sub_left x
  have hint : MeasureTheory.Integrable
      (fun y : ℝ^n ↦ fundamentalSolutionHeat (x - y) t * g y) :=
    hkernel.mul_bdd hg_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y ↦ by
        simpa only [Real.norm_eq_abs] using hM y)
  have hcont : Continuous
      (fun y : ℝ^n ↦ fundamentalSolutionHeat (x - y) t * g y) := by
    simp only [fundamentalSolutionHeat, ite_eq_right (not_le.mpr ht)]
    fun_prop
  -- A continuous nonnegative integrand that is positive somewhere has positive integral.
  have hpos := MeasureTheory.integral_pos_of_integrable_nonneg_nonzero hcont hint
    (fun y ↦ mul_nonneg (fundamentalSolutionHeat_pos (x - y) t ht).le (hg_nonneg y))
    (mul_pos (fundamentalSolutionHeat_pos (x - x₀) t ht) hx₀).ne'
  simpa only [initialValueSolution, ite_eq_right (not_le.mpr ht)] using hpos

end HeatEquation
