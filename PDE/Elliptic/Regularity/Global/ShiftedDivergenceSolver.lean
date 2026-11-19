/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.ShiftedDivergenceForm
public import PDE.Elliptic.Variational.DivergenceSolution

/-!
# Bounded weak solvers for the full shifted operator

For every shift at or above the explicit Gårding threshold `coerciveShift`, the Lax-Milgram theorem
gives a bounded map from `L²` to `H¹₀` (`fullDivergenceWeakSolveCLM`) with norm at most `2 / α`
(`norm_fullDivergenceWeakSolveCLM_apply_le`), and every weak solution at such a shift is its value
(`eq_fullDivergenceWeakSolveCLM`). This is Evans's §6.2.2, Theorem 3 (First Existence Theorem for
weak solutions), whose shift comes from the energy estimate of Theorem 2. The change-of-shift
identity `isWeakShiftedFullDivergenceSolution_change_shift` also represents solutions at arbitrary
shifts through this coercive solver, with an additional `L²` load proportional to the solution
itself.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.2.1, Theorem 1 (Lax-Milgram Theorem) and its proof,
  pp. 315-317; §6.2.2, Theorem 2 (Energy estimates), p. 318, and Theorem 3 (First Existence Theorem
  for weak solutions), p. 319.
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Sobolev

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set PDE.Analysis.Variational
open scoped ENNReal SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

local notation "L2" => DerivLp n 2 Ω

variable (a : Fin n → Fin n → DerivLp n ∞ Ω)
  (b : Fin n → DerivLp n ∞ Ω) (c : DerivLp n ∞ Ω)

/-- Changing the scalar shift changes only the zeroth-order forcing.
This identity needs no sign condition on either shift. -/
theorem isWeakShiftedFullDivergenceSolution_change_shift
    (lambda mu : ℝ) (f : L2) (u : H¹₀(Ω)) :
    IsWeakShiftedFullDivergenceSolution a b c lambda f 0 u ↔
      IsWeakShiftedFullDivergenceSolution a b c mu
        (f + (mu - lambda) • baseCoordCLM u) 0 u := by
  constructor <;> intro hu
  · apply (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution
      hu.isOpen a b c mu _ 0 u).1
    have h := (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution
      hu.isOpen a b c lambda f 0 u).2 hu
    intro v
    have hv := h v
    simp only [shiftedDivergenceForm_apply, generalizedLoad_apply, Pi.zero_apply,
      inner_zero_left, Finset.sum_const_zero, add_zero, inner_add_left,
      real_inner_smul_left] at hv ⊢
    linarith
  · apply (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution
      hu.isOpen a b c lambda f 0 u).1
    have h := (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution
      hu.isOpen a b c mu _ 0 u).2 hu
    intro v
    have hv := h v
    simp only [shiftedDivergenceForm_apply, generalizedLoad_apply, Pi.zero_apply,
      inner_zero_left, Finset.sum_const_zero, add_zero, inner_add_left,
      real_inner_smul_left] at hv ⊢
    linarith

variable {alpha beta gamma mu : ℝ}
  (hA : IntegratedElliptic (multiplicationCoefficientOperator a) alpha)
  (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
  (hb : ∀ i, ‖b i‖ ≤ beta) (hc : ‖c‖ ≤ gamma)
  (hmu : coerciveShift (n := n) alpha beta gamma ≤ mu)

/-- The full divergence-form `L² → H¹₀` solver at any shift at or above the
explicit Gårding threshold. Its boundedness follows from the Lax-Milgram theorem. -/
def fullDivergenceWeakSolveCLM : L2 →L[ℝ] H¹₀(Ω) := by
  let form : H¹₀(Ω) →L[ℝ] H¹₀(Ω) →L[ℝ] ℝ :=
    shiftedDivergenceForm
      (multiplicationCoefficientOperator a)
      (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu
  have hcoercive : IsCoercive form :=
    shiftedDivergenceForm_isCoercive_of_coerciveShift_le _ _ _ hA
      (lowerOrderBounds_multiplication b c hbeta hgamma hb hc) hmu
  exact (solveCLM form hcoercive).comp loadFunctionalCLM

/-- The bounded weak solver satisfies the full distributional equation. -/
theorem fullDivergenceWeakSolveCLM_isWeakSolution
    (hOpen : IsOpen Ω) (f : L2) :
    IsWeakShiftedFullDivergenceSolution a b c mu f 0
      (fullDivergenceWeakSolveCLM a b c hA hbeta hgamma hb hc hmu f) := by
  apply (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution
    hOpen a b c mu f 0 _).1
  have h := solveCLM.isWeakSolution
    (shiftedDivergenceForm
      (multiplicationCoefficientOperator a)
      (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu)
    (shiftedDivergenceForm_isCoercive_of_coerciveShift_le _ _ _ hA
      (lowerOrderBounds_multiplication b c hbeta hgamma hb hc) hmu)
    (loadFunctionalCLM (n := n) (Ω := Ω) f)
  simpa [fullDivergenceWeakSolveCLM, generalizedLoad] using h

/-- The weak solver has the same `2 / alpha` bound at every shift at or above the
Gårding threshold. -/
theorem norm_fullDivergenceWeakSolveCLM_apply_le (f : L2) :
    ‖fullDivergenceWeakSolveCLM a b c hA hbeta hgamma hb hc hmu f‖ ≤
      (2 / alpha) * ‖f‖ := by
  let form := shiftedDivergenceForm
    (multiplicationCoefficientOperator a)
    (multiplicationFirstOrderOperator b) (multiplicationZeroOrderOperator c) mu
  have hbc := lowerOrderBounds_multiplication b c hbeta hgamma hb hc
  have hcoercive : IsCoercive form :=
    shiftedDivergenceForm_isCoercive_of_coerciveShift_le _ _ _ hA hbc hmu
  have h := solve.norm_le_div form hcoercive (alpha / 2)
    (div_pos hA.1 (by norm_num))
    (shiftedDivergenceForm_coercive_bound_of_coerciveShift_le _ _ _ hA hbc hmu)
    (loadFunctional f)
  have hload := norm_loadFunctional_le f
  change ‖solve form hcoercive (loadFunctional f)‖ ≤ _
  calc
    ‖solve form hcoercive (loadFunctional f)‖ ≤ ‖loadFunctional f‖ / (alpha / 2) := h
    _ ≤ ‖f‖ / (alpha / 2) :=
      div_le_div_of_nonneg_right hload (div_nonneg hA.1.le (by norm_num))
    _ = (2 / alpha) * ‖f‖ := by simp [div_eq_mul_inv, mul_comm]

/-- Uniqueness identifies every weak solution at a coercive shift with the
bounded solver. -/
theorem eq_fullDivergenceWeakSolveCLM
    (f : L2) {u : H¹₀(Ω)}
    (hu : IsWeakShiftedFullDivergenceSolution a b c mu f 0 u) :
    u = fullDivergenceWeakSolveCLM a b c hA hbeta hgamma hb hc hmu f := by
  have hcoercive := shiftedDivergenceForm_isCoercive_of_coerciveShift_le _ _ _ hA
    (lowerOrderBounds_multiplication b c hbeta hgamma hb hc) hmu
  apply IsWeakSolution.unique _ hcoercive (generalizedLoad f 0)
  · exact (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution
      hu.isOpen a b c mu f 0 u).2 hu
  · exact (isWeakSolution_iff_isWeakShiftedFullDivergenceSolution
      hu.isOpen a b c mu f 0 _).2
      (fullDivergenceWeakSolveCLM_isWeakSolution
        a b c hA hbeta hgamma hb hc hmu hu.isOpen f)

end SobolevSpace.GraphSpace
