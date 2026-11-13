/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity.Finset

/-!
# Scalar estimates for interior difference-quotient energy

Real-number steps of the interior `H²` energy estimate. `absorb_elliptic_energy` absorbs into the
coercive term the part `beta` of the ellipticity constant `alpha` spent on Young's inequality, and
`absorb_weighted_source_energy` rearranges the estimate after the source term contributes
`gamma * cutoffNorm ^ 2 / 2` times the energy. `exists_positive_absorption_parameter` chooses a
Young parameter `gamma > 0` with `gamma * cutoffNorm ^ 2 < alpha`, and
`norm_component_le_sqrt_of_weighted_energy` bounds each component of a weighted sum of squared
norms.

In Evans's proof of §6.3.1, Theorem 1, they correspond to the choices `ε = θ/2` and `ε = θ/4` in
Cauchy's inequality with `ε` in the estimates (19)-(22) of `A` and `B`, and to combining (12), (20)
and (22) into a bound for `∫ ζ² |D_k^h Du|²`, from which Evans's §5.8.2, Theorem 3(ii), gives
`Du ∈ H¹_loc`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.8.2(a), Theorem 3 (Difference quotients and weak
  derivatives), (9), p. 292; §6.3.1, proof of Theorem 1 (Interior H²-regularity), steps 4-6,
  (12)-(22), pp. 329-331.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

variable {n : ℕ}

/-- Scalar absorption step for a weak equation split into its coercive principal part and
the remaining errors. The parameter `beta` is the part of the ellipticity constant spent on
Young's inequalities. -/
theorem absorb_elliptic_energy
    {alpha beta energy principal error forcing remainder : ℝ}
    (hcoercive : alpha * energy ≤ principal)
    (hbalance : principal + error = forcing)
    (herrors : |error| + |forcing| ≤ remainder + beta * energy) :
    (alpha - beta) * energy ≤ remainder := by
  have hp : principal ≤ |error| + |forcing| := by
    have hf : forcing ≤ |forcing| := le_abs_self forcing
    have he : -error ≤ |error| := neg_le_abs error
    linarith
  nlinarith

/-- Rearrange an energy estimate after the source contributes
`gamma * cutoffNorm² / 2` times the same energy. -/
theorem absorb_weighted_source_energy
    {alpha gamma cutoffNorm energy remainder sourceLower : ℝ}
    (henergy :
      (alpha / 2) * energy ≤
        remainder + (gamma / 4) *
          (sourceLower + 2 * cutoffNorm ^ 2 * energy)) :
    ((alpha - gamma * cutoffNorm ^ 2) / 2) * energy ≤
      remainder + (gamma / 4) * sourceLower := by
  nlinarith

/-- A positive Young parameter can always be chosen small enough to absorb
the cutoff-weighted source contribution into a positive elliptic energy. -/
theorem exists_positive_absorption_parameter
    {alpha : ℝ} (halpha : 0 < alpha) (cutoffNorm : ℝ) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma * cutoffNorm ^ 2 < alpha := by
  let gamma := alpha / (2 * (cutoffNorm ^ 2 + 1))
  have hdenom : 0 < 2 * (cutoffNorm ^ 2 + 1) := by positivity
  refine ⟨gamma, div_pos halpha hdenom, ?_⟩
  dsimp only [gamma]
  rw [div_mul_eq_mul_div, div_lt_iff₀ hdenom]
  nlinarith [sq_nonneg cutoffNorm]

/-- A positive weighted bound for a finite sum of norm squares bounds each
component.  This is the final scalar step used before weak compactness. -/
theorem norm_component_le_sqrt_of_weighted_energy
    {E : Type*} [SeminormedAddCommGroup E]
    (x : Fin n → E) (i : Fin n) {weight bound : ℝ}
    (hweight : 0 < weight)
    (henergy : weight * ∑ j : Fin n, ‖x j‖ ^ 2 ≤ bound) :
    ‖x i‖ ≤ Real.sqrt (bound / weight) := by
  have hcomponent : ‖x i‖ ^ 2 ≤ ∑ j : Fin n, ‖x j‖ ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg ‖x j‖) (Finset.mem_univ i)
  have hweighted : weight * ‖x i‖ ^ 2 ≤ bound :=
    (mul_le_mul_of_nonneg_left hcomponent hweight.le).trans henergy
  apply Real.le_sqrt_of_sq_le
  exact (le_div_iff₀ hweight).2 (by simpa [mul_comm] using hweighted)

end SobolevSpace.GraphSpace
