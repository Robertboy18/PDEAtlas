/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.CanonicalForm2D.Equation
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# The full wave expression after the sum/difference substitution

The constructed characteristic chart can be followed by the invertible linear
sum/difference change. The full operator becomes a multiple of `w₀₀ - w₁₁`;
the two drift coefficients become their sum and difference.

`linearOperator_comp_characteristic_to_wave` is the passage of Evans, §7.2.5, from the first
canonical form (95) to (96), `w_{z₁z₁} - w_{z₂z₂} + ⋯ = 0`, by the change of variables
`z₁ = y₁ + y₂`, `z₂ = y₁ - y₂`; renaming `t = z₁`, `x = z₂` gives the second canonical form
(97), with the one-dimensional wave operator as principal part.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.5, equations (95)-(97).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace Hyperbolic.CanonicalForm2D

/-- The sum/difference substitution is smooth at every differentiability order. -/
theorem contDiffAt_sumDifferenceCoordinates (x : ℝ^2) {r : WithTop ℕ∞} :
    ContDiffAt ℝ r sumDifferenceCoordinates x := by
  refine (contDiffAt_piLp 2).mpr fun i ↦ ?_
  fin_cases i
  · exact (contDiffAt_piLp_apply 2 (i := (0 : Fin 2))).add
      (contDiffAt_piLp_apply 2 (i := (1 : Fin 2)))
  · exact (contDiffAt_piLp_apply 2 (i := (0 : Fin 2))).sub
      (contDiffAt_piLp_apply 2 (i := (1 : Fin 2)))

/-- The final linear substitution is bijective, with inverse given by the half sum
and half difference. -/
theorem sumDifferenceCoordinates_bijective : Function.Bijective sumDifferenceCoordinates := by
  constructor
  · intro x y h
    have h₀ := congrArg (fun z : ℝ^2 ↦ z 0) h
    have h₁ := congrArg (fun z : ℝ^2 ↦ z 1) h
    change x 0 + x 1 = y 0 + y 1 at h₀
    change x 0 - x 1 = y 0 - y 1 at h₁
    ext i
    fin_cases i
    · change x 0 = y 0
      linarith
    · change x 1 = y 1
      linarith
  · intro z
    refine ⟨!₂[(z 0 + z 1) / 2, (z 0 - z 1) / 2], ?_⟩
    ext i
    fin_cases i
    · change (z 0 + z 1) / 2 + (z 0 - z 1) / 2 = z 0
      cas
    · change (z 0 + z 1) / 2 - (z 0 - z 1) / 2 = z 1
      cas

private theorem partialDeriv_sumDifferenceCoordinates (i j : Fin 2) (x : ℝ^2) :
    (∂[i] (fun z ↦ sumDifferenceCoordinates z j)) x = if i = 1 ∧ j = 1 then -1 else 1 := by
  fin_cases i <;> fin_cases j
  · change (∂[0] (fun y : ℝ^2 ↦ y 0 + y 1)) x = 1
    cas
  · change (∂[0] (fun y : ℝ^2 ↦ y 0 - y 1)) x = 1
    cas
  · change (∂[1] (fun y : ℝ^2 ↦ y 0 + y 1)) x = 1
    cas
  · change (∂[1] (fun y : ℝ^2 ↦ y 0 - y 1)) x = -1
    cas

/-- The complete characteristic operator, followed by sum/difference coordinates,
has wave principal part and the corresponding sum/difference drift. -/
theorem linearOperator_comp_characteristic_to_wave (A : ℝ^2 → PrincipalPart) (b : ℝ^2 → ℝ^2)
    (c : ℝ^2 → ℝ) (Φ : ℝ^2 → ℝ^2) (x : ℝ^2) (hΦ : ContDiffAt ℝ 2 Φ x)
    (h₀ : (transformedPrincipal A Φ x).a11 = 0) (h₁ : (transformedPrincipal A Φ x).a22 = 0)
    (w : ℝ^2 → ℝ) (hw : ContDiffAt ℝ 2 w (sumDifferenceCoordinates (Φ x))) :
    linearOperator A b c ((w ∘ sumDifferenceCoordinates) ∘ Φ) x =
      2 * (transformedPrincipal A Φ x).a12 *
        ((∂[0] (∂[0] w)) (sumDifferenceCoordinates (Φ x)) -
          (∂[1] (∂[1] w)) (sumDifferenceCoordinates (Φ x))) +
      (transformedDrift A b Φ x 0 + transformedDrift A b Φ x 1) *
        (∂[0] w) (sumDifferenceCoordinates (Φ x)) +
      (transformedDrift A b Φ x 0 - transformedDrift A b Φ x 1) *
        (∂[1] w) (sumDifferenceCoordinates (Φ x)) +
      c x * w (sumDifferenceCoordinates (Φ x)) := by
  have hfirst (i : Fin 2) : (∂[i] (w ∘ sumDifferenceCoordinates)) (Φ x) =
        ∑ j : Fin 2, (∂[j] w) (sumDifferenceCoordinates (Φ x)) *
          (∂[i] (fun y ↦ sumDifferenceCoordinates y j)) (Φ x) :=
    PDE.partialDeriv_comp i w sumDifferenceCoordinates (Φ x)
      (hw.differentiableAt (by norm_num))
      ((contDiffAt_sumDifferenceCoordinates (Φ x) (r := 1)).differentiableAt (by norm_num))
  have hfirst₀ : (∂[0] (w ∘ sumDifferenceCoordinates)) (Φ x) =
        (∂[0] w) (sumDifferenceCoordinates (Φ x)) +
          (∂[1] w) (sumDifferenceCoordinates (Φ x)) := by
    simpa only [Fin.sum_univ_two, partialDeriv_sumDifferenceCoordinates, Fin.isValue,
      zero_ne_one, false_and, ↓reduceIte, mul_one] using hfirst 0
  have hfirst₁ : (∂[1] (w ∘ sumDifferenceCoordinates)) (Φ x) =
        (∂[0] w) (sumDifferenceCoordinates (Φ x)) -
          (∂[1] w) (sumDifferenceCoordinates (Φ x)) := by
    simpa only [Fin.sum_univ_two, partialDeriv_sumDifferenceCoordinates, Fin.isValue,
      zero_ne_one, true_and, ↓reduceIte, mul_one, mul_neg_one, sub_eq_add_neg] using hfirst 1
  rw [linearOperator_comp_characteristic A b c (w ∘ sumDifferenceCoordinates) Φ x
    (hw.comp _ (contDiffAt_sumDifferenceCoordinates (Φ x))) hΦ h₀ h₁,
    mixedDerivative_under_sumDifferenceCoordinates w (Φ x) hw, hfirst₀, hfirst₁]
  simp only [Function.comp_apply]
  ring

end Hyperbolic.CanonicalForm2D
