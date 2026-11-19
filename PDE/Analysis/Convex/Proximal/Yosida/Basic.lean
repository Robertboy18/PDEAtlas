/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Proximal.Resolvent
import Mathlib.Tactic.Positivity.Finset

/-!
# Yosida approximations of a multivalued subdifferential

The resolvent residual defines a single-valued approximation while the original
subdifferential remains multivalued. Its supporting-vector property gives cocoercivity,
monotonicity, the inverse-parameter Lipschitz estimate with constant `1 / λ`, and the `2 / λ`
bound of Evans, §9.6.1, Theorem 2(ii).

The approximation is Evans's `A_λ` of (7), and `yosidaApproximation_mem_subdifferential` is his
Theorem 2(iv). He obtains (ii) from (i) and the definition (7), which gives the constant
`2 / λ`; we get `1 / λ` from cocoercivity, and `norm_yosidaApproximation_sub_le_two_div` states
his form.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.1, the definition (7) of the Yosida approximation,
  Theorem 2(ii)-(iv) and steps 1-3 of its proof, pp. 563-564.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Convex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The scaled residual of the constructed subdifferential resolvent. -/
def yosidaApproximation (I : H → EReal) (hproper : IsProper I)
    (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
    (lambda : ℝ) (hlambda : 0 < lambda) (w : H) : H :=
  lambda⁻¹ • (w - resolvent I hproper hconvex hlsc lambda hlambda w)

variable {I : H → EReal} (hproper : IsProper I)
  (hconvex : Convex ℝ (realEpigraph I)) (hlsc : LowerSemicontinuous I)
  {lambda : ℝ} (hlambda : 0 < lambda)

/-- The Yosida value belongs to the subdifferential at the resolvent point. -/
theorem yosidaApproximation_mem_subdifferential (w : H) :
    yosidaApproximation I hproper hconvex hlsc lambda hlambda w ∈
      subdifferential I (resolvent I hproper hconvex hlsc lambda hlambda w) :=
  resolvent_residual_mem_subdifferential hproper hconvex hlsc hlambda w

/-- The resolvent and Yosida approximation decompose the identity. -/
theorem resolvent_add_smul_yosidaApproximation (w : H) :
    resolvent I hproper hconvex hlsc lambda hlambda w +
      lambda • yosidaApproximation I hproper hconvex hlsc lambda hlambda w = w := by
  unfold yosidaApproximation
  rw [smul_inv_smul₀ hlambda.ne']
  abel

/-- Cocoercivity of the Yosida approximation, with the exact parameter. -/
theorem yosidaApproximation_cocoercive (x y : H) :
    lambda * ‖yosidaApproximation I hproper hconvex hlsc lambda hlambda x -
        yosidaApproximation I hproper hconvex hlsc lambda hlambda y‖ ^ 2 ≤
      inner ℝ (x - y) (yosidaApproximation I hproper hconvex hlsc lambda hlambda x -
        yosidaApproximation I hproper hconvex hlsc lambda hlambda y) := by
  let J := resolvent I hproper hconvex hlsc lambda hlambda
  let A := yosidaApproximation I hproper hconvex hlsc lambda hlambda
  have hx : J x + lambda • A x = x :=
    resolvent_add_smul_yosidaApproximation hproper hconvex hlsc hlambda x
  have hy : J y + lambda • A y = y :=
    resolvent_add_smul_yosidaApproximation hproper hconvex hlsc hlambda y
  have hbalance : x - y = (J x - J y) + lambda • (A x - A y) := by
    calc
      x - y = (J x + lambda • A x) - (J y + lambda • A y) :=
        congrArg₂ (· - ·) hx.symm hy.symm
      _ = _ := by rw [smul_sub]; abel
  have hmono : 0 ≤ inner ℝ (A x - A y) (J x - J y) :=
    subdifferential_monotone hproper
      (yosidaApproximation_mem_subdifferential hproper hconvex hlsc hlambda x)
      (yosidaApproximation_mem_subdifferential hproper hconvex hlsc hlambda y)
  change lambda * ‖A x - A y‖ ^ 2 ≤ inner ℝ (x - y) (A x - A y)
  rw [hbalance, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm] at hmono
  exact le_add_of_nonneg_left hmono

/-- Monotonicity of the Yosida approximation, Evans, §9.6.1, Theorem 2(iii). -/
theorem yosidaApproximation_monotone (x y : H) :
    0 ≤ inner ℝ (x - y) (yosidaApproximation I hproper hconvex hlsc lambda hlambda x -
      yosidaApproximation I hproper hconvex hlsc lambda hlambda y) :=
  (mul_nonneg hlambda.le (sq_nonneg _)).trans
    (yosidaApproximation_cocoercive hproper hconvex hlsc hlambda x y)

/-- The Yosida approximation satisfies `‖A_λ x - A_λ y‖ ≤ λ⁻¹ ‖x - y‖`. -/
theorem norm_yosidaApproximation_sub_le (x y : H) :
    ‖yosidaApproximation I hproper hconvex hlsc lambda hlambda x -
        yosidaApproximation I hproper hconvex hlsc lambda hlambda y‖ ≤
      lambda⁻¹ * ‖x - y‖ := by
  exact norm_le_of_mul_norm_sq_le_inner hlambda
    (yosidaApproximation_cocoercive hproper hconvex hlsc hlambda x y)

/-- The Yosida approximation is Lipschitz with constant `λ⁻¹`. -/
theorem lipschitzWith_yosidaApproximation :
    LipschitzWith (NNReal.mk lambda⁻¹ (inv_nonneg.2 hlambda.le))
      (yosidaApproximation I hproper hconvex hlsc lambda hlambda) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_mk] using
    norm_yosidaApproximation_sub_le hproper hconvex hlsc hlambda x y

/-- The `2 / lambda` bound stated in Evans, §9.6.1, Theorem 2(ii). -/
theorem norm_yosidaApproximation_sub_le_two_div (x y : H) :
    ‖yosidaApproximation I hproper hconvex hlsc lambda hlambda x -
        yosidaApproximation I hproper hconvex hlsc lambda hlambda y‖ ≤
      (2 / lambda) * ‖x - y‖ := by
  refine (norm_yosidaApproximation_sub_le hproper hconvex hlsc hlambda x y).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simp only [div_eq_mul_inv]
  nlinarith [inv_nonneg.2 hlambda.le]

end PDE.Analysis.Convex
