/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Coefficients for higher-order half-space reflection

For order `k`, use the `k + 1` negative normal dilations `-1, …, -(k + 1)`.
The inverse Vandermonde matrix supplies weights whose moments of orders `0, …, k`
are all one. Consequently the weighted reflection reproduces every normal jet through
order `k`. No boundary condition on the source jet is needed.

Evans, *Partial Differential Equations*, §5.4, uses the two-term reflection
`-3u(x', -xₙ) + 4u(x', -xₙ/2)`, whose weights have moments of orders `0` and `1` equal to
one, and remarks that `W^{k,p}` for `k > 2` needs a more complicated higher-order reflection;
the coefficients here give such a reflection for every `k`. The moment identities alone
do not assert that the piecewise extension has global weak derivatives.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.4, Theorem 1, pp. 268-271, whose proof extends `C¹`
  functions by the two-term reflection (3), p. 269, and Remarks (i) and (ii), p. 271: the same
  operator is bounded on `W^{2,p}` when the boundary is `C²`, and `k > 2` needs a more complicated
  higher-order reflection.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace.HigherOrderReflection

open scoped Matrix

/-- The negative normal dilation at the `j`th reflection node. -/
def reflectionNode (k : ℕ) (j : Fin (k + 1)) : ℝ :=
  -((j : ℕ) + 1 : ℝ)

/-- All reflection nodes send the negative normal half-line to the positive half-line. -/
theorem reflectionNode_neg (k : ℕ) (j : Fin (k + 1)) :
    reflectionNode k j < 0 := by
  unfold reflectionNode
  apply neg_neg_of_pos
  positivity

/-- Distinct dilation factors make the moment system nonsingular. -/
theorem reflectionNode_injective (k : ℕ) : Function.Injective (reflectionNode k) := by
  intro i j hij
  apply Fin.ext
  exact_mod_cast add_right_cancel (neg_injective hij)

/-- Weights obtained by solving the normal-jet moment system. -/
def reflectionCoeff (k : ℕ) : Fin (k + 1) → ℝ :=
  (fun _ ↦ 1) ᵥ* (Matrix.vandermonde (reflectionNode k))⁻¹

/-- The weighted reflected normal derivative of every order at most `k` has coefficient one. -/
theorem sum_reflectionCoeff_mul_pow (k : ℕ) (r : ℕ) (hr : r ≤ k) :
    ∑ j, reflectionCoeff k j * reflectionNode k j ^ r = 1 := by
  have hdet : IsUnit (Matrix.vandermonde (reflectionNode k)).det :=
    isUnit_iff_ne_zero.mpr
      (Matrix.det_vandermonde_ne_zero_iff.mpr (reflectionNode_injective k))
  have h := congrFun
    (show reflectionCoeff k ᵥ* Matrix.vandermonde (reflectionNode k) = (fun _ ↦ 1) by
      rw [reflectionCoeff, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet,
        Matrix.vecMul_one]) (⟨r, Nat.lt_succ_of_le hr⟩ : Fin (k + 1))
  exact h

/-- The zeroth moment preserves boundary values. -/
@[simp] theorem sum_reflectionCoeff (k : ℕ) :
    ∑ j, reflectionCoeff k j = 1 := by
  simpa using sum_reflectionCoeff_mul_pow k 0 (Nat.zero_le k)

/-- The moment equations uniquely determine the reflection weights. -/
theorem reflectionCoeff_unique (k : ℕ) (c : Fin (k + 1) → ℝ)
    (hc : ∀ r : Fin (k + 1), ∑ j, c j * reflectionNode k j ^ (r : ℕ) = 1) :
    c = reflectionCoeff k := by
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (reflectionNode_injective k)
  intro r
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [hc r, sum_reflectionCoeff_mul_pow k r (Nat.le_of_lt_succ r.isLt), sub_self]

/-- Matching scalar moments reproduces jets with values in any real vector space. -/
theorem sum_reflectionCoeff_smul_jet {E : Type*} [AddCommGroup E] [Module ℝ E]
    (k r : ℕ) (hr : r ≤ k) (v : E) :
    ∑ j, (reflectionCoeff k j * reflectionNode k j ^ r) • v = v := by
  rw [← Finset.sum_smul, sum_reflectionCoeff_mul_pow k r hr, one_smul]

end SobolevSpace.GraphSpace.HigherOrderReflection
