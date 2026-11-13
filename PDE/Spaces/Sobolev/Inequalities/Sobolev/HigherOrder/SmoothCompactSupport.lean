/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.Exponent

/-!
# Higher-order Sobolev inequality for smooth compactly supported functions

The subcritical Gagliardo–Nirenberg–Sobolev inequality of order `k` on `C_c^k(ℝ^n)`: if `1 ≤ p`
and `kp < n`, then

`‖u‖_{L^{np/(n-kp)}} ≤ C(n,k,p) · ∑_{|α| = k} ‖D^α u‖_{L^p}`.

This is the inequality behind Evans, PDE, §5.6.3, Theorem 6(i), for compactly supported
functions on `ℝ^n`. As in step 1 of Evans's proof, we iterate the
first-order inequality `‖v‖_{L^{q^*}} ≤ C(q) ∑_i ‖∂_i v‖_{L^q}`, with `q^* = nq/(n-q)`, along the
chain of exponents `p_0 = p`, `p_{j+1} = p_j^*`, applying it at each stage to every coordinate
derivative of the previous stage. The exponent bookkeeping is in `HigherOrder.Exponent`; the
completed-space versions are in `HigherOrder.Global`.

## Main results

* `higherDerivativeSum`: the sum of the `L^p` seminorms of all ordered coordinate derivative
  words of length `k`, defined by recursion on `k`.
* `higherOrderConstant`: the constant produced by the iteration, the product of Mathlib's
  first-order constants `SNormLESNormFDerivOfEqConst` at the intermediate exponents.
* `eLpNorm_le_higherDerivativeSum`: the inequality itself.

## Implementation notes

The derivative sum runs over ordered words `(i_1, …, i_k)` rather than over multi-indices, so a
mixed derivative is counted once for each ordering of its indices. That multiplicity is a finite
constant depending only on `n` and `k`, and keeping it makes the induction a direct recursion on
`k`. The constant `higherOrderConstant` is therefore not sharp.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.1, Theorem 1, (10), p. 277, for the first-order
  inequality, and §5.6.3, Theorem 6(i), pp. 284-285, and step 1 of its proof, p. 285.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

namespace SobolevSpace
namespace Inequalities

open MeasureTheory Set
open scoped ENNReal Topology

section SmoothCompactSupport

variable {n k : ℕ} {p : NNReal}

/-- Recursive sum of the `L^p` seminorms of all ordered coordinate
derivatives of order `k`.

The ordered-word sum may count the same mixed derivative more than once.
That finite multiplicity keeps the induction transparent; it is
equivalent, up to a dimension-and-order constant, to the sum over
multi-indices of length `k`. -/
noncomputable def higherDerivativeSum
    (n : ℕ) : ℕ → NNReal → (ℝ^n → ℝ) → ℝ≥0∞
  | 0, p, u => eLpNorm u (p : ℝ≥0∞) (volume : Measure (ℝ^n))
  | k + 1, p, u =>
      ∑ i : Fin n,
        higherDerivativeSum n k p
          (fun x ↦ (∂[i] u) x)

/-- Explicit constant produced by iterating the verified first-order
Gagliardo-Nirenberg-Sobolev inequality. -/
noncomputable def higherOrderConstant
    (n : ℕ) : ℕ → NNReal → ℝ≥0∞
  | 0, _ => 1
  | k + 1, p =>
      (MeasureTheory.SNormLESNormFDerivOfEqConst ℝ
        (volume : Measure (ℝ^n))
        ((higherOrderExponent n k p : NNReal) : ℝ) : ℝ≥0∞) *
        higherOrderConstant n k p

/-- At order zero the derivative sum is the `L^p` seminorm of `u` itself. -/
@[simp]
theorem higherDerivativeSum_zero
    (u : ℝ^n → ℝ) :
    higherDerivativeSum n 0 p u =
      eLpNorm u (p : ℝ≥0∞) (volume : Measure (ℝ^n)) :=
  rfl

/-- The order-`(k+1)` derivative sum is the sum over coordinates `i` of the order-`k` sums of
`∂_i u`. This is the defining recursion, exposed for `simp`. -/
@[simp]
theorem higherDerivativeSum_succ
    (u : ℝ^n → ℝ) :
    higherDerivativeSum n (k + 1) p u =
      ∑ i : Fin n,
        higherDerivativeSum n k p
          (fun x ↦ (∂[i] u) x) :=
  rfl

/-- General Gagliardo-Nirenberg-Sobolev inequality on the smooth
compactly supported core, Evans §5.6.3, Theorem 6(i).

For `u ∈ C_c^k(ℝ^n)`, `1 ≤ p`, and `kp < n`,

`‖u‖_{L^{np/(n-kp)}} ≤ C(n,k,p) ∑_{|α|=k} ‖D^αu‖_{L^p}`.

Here the displayed sum is implemented as `higherDerivativeSum`, the finite
sum over ordered coordinate words. -/
theorem eLpNorm_le_higherDerivativeSum
    {u : ℝ^n → ℝ}
    (hu : ContDiff ℝ k u) (hcompact : HasCompactSupport u)
    (hp : (1 : NNReal) ≤ p) (hn : 0 < n)
    (hsub : (k : ℝ) * p < n) :
    eLpNorm u (higherOrderExponent n k p : ℝ≥0∞)
        (volume : Measure (ℝ^n)) ≤
      higherOrderConstant n k p * higherDerivativeSum n k p u := by
  induction k generalizing u with
  | zero =>
      rw [higherOrderExponent_zero hn]
      simp [higherOrderConstant, higherDerivativeSum]
  | succ k ih =>
      have hp0 : 0 < (p : ℝ) := by exact_mod_cast zero_lt_one.trans_le hp
      have hsub' : ((k : ℝ) + 1) * p < n := by simpa [Nat.cast_add, Nat.cast_one] using hsub
      have hksub : (k : ℝ) * p < n := by linarith
      set q : NNReal := higherOrderExponent n k p
      have hq_one : (1 : NNReal) ≤ q := one_le_higherOrderExponent hp hksub
      -- the first-order inequality at the exponent `q`, then the induction hypothesis on each
      -- coordinate derivative
      have hsob := Inequalities.eLpNorm_le_sum_eLpNorm_partialDeriv_of_eq (n := n)
        (hu.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))) hcompact hq_one hn
        (Inequalities.inv_pStar_eq hn (by exact_mod_cast zero_lt_one.trans_le hq_one)
          (higherOrderExponent_lt_dimension hsub'))
      rw [← pStar_higherOrderExponent hp0 hsub']
      calc
        _ ≤ (MeasureTheory.SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) (q : ℝ) : ℝ≥0∞) *
              ∑ i : Fin n, eLpNorm (fun x ↦ (∂[i] u) x) (q : ℝ≥0∞) (volume : Measure (ℝ^n)) := by
          simpa [q] using hsob
        _ ≤ (MeasureTheory.SNormLESNormFDerivOfEqConst ℝ (volume : Measure (ℝ^n)) (q : ℝ) : ℝ≥0∞) *
              (higherOrderConstant n k p * higherDerivativeSum n (k + 1) p u) := by
          gcongr
          rw [higherDerivativeSum_succ, Finset.mul_sum]
          exact Finset.sum_le_sum fun i _ ↦ ih (PDE.contDiff_partialDeriv_of_succ (n := n) hu)
            (hcompact.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))) hksub
        _ = _ := by simp [higherOrderConstant, q, mul_assoc]

end SmoothCompactSupport

end Inequalities
end SobolevSpace
