/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.Global

/-!
# Higher-order Sobolev exponents

Exponent algebra for the general Sobolev inequalities, Evans §5.6.3, Theorem 6.

For `u ∈ W^{k,p}(ℝ^n)`, `1 ≤ p`, and `kp < n`, the target exponent is

`q = np / (n - kp)`, equivalently `1 / q = 1 / p - k / n`.

The estimates are in `HigherOrder.SmoothCompactSupport`, `HigherOrder.Global`,
and `HigherOrder.Domains`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.3, Theorem 6 and its proof, pp. 284-286.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace
namespace Inequalities

open MeasureTheory Set
open scoped ENNReal Topology

/-- The higher-order Sobolev exponent

`p_k = np / (n - kp)`.

As with `Inequalities.pStar`, this is totalized with `Real.toNNReal`; the
analytic theorems always assume the subcritical condition `kp < n`. -/
noncomputable def higherOrderExponent (n k : ℕ) (p : NNReal) : NNReal :=
  Real.toNNReal ((p : ℝ) * (n : ℝ) / ((n : ℝ) - (k : ℝ) * p))

/-- A subcritical relation `a p < n` with `a, p ≥ 0` forces positive dimension. -/
theorem pos_of_mul_lt_natCast {n : ℕ} {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p) (h : a * p < n) :
    0 < n := by
  exact_mod_cast lt_of_le_of_lt (mul_nonneg ha hp) h

/-- Closed form for the iterated Sobolev exponent:
`p_k = np / (n - kp)`.

The strict subcritical assumption ensures that every denominator occurring
in the iteration is positive. -/
theorem higherOrderExponent_coe
    {n k : ℕ} {p : NNReal}
    (hsub : (k : ℝ) * p < n) :
    ((higherOrderExponent n k p : NNReal) : ℝ) =
      (p : ℝ) * (n : ℝ) / ((n : ℝ) - (k : ℝ) * p) := by
  have hden : 0 < (n : ℝ) - (k : ℝ) * p := sub_pos.mpr hsub
  have hnonneg :
      0 ≤ (p : ℝ) * (n : ℝ) / ((n : ℝ) - (k : ℝ) * p) := by
    positivity
  simpa [higherOrderExponent] using
    Real.coe_toNNReal
      ((p : ℝ) * (n : ℝ) / ((n : ℝ) - (k : ℝ) * p)) hnonneg

/-- At order zero, the higher-order exponent is the original exponent. -/
theorem higherOrderExponent_zero
    {n : ℕ} {p : NNReal} (hn : 0 < n) :
    higherOrderExponent n 0 p = p := by
  apply NNReal.eq
  have hsub : (0 : ℝ) * p < n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    simpa using this
  rw [higherOrderExponent_coe (by simpa using hsub)]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp [hn0.ne']

/-- Reciprocal form of the higher-order exponent, as in Evans §5.6.3, Theorem 6(i): for `0 < p`
and `kp < n`,

`1 / p_k = 1 / p - k / n`.
-/
theorem inv_higherOrderExponent_eq
    {n k : ℕ} {p : NNReal} (hp : 0 < (p : ℝ))
    (hsub : (k : ℝ) * p < n) :
    (((higherOrderExponent n k p : NNReal) : ℝ)⁻¹) =
      (p : ℝ)⁻¹ - (k : ℝ) * (n : ℝ)⁻¹ := by
  rw [higherOrderExponent_coe hsub]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast pos_of_mul_lt_natCast (Nat.cast_nonneg k) p.2 hsub
  have hp_ne : (p : ℝ) ≠ 0 := ne_of_gt hp
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hden : (n : ℝ) - (k : ℝ) * p ≠ 0 :=
    ne_of_gt (sub_pos.mpr hsub)
  field_simp [hp_ne, hn_ne, hden]

/-- The reciprocal relation `1 / q = 1 / p - k / n` of Evans §5.6.3, Theorem 6(i), determines
the higher-order Sobolev exponent: for `0 < p` and `kp < n`, such a `q` equals
`higherOrderExponent n k p`. -/
theorem eq_higherOrderExponent_of_inv_eq
    {n k : ℕ} {p q : NNReal} (hp : 0 < (p : ℝ))
    (hsub : (k : ℝ) * p < n)
    (hq : (q : ℝ)⁻¹ =
      (p : ℝ)⁻¹ - (k : ℝ) * (n : ℝ)⁻¹) :
    q = higherOrderExponent n k p := by
  apply NNReal.eq
  apply inv_injective
  exact hq.trans (inv_higherOrderExponent_eq hp hsub).symm

/-- One higher-order exponent step is exactly the first-order Sobolev
conjugate of the preceding exponent. -/
theorem pStar_higherOrderExponent
    {n k : ℕ} {p : NNReal} (hp : 0 < (p : ℝ))
    (hsub : ((k : ℝ) + 1) * p < n) :
    Inequalities.pStar n (higherOrderExponent n k p) =
      higherOrderExponent n (k + 1) p := by
  have hn : 0 < n := pos_of_mul_lt_natCast (by positivity) p.2 hsub
  have hksub : (k : ℝ) * p < n := by
    have hp_nonneg : (0 : ℝ) ≤ p := le_of_lt hp
    nlinarith
  have hpk_lt :
      ((higherOrderExponent n k p : NNReal) : ℝ) < n := by
    rw [higherOrderExponent_coe hksub]
    have hden : 0 < (n : ℝ) - (k : ℝ) * p :=
      sub_pos.mpr hksub
    rw [div_lt_iff₀ hden]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    nlinarith [mul_pos hn0 hden]
  apply NNReal.eq
  have hsuccSub :
      ((k + 1 : ℕ) : ℝ) * p < n := by
    simpa [Nat.cast_add, Nat.cast_one] using hsub
  apply inv_injective
  calc
    (((Inequalities.pStar n (higherOrderExponent n k p) : NNReal) : ℝ)⁻¹)
        = (((higherOrderExponent n k p : NNReal) : ℝ)⁻¹) -
            (n : ℝ)⁻¹ :=
      Inequalities.inv_pStar_eq hn
        (by
          rw [higherOrderExponent_coe hksub]
          positivity)
        hpk_lt
    _ = ((p : ℝ)⁻¹ - (k : ℝ) * (n : ℝ)⁻¹) -
          (n : ℝ)⁻¹ := by
      rw [inv_higherOrderExponent_eq hp hksub]
    _ = (p : ℝ)⁻¹ - ((k + 1 : ℕ) : ℝ) * (n : ℝ)⁻¹ := by
      push_cast
      ring
    _ = (((higherOrderExponent n (k + 1) p : NNReal) : ℝ)⁻¹) :=
      (inv_higherOrderExponent_eq hp hsuccSub).symm

/-- Every intermediate higher-order exponent remains at least the original
exponent. -/
theorem le_higherOrderExponent
    {n k : ℕ} {p : NNReal}
    (hsub : (k : ℝ) * p < n) :
    p ≤ higherOrderExponent n k p := by
  apply NNReal.coe_le_coe.mp
  rw [higherOrderExponent_coe hsub]
  have hden : 0 < (n : ℝ) - (k : ℝ) * p :=
    sub_pos.mpr hsub
  rw [le_div_iff₀ hden]
  have hk_nonneg : (0 : ℝ) ≤ k := by positivity
  have hp_nonneg : (0 : ℝ) ≤ p := p.2
  nlinarith [mul_nonneg hk_nonneg (sq_nonneg (p : ℝ))]

/-- Under `1 ≤ p`, every iterated subcritical Sobolev exponent is at least
one. -/
theorem one_le_higherOrderExponent
    {n k : ℕ} {p : NNReal} (hp : (1 : NNReal) ≤ p)
    (hsub : (k : ℝ) * p < n) :
    (1 : NNReal) ≤ higherOrderExponent n k p :=
  hp.trans (le_higherOrderExponent hsub)

/-- The exponent reached after `k` steps is still subcritical for one more
first-order embedding precisely when `(k + 1)p < n`. -/
theorem higherOrderExponent_lt_dimension
    {n k : ℕ} {p : NNReal}
    (hsub : ((k : ℝ) + 1) * p < n) :
    ((higherOrderExponent n k p : NNReal) : ℝ) < n := by
  have hp_nonneg : (0 : ℝ) ≤ p := p.2
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (mul_nonneg (by positivity) hp_nonneg) hsub
  have hksub : (k : ℝ) * p < n := by nlinarith
  rw [higherOrderExponent_coe hksub]
  have hden : 0 < (n : ℝ) - (k : ℝ) * p :=
    sub_pos.mpr hksub
  rw [div_lt_iff₀ hden]
  nlinarith [mul_pos hn0 hden]

/-- Iterating `j` Sobolev exponent steps after `k` steps gives the
`(k + j)`-step exponent. -/
theorem higherOrderExponent_add
    {n j k : ℕ} {p : NNReal} (hp : 0 < (p : ℝ))
    (hsub : (((k + j : ℕ) : ℝ) * (p : ℝ)) < (n : ℝ)) :
    higherOrderExponent n j (higherOrderExponent n k p) =
      higherOrderExponent n (k + j) p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast pos_of_mul_lt_natCast (Nat.cast_nonneg _) p.2 hsub
  have hsub' : ((k : ℝ) + (j : ℝ)) * (p : ℝ) < (n : ℝ) := by
    simpa [Nat.cast_add] using hsub
  have hksub : (k : ℝ) * (p : ℝ) < (n : ℝ) := by
    have hj0 : (0 : ℝ) ≤ j := by positivity
    nlinarith [mul_nonneg hj0 (le_of_lt hp)]
  let q : NNReal := higherOrderExponent n k p
  have hqCoe :
      (q : ℝ) =
        (p : ℝ) * (n : ℝ) /
          ((n : ℝ) - (k : ℝ) * (p : ℝ)) := by
    dsimp [q]
    exact higherOrderExponent_coe hksub
  have hqPos : 0 < (q : ℝ) := by
    rw [hqCoe]
    positivity
  have hjqSub : (j : ℝ) * (q : ℝ) < (n : ℝ) := by
    rw [hqCoe]
    have hden : 0 < (n : ℝ) - (k : ℝ) * (p : ℝ) :=
      sub_pos.mpr hksub
    rw [show
      (j : ℝ) *
          ((p : ℝ) * (n : ℝ) /
            ((n : ℝ) - (k : ℝ) * (p : ℝ))) =
        ((j : ℝ) * ((p : ℝ) * (n : ℝ))) /
          ((n : ℝ) - (k : ℝ) * (p : ℝ)) by ring]
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos hn0 hden]
  change higherOrderExponent n j q =
    higherOrderExponent n (k + j) p
  apply eq_higherOrderExponent_of_inv_eq hp hsub
  rw [inv_higherOrderExponent_eq hqPos hjqSub]
  rw [inv_higherOrderExponent_eq hp hksub]
  push_cast
  ring

/-- At the critical relation `kp=n`, removing one derivative leaves the
dimension exponent:

`p_{k-1} = np / (n-(k-1)p) = n`.

This is the identity `r = pn / (n - pl) = n` for `l = n/p - 1` in step 3 of the proof of
Evans §5.6.3, Theorem 6, the case where `n/p` is an integer. -/
theorem higherOrderExponent_pred_eq_dimension
    {n k : ℕ} {p : NNReal}
    (hk : 0 < k) (hp : 0 < (p : ℝ))
    (hcrit : (k : ℝ) * p = n) :
    higherOrderExponent n (k - 1) p = (n : NNReal) := by
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hk))]
    norm_num
  have hsub : ((k - 1 : ℕ) : ℝ) * p < n := by
    rw [hkcast]
    nlinarith
  apply NNReal.eq
  rw [higherOrderExponent_coe hsub]
  rw [hkcast]
  have hden : (n : ℝ) - ((k : ℝ) - 1) * p = p := by
    nlinarith
  rw [hden]
  field_simp
  norm_num

end Inequalities
end SobolevSpace
