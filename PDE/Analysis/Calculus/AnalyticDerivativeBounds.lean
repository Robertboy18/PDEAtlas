/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Order
import PDE.Analysis.Calculus.TaylorSeries

/-!
# Cauchy estimates for analytic functions

## Motivation

How fast can the derivatives of an analytic function grow near a point?

## The idea

Let `f` have the power series `p` at `x`, with `‖p n‖ ≤ C * a ^ n`. A power
series can be expanded again around a nearby point `x + y`. Mathlib calls the new series
`p.changeOrigin y`. Its `k`-th coefficient is a sum over `l` of `(k + l).choose l` rearranged
copies of `p (k + l)`, each applied to `l` copies of `y`. So its norm is at most the binomial
series `∑ l, (k + l).choose l * C * a ^ (k + l) * ‖y‖ ^ l`, which equals
`C * a ^ k / (1 - a * ‖y‖) ^ (k + 1)`. The `k`-th derivative of `f` at `x + y` is a sum of `k!`
permuted copies of that coefficient. For `a * ‖y‖ ≤ 1 / 2` this gives
`‖Dᵏf(x + y)‖ ≤ k! * (2 * C) * (2 * a) ^ k`, and the constants do not depend on `y` or `k`.
The argument uses no complex analysis, so the scalar field can be any nontrivially normed
field. For real functions the Taylor formula with integral remainder gives the converse, so
the factorial rate characterizes real analyticity.

## Main results

* `FormalMultilinearSeries.norm_changeOrigin_le_of_le_mul_pow` (all formal multilinear series
  with `‖p n‖ ≤ C * a ^ n`): `‖p.changeOrigin y k‖ ≤ C * a ^ k / (1 - a * ‖y‖) ^ (k + 1)` when
  `a * ‖y‖ < 1`.
* `HasFPowerSeriesWithinOnBall.norm_iteratedFDerivWithin_le_of_le_mul_pow` (all functions with
  a power series `p` within a set of unique differentiability, `‖p n‖ ≤ C * a ^ n`, Banach
  codomain): `‖Dᵏf(x + y)‖ ≤ k! * C * a ^ k / (1 - a * ‖y‖) ^ (k + 1)` for all `y` in the ball of
  the expansion with `x + y` in the set and `a * ‖y‖ < 1`. The version on the whole space is
  `HasFPowerSeriesOnBall.norm_iteratedFDeriv_le_of_le_mul_pow`.
* `AnalyticAt.exists_norm_iteratedFDeriv_le` (all analytic functions into a Banach space, over
  any nontrivially normed field): there are `r > 0`, `C` and `K` with
  `‖Dᵏf(y)‖ ≤ k! * C * K ^ k` for all `k` and all `y` in the ball of radius `r`. The version
  within a set is `AnalyticWithinAt.exists_norm_iteratedFDerivWithin_le`.
* `AnalyticAt.exists_norm_iteratedFDeriv_le_family` (all finite families of analytic
  functions): the same bound with one `r`, `C` and `K` for the whole family.
* `PDE.Analysis.analyticAt_iff_exists_norm_iteratedFDeriv_le` (all functions from a real normed
  space to a real Banach space): `f` is analytic at `x` exactly when it is smooth on a ball
  around `x` and satisfies such a bound there.

## Relations

* The bounds rest on Mathlib's change of origin, `HasFPowerSeriesWithinOnBall.changeOrigin`, on
  the formula `HasFPowerSeriesWithinOnBall.iteratedFDerivWithin_eq_sum_of_completeSpace` for
  the derivatives at the center, and on the binomial series
  `hasSum_choose_mul_geometric_of_norm_lt_one`. The coefficient bound of an analytic function
  comes from `FormalMultilinearSeries.le_mul_pow_of_radius_pos`.
* `FormalMultilinearSeries.norm_changeOriginSeries_le` restates Mathlib's
  `FormalMultilinearSeries.nnNorm_changeOriginSeries_le_tsum` with the number of subsets
  written as a binomial coefficient.
* `AnalyticAt.exists_norm_iteratedFDeriv_le` is the converse of
  `ContDiffOn.hasFPowerSeriesOnBall_of_iteratedFDeriv_bound`. The two together are
  `PDE.Analysis.analyticAt_iff_exists_norm_iteratedFDeriv_le`.
* For harmonic functions `LaplacianEquation.IsHarmonicPDE.norm_iteratedFDeriv_le_factorial`
  proves a bound of the same shape with the explicit constants `C = M` and `K = e * n / R`,
  and `LaplacianEquation.IsHarmonicPDE.analyticOnNhd` deduces analyticity from it. Here the
  constants come from the power series, and the bound holds for every analytic function.
* Mathlib's `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` is Cauchy's estimate
  for a function of one complex variable. It bounds the derivatives at the center of a disc
  by the maximum of `f` on the circle. The estimates here need no complex structure. They
  bound the derivatives by the coefficients of the power series, at the center and near it.

## What stays open

* A bound on a whole compact subset of an open set of analyticity. It follows from the local
  statement by a finite subcover and is not stated here.
* Constants in terms of a bound for `f` alone. On a real ball a bound for `f` does not control
  its derivatives (take `sin (n * t)`), so the constants here come from the coefficients of
  the power series.
* The characterization over other fields. The converse direction here uses the real Taylor
  formula with integral remainder. For functions of one complex variable no bound is needed:
  differentiability on an open set already gives analyticity (Mathlib's
  `DifferentiableOn.analyticAt`).
* Codomains that are not complete. Mathlib's change of origin needs completeness.

## References

* See also S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, 2nd ed.,
  Birkhäuser, 2002, <https://doi.org/10.1007/978-0-8176-8134-0>, for the characterization of
  real-analytic functions by derivative bounds in finite dimension. This module was written
  from Mathlib's change of origin for power series, not from that text.
-/

@[expose] public section

open Metric Set
open scoped ContDiff ENNReal NNReal

section Bounds

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FormalMultilinearSeries

/-- The coefficient `p.changeOriginSeries k l` is a sum of `(k + l).choose l` rearranged copies
of `p (k + l)`, one for each subset of size `l` of the `k + l` arguments. So its norm is at
most `(k + l).choose l * ‖p (k + l)‖`. -/
theorem norm_changeOriginSeries_le (p : FormalMultilinearSeries 𝕜 E F) (k l : ℕ) :
    ‖p.changeOriginSeries k l‖ ≤ ((k + l).choose l : ℝ) * ‖p (k + l)‖ := by
  have h : ‖p.changeOriginSeries k l‖₊ ≤ ((k + l).choose l : ℝ≥0) * ‖p (k + l)‖₊ := by
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_finset_len,
      Fintype.card_fin, nsmul_eq_mul] using p.nnNorm_changeOriginSeries_le_tsum k l
  exact_mod_cast NNReal.coe_le_coe.2 h

/-- A series with geometric coefficient bounds keeps them after a change of origin: if
`‖p n‖ ≤ C * a ^ n` for all `n` and `a * ‖y‖ < 1`, then
`‖p.changeOrigin y k‖ ≤ C * a ^ k / (1 - a * ‖y‖) ^ (k + 1)` for all `k`.

This is the estimate behind the Cauchy estimates away from the center. The `l`-th term of the
series that defines `p.changeOrigin y k` is at most `(k + l).choose l * C * a ^ (k + l) * ‖y‖ ^ l`
by `norm_changeOriginSeries_le`, and the binomial series sums these bounds. -/
theorem norm_changeOrigin_le_of_le_mul_pow (p : FormalMultilinearSeries 𝕜 E F) {C a : ℝ}
    (ha : 0 ≤ a) (hp : ∀ n, ‖p n‖ ≤ C * a ^ n) {y : E} (hy : a * ‖y‖ < 1) (k : ℕ) :
    ‖p.changeOrigin y k‖ ≤ C * a ^ k / (1 - a * ‖y‖) ^ (k + 1) := by
  have hsum : HasSum (fun l : ℕ ↦ C * a ^ k * (((l + k).choose k : ℝ) * (a * ‖y‖) ^ l))
      (C * a ^ k / (1 - a * ‖y‖) ^ (k + 1)) := by
    have hnorm : ‖a * ‖y‖‖ < 1 := by rwa [Real.norm_of_nonneg (by positivity)]
    simpa only [mul_one_div] using
      (hasSum_choose_mul_geometric_of_norm_lt_one k hnorm).mul_left (C * a ^ k)
  refine tsum_of_norm_bounded hsum fun l ↦ ?_
  calc ‖p.changeOriginSeries k l fun _ ↦ y‖
      ≤ ‖p.changeOriginSeries k l‖ * ‖y‖ ^ l := by
        simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
          (p.changeOriginSeries k l).le_opNorm fun _ ↦ y
    _ ≤ ((k + l).choose l : ℝ) * (C * a ^ (k + l)) * ‖y‖ ^ l := by
        gcongr
        exact (p.norm_changeOriginSeries_le k l).trans (by gcongr; exact hp _)
    _ = C * a ^ k * (((l + k).choose k : ℝ) * (a * ‖y‖) ^ l) := by
        rw [add_comm l k, Nat.choose_symm_add]
        ring

end FormalMultilinearSeries

variable [CompleteSpace F] {f : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E}
  {r : ℝ≥0∞}

/-- Cauchy estimate at the center, within a set: if `f` has the power series `p` at `x` within
a set `s` of unique differentiability that contains `x`, then
`‖iteratedFDerivWithin 𝕜 n f s x‖ ≤ n! * ‖p n‖`.

This turns a bound on the coefficients of a power series into a bound on the derivatives.
Mathlib writes the `n`-th derivative at the center as the sum of `p n` over the `n!`
permutations of its arguments. Each term has the norm of `p n`. -/
theorem HasFPowerSeriesWithinOnBall.norm_iteratedFDerivWithin_le
    (h : HasFPowerSeriesWithinOnBall f p s x r) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (n : ℕ) :
    ‖iteratedFDerivWithin 𝕜 n f s x‖ ≤ (n.factorial : ℝ) * ‖p n‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [h.iteratedFDerivWithin_eq_sum_of_completeSpace hs hx v]
  calc ‖∑ σ : Equiv.Perm (Fin n), p n fun i ↦ v (σ i)‖
      ≤ ∑ _σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v i‖ :=
        norm_sum_le_of_le _ fun σ _ ↦ ((p n).le_opNorm _).trans_eq <| by
          rw [Equiv.prod_comp σ fun i ↦ ‖v i‖]
    _ = (n.factorial : ℝ) * ‖p n‖ * ∏ i, ‖v i‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul, mul_assoc]

/-- Cauchy estimate at the center: if `f` has the power series `p` at `x` and the codomain is
complete, then `‖iteratedFDeriv 𝕜 n f x‖ ≤ n! * ‖p n‖`. This is the case `s = univ` of
`HasFPowerSeriesWithinOnBall.norm_iteratedFDerivWithin_le`. -/
theorem HasFPowerSeriesOnBall.norm_iteratedFDeriv_le (h : HasFPowerSeriesOnBall f p x r)
    (n : ℕ) : ‖iteratedFDeriv 𝕜 n f x‖ ≤ (n.factorial : ℝ) * ‖p n‖ := by
  simpa only [iteratedFDerivWithin_univ] using
    (hasFPowerSeriesWithinOnBall_univ.2 h).norm_iteratedFDerivWithin_le uniqueDiffOn_univ
      (mem_univ x) n

/-- Cauchy estimate away from the center, within a set: let `f` have the power series `p` at
`x` on the ball of radius `r` within a set `s` of unique differentiability, with
`‖p n‖ ≤ C * a ^ n` for all `n`. Then for every `y` with `‖y‖ < r`, `x + y ∈ s` and
`a * ‖y‖ < 1`,
`‖iteratedFDerivWithin 𝕜 k f s (x + y)‖ ≤ k! * C * a ^ k / (1 - a * ‖y‖) ^ (k + 1)`.

The bound is explicit in the coefficient bound of the series, and it is uniform for `a * ‖y‖`
bounded away from `1`. The proof moves the origin of the series to `x + y`, applies the
estimate at the center, and bounds the new coefficients with
`FormalMultilinearSeries.norm_changeOrigin_le_of_le_mul_pow`. -/
theorem HasFPowerSeriesWithinOnBall.norm_iteratedFDerivWithin_le_of_le_mul_pow
    (h : HasFPowerSeriesWithinOnBall f p s x r) (hs : UniqueDiffOn 𝕜 s) {C a : ℝ} (ha : 0 ≤ a)
    (hp : ∀ n, ‖p n‖ ≤ C * a ^ n) {y : E} (hy : ‖y‖ₑ < r) (hxy : x + y ∈ s)
    (hay : a * ‖y‖ < 1) (k : ℕ) :
    ‖iteratedFDerivWithin 𝕜 k f s (x + y)‖ ≤
      (k.factorial : ℝ) * C * a ^ k / (1 - a * ‖y‖) ^ (k + 1) := by
  refine ((h.changeOrigin hy (mem_insert_of_mem x hxy)).norm_iteratedFDerivWithin_le hs hxy
    k).trans ?_
  rw [mul_assoc, mul_div_assoc]
  gcongr
  exact p.norm_changeOrigin_le_of_le_mul_pow ha hp hay k

/-- Cauchy estimate away from the center: let `f` have the power series `p` at `x` on the ball
of radius `r`, with `‖p n‖ ≤ C * a ^ n` for all `n` and a complete codomain. Then for every
`y` with `‖y‖ < r` and `a * ‖y‖ < 1`,
`‖iteratedFDeriv 𝕜 k f (x + y)‖ ≤ k! * C * a ^ k / (1 - a * ‖y‖) ^ (k + 1)`. This is the case
`s = univ` of `HasFPowerSeriesWithinOnBall.norm_iteratedFDerivWithin_le_of_le_mul_pow`. -/
theorem HasFPowerSeriesOnBall.norm_iteratedFDeriv_le_of_le_mul_pow
    (h : HasFPowerSeriesOnBall f p x r) {C a : ℝ} (ha : 0 ≤ a) (hp : ∀ n, ‖p n‖ ≤ C * a ^ n)
    {y : E} (hy : ‖y‖ₑ < r) (hay : a * ‖y‖ < 1) (k : ℕ) :
    ‖iteratedFDeriv 𝕜 k f (x + y)‖ ≤
      (k.factorial : ℝ) * C * a ^ k / (1 - a * ‖y‖) ^ (k + 1) := by
  simpa only [iteratedFDerivWithin_univ] using
    (hasFPowerSeriesWithinOnBall_univ.2 h).norm_iteratedFDerivWithin_le_of_le_mul_pow
      uniqueDiffOn_univ ha hp hy (mem_univ _) hay k

/-- Cauchy estimates for a function that is analytic within a set: if `f` is analytic at `x`
within a set `s` of unique differentiability and the codomain is complete, then there are
`r > 0`, `C ≥ 0` and `K > 0` such that
`‖iteratedFDerivWithin 𝕜 k f s y‖ ≤ k! * C * K ^ k` for all `k` and all `y ∈ s` with
`dist y x < r`. The constants do not depend on `k` or `y`.

If the series `p` of `f` at `x` satisfies `‖p n‖ ≤ C₀ * a ^ n`, the proof takes `C = 2 * C₀`,
`K = 2 * a`, and `r` so small that `a * r ≤ 1 / 2`, and applies
`HasFPowerSeriesWithinOnBall.norm_iteratedFDerivWithin_le_of_le_mul_pow`. -/
theorem AnalyticWithinAt.exists_norm_iteratedFDerivWithin_le (hf : AnalyticWithinAt 𝕜 f s x)
    (hs : UniqueDiffOn 𝕜 s) :
    ∃ r > (0 : ℝ), ∃ C K : ℝ, 0 ≤ C ∧ 0 < K ∧ ∀ k : ℕ, ∀ y ∈ s ∩ ball x r,
      ‖iteratedFDerivWithin 𝕜 k f s y‖ ≤ (k.factorial : ℝ) * C * K ^ k := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨C, a, hC, ha, hpa⟩ := p.le_mul_pow_of_radius_pos (hp.r_pos.trans_le hp.r_le)
  obtain ⟨ρ, hρ, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  refine ⟨min ρ (2 * a)⁻¹, lt_min (by exact_mod_cast hρ) (by positivity), 2 * C, 2 * a,
    by positivity, by positivity, fun k y ⟨hys, hy⟩ ↦ ?_⟩
  rw [mem_ball, dist_eq_norm, lt_min_iff] at hy
  have hay : a * ‖y - x‖ ≤ 1 / 2 :=
    calc a * ‖y - x‖ ≤ a * (2 * a)⁻¹ := mul_le_mul_of_nonneg_left hy.2.le ha.le
      _ = 1 / 2 := by field_simp
  have hyr : ‖y - x‖ₑ < r := (eNorm_lt_coe.2 (show ‖y - x‖₊ < ρ from hy.1)).trans hρr
  have hmain := hp.norm_iteratedFDerivWithin_le_of_le_mul_pow hs ha.le hpa hyr
    (by rwa [add_sub_cancel]) (by linarith) k
  rw [add_sub_cancel] at hmain
  calc ‖iteratedFDerivWithin 𝕜 k f s y‖
      ≤ (k.factorial : ℝ) * C * a ^ k / (1 - a * ‖y - x‖) ^ (k + 1) := hmain
    _ ≤ (k.factorial : ℝ) * C * a ^ k / (1 / 2) ^ (k + 1) := by
        gcongr
        linarith
    _ = (k.factorial : ℝ) * (2 * C) * (2 * a) ^ k := by
        rw [mul_pow, one_div, inv_pow, div_inv_eq_mul, pow_succ]
        ring

/-- Cauchy estimates for a finite family of functions that are analytic within a set: if every
`f i` is analytic at `x` within a set `s` of unique differentiability, then one radius `r > 0`
and one pair of constants `C ≥ 0`, `K > 0` give
`‖iteratedFDerivWithin 𝕜 k (f i) s y‖ ≤ k! * C * K ^ k` for all `i`, all `k` and all `y ∈ s`
with `dist y x < r`. The empty family is included.

The proof takes the smallest radius and the sums of the constants of
`AnalyticWithinAt.exists_norm_iteratedFDerivWithin_le`. -/
theorem AnalyticWithinAt.exists_norm_iteratedFDerivWithin_le_family {ι : Type*} [Finite ι]
    {f : ι → E → F} (hf : ∀ i, AnalyticWithinAt 𝕜 (f i) s x) (hs : UniqueDiffOn 𝕜 s) :
    ∃ r > (0 : ℝ), ∃ C K : ℝ, 0 ≤ C ∧ 0 < K ∧ ∀ i, ∀ k : ℕ, ∀ y ∈ s ∩ ball x r,
      ‖iteratedFDerivWithin 𝕜 k (f i) s y‖ ≤ (k.factorial : ℝ) * C * K ^ k := by
  cases nonempty_fintype ι
  choose r hr C K hC hK hbound using fun i ↦ (hf i).exists_norm_iteratedFDerivWithin_le hs
  obtain ⟨ρ, hρ⟩ := Finite.exists_ge fun i ↦ (⟨r i, hr i⟩ : Ioi (0 : ℝ))
  have hC0 : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ ↦ hC j
  refine ⟨ρ, ρ.2, ∑ j, C j, 1 + ∑ j, K j, hC0,
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ ↦ (hK j).le),
    fun i k y hy ↦ (hbound i k y ⟨hy.1, ball_subset_ball (Subtype.coe_le_coe.2 (hρ i)) hy.2⟩).trans
      ?_⟩
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_univ i))
      (Nat.cast_nonneg _))
    (pow_le_pow_left₀ (hK i).le ((Finset.single_le_sum (fun j _ ↦ (hK j).le)
      (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)) k)
    (pow_nonneg (hK i).le k) (mul_nonneg (Nat.cast_nonneg _) hC0)

/-- Cauchy estimates for an analytic function: if `f` is analytic at `x` and the codomain is
complete, then there are `r > 0`, `C ≥ 0` and `K > 0` such that
`‖iteratedFDeriv 𝕜 k f y‖ ≤ k! * C * K ^ k` for all `k` and all `y` in the ball of radius `r`
around `x`. The constants do not depend on `k` or `y`. The scalar field is any nontrivially
normed field.

This is the converse of `ContDiffOn.hasFPowerSeriesOnBall_of_iteratedFDeriv_bound`. It is the
case `s = univ` of `AnalyticWithinAt.exists_norm_iteratedFDerivWithin_le`, which moves the
origin of the power series to `y` and sums a binomial series. -/
theorem AnalyticAt.exists_norm_iteratedFDeriv_le (hf : AnalyticAt 𝕜 f x) :
    ∃ r > (0 : ℝ), ∃ C K : ℝ, 0 ≤ C ∧ 0 < K ∧ ∀ k : ℕ, ∀ y ∈ ball x r,
      ‖iteratedFDeriv 𝕜 k f y‖ ≤ (k.factorial : ℝ) * C * K ^ k := by
  simpa only [iteratedFDerivWithin_univ, univ_inter] using
    hf.analyticWithinAt.exists_norm_iteratedFDerivWithin_le uniqueDiffOn_univ

/-- Cauchy estimates for a finite family of analytic functions: if every `f i` is analytic at
`x` and the codomain is complete, then one radius `r > 0` and one pair of constants `C ≥ 0`,
`K > 0` give `‖iteratedFDeriv 𝕜 k (f i) y‖ ≤ k! * C * K ^ k` for all `i`, all `k` and all `y`
in the ball of radius `r` around `x`. The empty family is included.

This is the form in which the bound is used for the coefficients of an equation, where one
needs the same constants for all of them. It is the case `s = univ` of
`AnalyticWithinAt.exists_norm_iteratedFDerivWithin_le_family`. -/
theorem AnalyticAt.exists_norm_iteratedFDeriv_le_family {ι : Type*} [Finite ι] {f : ι → E → F}
    (hf : ∀ i, AnalyticAt 𝕜 (f i) x) :
    ∃ r > (0 : ℝ), ∃ C K : ℝ, 0 ≤ C ∧ 0 < K ∧ ∀ i, ∀ k : ℕ, ∀ y ∈ ball x r,
      ‖iteratedFDeriv 𝕜 k (f i) y‖ ≤ (k.factorial : ℝ) * C * K ^ k := by
  simpa only [iteratedFDerivWithin_univ, univ_inter] using
    AnalyticWithinAt.exists_norm_iteratedFDerivWithin_le_family
      (fun i ↦ (hf i).analyticWithinAt) uniqueDiffOn_univ

end Bounds

namespace PDE.Analysis

/-- Real analyticity is the factorial growth of the derivatives: a function `f` from a real
normed space to a real Banach space is analytic at `x` if and only if there are `r > 0`,
`C ≥ 0` and `K > 0` such that `f` is smooth on the ball of radius `r` around `x` and
`‖iteratedFDeriv ℝ k f y‖ ≤ k! * C * K ^ k` for all `k` and all `y` in that ball.

So an analytic function can be handled through its derivative bounds, and derivative bounds
of this form are enough to prove analyticity. The forward direction is
`AnalyticAt.exists_norm_iteratedFDeriv_le`. The backward direction is
`ContDiffOn.hasFPowerSeriesOnBall_of_iteratedFDeriv_bound` on a ball of radius at most
`1 / K`. -/
theorem analyticAt_iff_exists_norm_iteratedFDeriv_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {f : E → F}
    {x : E} :
    AnalyticAt ℝ f x ↔ ∃ r > (0 : ℝ), ContDiffOn ℝ ∞ f (ball x r) ∧ ∃ C K : ℝ, 0 ≤ C ∧ 0 < K ∧
      ∀ k : ℕ, ∀ y ∈ ball x r, ‖iteratedFDeriv ℝ k f y‖ ≤ (k.factorial : ℝ) * C * K ^ k := by
  refine ⟨fun hf ↦ ?_, ?_⟩
  · obtain ⟨r₁, hr₁, hana⟩ := hf.exists_ball_analyticOnNhd
    obtain ⟨r₂, hr₂, C, K, hC, hK, hbound⟩ := hf.exists_norm_iteratedFDeriv_le
    exact ⟨min r₁ r₂, lt_min hr₁ hr₂,
      (hana.mono (ball_subset_ball (min_le_left _ _))).contDiffOn_of_completeSpace, C, K, hC, hK,
      fun k y hy ↦ hbound k y (ball_subset_ball (min_le_right _ _) hy)⟩
  · rintro ⟨r, hr, hsmooth, C, K, hC, hK, hbound⟩
    let ρ : ℝ≥0 := ⟨min r K⁻¹, (lt_min hr (inv_pos.2 hK)).le⟩
    have hρ : 0 < ρ := lt_min hr (inv_pos.2 hK)
    have hsub : ball x (ρ : ℝ) ⊆ ball x r := ball_subset_ball (min_le_left _ _)
    have hKρ : K * ρ ≤ 1 :=
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hK.le).trans_eq (mul_inv_cancel₀ hK.ne')
    exact ((hsmooth.mono hsub).hasFPowerSeriesOnBall_of_iteratedFDeriv_bound hρ hC hK hKρ
      fun k y hy ↦ hbound k y (hsub hy)).analyticAt

end PDE.Analysis
