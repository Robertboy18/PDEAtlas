/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Spectral completeness and convergence

A Hilbert basis is orthonormal and complete. Its coefficient map takes values in `ℓ²`, and
Mathlib's `HilbertBasis.hasSum_repr` gives convergence of the expansion
`u = ∑ ⟪b i, u⟫ • b i` in the Hilbert-space norm. PDE estimates need the truncation error as
well, which we compute exactly and bound by weighted coefficient energies.

In separation of variables for the heat equation, Evans, §4.1.1, Example 1, expands the
initial datum in eigenfunctions, `g = ∑ d_k w_k` (9), writes the solution as the series (10),
and leaves the convergence of these series to Chapters 6 and 7. For a Hilbert basis of
eigenfunctions the expansion (9) converges by `HilbertBasis.hasSum_repr`, and the results here
bound its truncation error.

## Main results

* `hilbertBasis_parseval_norm_sq`: Parseval's identity `∑ ‖⟪b i, u⟫‖² = ‖u‖²`.
* `hilbertBasis_spectralResidual_norm_sq`: the squared error of the truncation to a finite
  set of modes is `‖u‖²` minus the retained coefficient energy.
* `hilbertBasis_spectralResidual_norm_sq_eq_tsum_tail`: for the first `N` modes, the squared
  error is the omitted coefficient tail.
* `hilbertBasis_spectralResidual_weightedEnergy_le`: the estimate from a nonnegative monotone
  spectral weight.
* `hilbertBasis_spectralResidual_norm_sq_le_polynomial`: the squared-error rate `(N + 1)⁻q`
  under finite `(n + 1)^q` coefficient energy.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.1.1, Example 1, (9) and (10), pp. 169-170.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Analysis.Spectral

open RCLike Real Filter ComplexConjugate
open scoped BigOperators InnerProductSpace Topology lp

noncomputable section

variable {ι 𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-!
## Exact truncation energy

Our first-`N` convention is `Finset.range N`, hence the retained indices are
`0, ..., N - 1`.  The omitted tail is consequently written as `k + N`.  Coefficients use
Mathlib's convention `⟪b i, u⟫`; for a complex Hilbert space this fixes which argument is
conjugate-linear and avoids silently changing the reconstruction formula.
-/

/-- Real-valued Parseval identity in the form used by energy estimates:
the sum of squared coefficient norms equals the squared Hilbert norm.

This is obtained from the fact that `HilbertBasis.repr` is a linear isometry into Mathlib's
`ℓ²`; it complements the complex-valued identity `HilbertBasis.tsum_inner_mul_inner` with the
real norm-square form used in energy estimates. -/
theorem hilbertBasis_parseval_norm_sq (b : HilbertBasis ι 𝕜 H) (u : H) :
    ∑' i, ‖⟪b i, u⟫_𝕜‖ ^ 2 = ‖u‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) (b.repr u)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using h.symm

/-- Exact Pythagorean energy identity for projection onto any finite set of Hilbert-basis modes.

The right side is nonnegative by Bessel's inequality; retaining the subtraction form makes the
statement directly useful for finite spectral/Galerkin energy balances. -/
theorem hilbertBasis_spectralResidual_norm_sq (b : HilbertBasis ι 𝕜 H) (u : H)
    (s : Finset ι) :
    ‖u - ∑ i ∈ s, ⟪b i, u⟫_𝕜 • b i‖ ^ 2 =
      ‖u‖ ^ 2 - ∑ i ∈ s, ‖⟪b i, u⟫_𝕜‖ ^ 2 := by
  have hInner :
      (∑ i ∈ s, ∑ j ∈ s,
          ⟪b i, u⟫_𝕜 * ⟪u, b j⟫_𝕜 * ⟪b j, b i⟫_𝕜) =
        (∑ k ∈ s, ⟪b k, u⟫_𝕜 * ⟪u, b k⟫_𝕜 : 𝕜) := by
    classical
    exact b.orthonormal.inner_left_right_finset
  have hNormProduct : ∀ z : 𝕜, re (z * conj z) = ‖z‖ ^ 2 := by
    intro z
    simp only [mul_conj]
    norm_cast
  rw [@norm_sub_sq 𝕜, sub_add]
  simp only [@InnerProductSpace.norm_sq_eq_re_inner 𝕜 H, inner_sum, sum_inner]
  simp only [inner_smul_right, two_mul, inner_smul_left, inner_conj_symm, ← mul_assoc, hInner,
    add_sub_cancel_right, sub_right_inj]
  simp only [map_sum, ← inner_conj_symm u, ← hNormProduct]

/-- For the first-`N` truncation, the squared Hilbert-space error is exactly the `ℓ²` energy in
the omitted coefficients.

Writing the tail as `k + N` avoids a subtype or indicator function and is convenient in estimates
for ordered eigenvalue sequences. -/
theorem hilbertBasis_spectralResidual_norm_sq_eq_tsum_tail
    (b : HilbertBasis ℕ 𝕜 H) (u : H) (N : ℕ) :
    ‖u - ∑ i ∈ Finset.range N, ⟪b i, u⟫_𝕜 • b i‖ ^ 2 =
      ∑' k, ‖⟪b (k + N), u⟫_𝕜‖ ^ 2 := by
  let energy : ℕ → ℝ := fun i ↦ ‖⟪b i, u⟫_𝕜‖ ^ 2
  have hEnergy : Summable energy := by
    simpa only [energy] using b.orthonormal.inner_products_summable u
  have hSplit :
      (∑ i ∈ Finset.range N, energy i) + ∑' k, energy (k + N) = ∑' i, energy i :=
    hEnergy.sum_add_tsum_nat_add N
  calc
    ‖u - ∑ i ∈ Finset.range N, ⟪b i, u⟫_𝕜 • b i‖ ^ 2 =
        ‖u‖ ^ 2 - ∑ i ∈ Finset.range N, energy i := by
      simpa only [energy] using
        hilbertBasis_spectralResidual_norm_sq b u (Finset.range N)
    _ = (∑' i, energy i) - ∑ i ∈ Finset.range N, energy i := by
      rw [hilbertBasis_parseval_norm_sq b u]
    _ = ∑' k, energy (k + N) := by linarith

/-!
## Quantitative weighted convergence

In applications `weight n` is typically an eigenvalue, a positive power of an eigenvalue, or a
Sobolev multiplier.  The assumptions below isolate exactly what the tail argument needs:
nonnegativity, monotonicity in the chosen mode ordering, and summability of the weighted
coefficient energy.  No growth law for the eigenvalues is baked into the abstract theorem.
-/

/-- Weighted spectral-tail estimate.  If `weight` is nonnegative and monotone, then

`weight N * ‖u - P_N u‖² ≤ ∑ n, weight n * |⟪b n, u⟫|²`.

Thus any lower growth estimate for the spectral weights immediately becomes a quantitative
truncation estimate.  The summability hypothesis is the abstract spectral regularity assumption
on `u`. -/
theorem hilbertBasis_spectralResidual_weightedEnergy_le
    (b : HilbertBasis ℕ 𝕜 H) (u : H) (weight : ℕ → ℝ) (N : ℕ)
    (hweight : ∀ n, 0 ≤ weight n) (hmono : Monotone weight)
    (hsum : Summable fun n ↦ weight n * ‖⟪b n, u⟫_𝕜‖ ^ 2) :
    weight N * ‖u - ∑ i ∈ Finset.range N, ⟪b i, u⟫_𝕜 • b i‖ ^ 2 ≤
      ∑' n, weight n * ‖⟪b n, u⟫_𝕜‖ ^ 2 := by
  let energy : ℕ → ℝ := fun n ↦ ‖⟪b n, u⟫_𝕜‖ ^ 2
  have hEnergy : Summable energy := by
    simpa only [energy] using b.orthonormal.inner_products_summable u
  have hEnergyTail : Summable fun k ↦ energy (k + N) :=
    (summable_nat_add_iff N).2 hEnergy
  have hWeightedTail : Summable fun k ↦ weight (k + N) * energy (k + N) :=
    (summable_nat_add_iff N).2 hsum
  have hCompare :
      (∑' k, weight N * energy (k + N)) ≤
        ∑' k, weight (k + N) * energy (k + N) := by
    exact Summable.tsum_le_tsum
      (fun k ↦ mul_le_mul_of_nonneg_right
        (hmono (by omega : N ≤ k + N)) (sq_nonneg ‖⟪b (k + N), u⟫_𝕜‖))
      (Summable.mul_left (weight N) hEnergyTail) hWeightedTail
  have hSplit :
      (∑ i ∈ Finset.range N, weight i * energy i) +
          ∑' k, weight (k + N) * energy (k + N) =
        ∑' n, weight n * energy n :=
    hsum.sum_add_tsum_nat_add N
  calc
    weight N * ‖u - ∑ i ∈ Finset.range N, ⟪b i, u⟫_𝕜 • b i‖ ^ 2 =
        weight N * ∑' k, energy (k + N) := by
      rw [hilbertBasis_spectralResidual_norm_sq_eq_tsum_tail b u N]
    _ = ∑' k, weight N * energy (k + N) := by
      rw [tsum_mul_left]
    _ ≤ ∑' k, weight (k + N) * energy (k + N) := hCompare
    _ ≤ ∑' n, weight n * energy n := by
      have hPrefix : 0 ≤ ∑ i ∈ Finset.range N, weight i * energy i := by
        exact Finset.sum_nonneg fun i _ ↦
          mul_nonneg (hweight i) (sq_nonneg ‖⟪b i, u⟫_𝕜‖)
      linarith

/-- Explicit polynomial truncation rate from weighted coefficient regularity.

If `∑ (n+1)^q |⟪b n,u⟫|²` is finite, then the first-`N` squared error is at most that weighted
energy divided by `(N+1)^q`.  Using `N+1` keeps the denominator strictly positive even at
`N = 0`; choosing `q = 2s` gives the familiar norm-error order `(N+1)⁻s`. -/
theorem hilbertBasis_spectralResidual_norm_sq_le_polynomial
    (b : HilbertBasis ℕ 𝕜 H) (u : H) (q N : ℕ)
    (hsum : Summable fun n ↦
      (((n + 1 : ℕ) : ℝ) ^ q) * ‖⟪b n, u⟫_𝕜‖ ^ 2) :
    ‖u - ∑ i ∈ Finset.range N, ⟪b i, u⟫_𝕜 • b i‖ ^ 2 ≤
      (∑' n, (((n + 1 : ℕ) : ℝ) ^ q) * ‖⟪b n, u⟫_𝕜‖ ^ 2) /
        (((N + 1 : ℕ) : ℝ) ^ q) := by
  have hWeighted := hilbertBasis_spectralResidual_weightedEnergy_le b u
    (fun n ↦ (((n + 1 : ℕ) : ℝ) ^ q)) N
    (fun n ↦ by positivity)
    (by
      intro m n hmn
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast Nat.add_le_add_right hmn 1)
    hsum
  apply (le_div_iff₀ (by positivity : 0 < (((N + 1 : ℕ) : ℝ) ^ q))).2
  simpa only [mul_comm] using hWeighted

end

end PDE.Analysis.Spectral
