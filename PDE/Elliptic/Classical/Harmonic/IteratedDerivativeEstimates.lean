/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.DerivativeEstimates
public import PDE.Elliptic.Classical.Harmonic.Derivatives
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Arbitrary-order interior derivative estimates for harmonic functions

If `u` is harmonic on an open set `U` containing the closed ball `B(x, k r)` and
`|u| ≤ M` on that ball, then

`‖D^k u(x)‖ ≤ n^k M / r^k`.

With `d = k r` this is the classical bound `(n k / d)^k · sup |u|` for the `k`-th derivatives of
a harmonic function at distance `d` from the boundary (Gilbarg and Trudinger, Chapter 2). The
proof iterates the first-order estimate `IsHarmonicPDE.norm_fderiv_le` of
`PDE.Elliptic.Classical.Harmonic.DerivativeEstimates`, spending radius `r` at each step: the
`(k+1)`-st derivative at `x` is controlled by the `k`-th derivative on the sphere of radius `r`,
which is in turn controlled by `u` on the remaining ball. Evans uses the same one-step bound in
step 2 of his proof of §2.2.3, Theorem 7, but combines it with `L¹` bounds instead of iterating
it.

The original harmonicity hypothesis supplies `C²` regularity. Interior smoothness and
harmonicity of all fixed derivative evaluations are derived in
`PDE.Elliptic.Classical.Harmonic.Derivatives`. The public estimates therefore require only
harmonicity of `u`, openness of `U`, and the stated ball and function bounds.

## Main results

* `IsHarmonicPDE.norm_iteratedFDeriv_radii_le`: the nonuniform version, with a separate radius
  `r i` for each step and total radius `∑ r i`, giving the bound `n^k M / ∏ r i`.
* `IsHarmonicPDE.norm_iteratedFDeriv_le`: the uniform-step version above.
* `IsHarmonicPDE.norm_iteratedFDeriv_succ_le`: the same for positive order `k + 1`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 7 (Estimates on derivatives) and step 2 of
  its proof, pp. 29-30.
  <https://doi.org/10.1090/gsm/019>
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, 2001, Chapter 2 (Laplace's Equation).
  <https://doi.org/10.1007/978-3-642-61798-0_2>
-/

@[expose] public section

namespace LaplacianEquation

open Set

-- Currying reduces multilinear-valued smoothness to `contDiffOn_clm_apply`.
private theorem contDiffOn_continuousMultilinearMap_of_apply
    {D E F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {m : WithTop ℕ∞} {k : ℕ} {f : D → E [×k]→L[ℝ] F} {s : Set D}
    (h : ∀ v, ContDiffOn ℝ m (fun x ↦ f x v) s) :
    ContDiffOn ℝ m f s := by
  induction k with
  | zero =>
      have hcurry :
          ContDiffOn ℝ m
            (fun x ↦ continuousMultilinearCurryFin0 ℝ E F (f x)) s := by
        simpa only [continuousMultilinearCurryFin0_apply] using h (0 : Fin 0 → E)
      simpa [Function.comp_def] using
        (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp_contDiffOn hcurry
  | succ k ih =>
      let e :=
        continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ E) F
      have hcurry : ContDiffOn ℝ m (fun x ↦ e (f x)) s := by
        apply contDiffOn_clm_apply.mpr
        intro q
        apply ih
        intro v
        simpa only [e, continuousMultilinearCurryLeftEquiv_apply] using
          h (Fin.cons q v)
      simpa [Function.comp_def] using
        e.symm.contDiff.comp_contDiffOn hcurry

/--
Interior estimate with a separate radius budget for every derivative.

Suppose every evaluation of `iteratedFDeriv ℝ j u` is harmonic on `U` for
`j < k`. If the closed ball whose radius is the sum of the positive budgets
`r i` lies in `U`, and `|u| ≤ M` there, then

`‖D^k u(x)‖ ≤ n^k M / ∏ i, r i`.

The head radius is spent in the final first-derivative estimate, while the
tail radii are used recursively to control the preceding derivative on the
intermediate sphere. This is the nonuniform form of the usual iterated
interior estimate.
-/
private theorem norm_iteratedFDeriv_radii_le_of_harmonic_derivatives
    {n k : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hharmonic : ∀ j < k, ∀ v : Fin j → ℝ^n,
      IsHarmonicPDE n (fun y ↦ iteratedFDeriv ℝ j u y v) U)
    (r : Fin k → ℝ)
    (hr : ∀ i, 0 < r i)
    {x : ℝ^n} {M : ℝ}
    (hball : Metric.closedBall x (∑ i, r i) ⊆ U)
    (hM : ∀ y ∈ Metric.closedBall x (∑ i, r i), |u y| ≤ M) :
    ‖iteratedFDeriv ℝ k u x‖ ≤
      (n : ℝ) ^ k * M / ∏ i, r i := by
  induction k generalizing x with
  | zero =>
      rw [norm_iteratedFDeriv_zero]
      simpa [Real.norm_eq_abs] using
        hM x (Metric.mem_closedBall_self (by positivity))
  | succ k ih =>
      have htailSum : 0 ≤ ∑ i : Fin k, r i.succ := Finset.sum_nonneg fun i _ ↦ (hr i.succ).le
      have hsum : ∑ i, r i = r 0 + ∑ i : Fin k, r i.succ := Fin.sum_univ_succ r
      have hM0 : 0 ≤ M := (abs_nonneg (u x)).trans
        (hM x (Metric.mem_closedBall_self (by linarith [(hr 0).le])))
      have hinner : Metric.closedBall x (r 0) ⊆ U :=
        (Metric.closedBall_subset_closedBall (by linarith)).trans hball
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ k u) x :=
        ((contDiffOn_continuousMultilinearMap_of_apply (m := 2) fun v ↦
          (hharmonic k k.lt_succ_self v).contDiffOn.mono
            (Metric.ball_subset_closedBall.trans hinner)).contDiffAt
          (Metric.ball_mem_nhds x (hr 0))).differentiableAt (by norm_num)
      have hderiv (y : ℝ^n) (hy : y ∈ Metric.sphere x (r 0)) :
          ‖iteratedFDeriv ℝ k u y‖ ≤ (n : ℝ) ^ k * M / ∏ i : Fin k, r i.succ := by
        have hsmall : Metric.closedBall y (∑ i : Fin k, r i.succ) ⊆
            Metric.closedBall x (∑ i, r i) :=
          Metric.closedBall_subset_closedBall' (by rw [Metric.mem_sphere.1 hy]; linarith)
        exact ih (fun j hj v ↦ hharmonic j (hj.trans k.lt_succ_self) v) (fun i ↦ r i.succ)
          (fun i ↦ hr i.succ) (hsmall.trans hball) fun z hz ↦ hM z (hsmall hz)
      have htailProd : 0 < ∏ i : Fin k, r i.succ := Finset.prod_pos fun i _ ↦ hr i.succ
      have hfullProd : 0 < ∏ i, r i := Finset.prod_pos fun i _ ↦ hr i
      have hdirectional (v : Fin k → ℝ^n) :
          ‖fderiv ℝ (fun y ↦ iteratedFDeriv ℝ k u y v) x‖ ≤
            (n : ℝ) * (((n : ℝ) ^ k * M / ∏ i : Fin k, r i.succ) * ∏ i, ‖v i‖) / r 0 :=
        (hharmonic k k.lt_succ_self v).norm_fderiv_le (hr 0) hinner (by positivity)
          fun y hy ↦ (Real.norm_eq_abs _).symm.trans_le
            (((iteratedFDeriv ℝ k u y).le_opNorm v).trans
              (mul_le_mul_of_nonneg_right (hderiv y hy) (by positivity)))
      refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
      rw [hdiff.iteratedFDeriv_succ_apply_left']
      calc _ ≤ ‖fderiv ℝ (fun y ↦ iteratedFDeriv ℝ k u y (Fin.tail m)) x‖ * ‖m 0‖ :=
            ContinuousLinearMap.le_opNorm _ (m 0)
        _ ≤ ((n : ℝ) * (((n : ℝ) ^ k * M / ∏ i : Fin k, r i.succ) *
              ∏ i, ‖Fin.tail m i‖) / r 0) * ‖m 0‖ :=
          mul_le_mul_of_nonneg_right (hdirectional (Fin.tail m)) (norm_nonneg (m 0))
        _ = ((n : ℝ) ^ (k + 1) * M / ∏ i, r i) * ∏ i, ‖m i‖ := by
          rw [Fin.prod_univ_succ, Fin.prod_univ_succ, pow_succ]
          simp only [Fin.tail]
          field_simp [(hr 0).ne', htailProd.ne']

/-- Interior estimate with a separate positive radius for each derivative.

If `u` is harmonic on an open set `U`, the closed ball of radius `∑ i, r i` lies in
`U`, and `|u| ≤ M` there, then `‖D^k u(x)‖ ≤ n^k M / ∏ i, r i`.
Smoothness and harmonicity of all derivative evaluations follow from harmonicity of `u`.
The order-zero case is the original pointwise bound. -/
theorem IsHarmonicPDE.norm_iteratedFDeriv_radii_le
    {n k : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U)
    (r : Fin k → ℝ) (hr : ∀ i, 0 < r i)
    {x : ℝ^n} {M : ℝ}
    (hball : Metric.closedBall x (∑ i, r i) ⊆ U)
    (hM : ∀ y ∈ Metric.closedBall x (∑ i, r i), |u y| ≤ M) :
    ‖iteratedFDeriv ℝ k u x‖ ≤ (n : ℝ) ^ k * M / ∏ i, r i :=
  norm_iteratedFDeriv_radii_le_of_harmonic_derivatives
    (fun j _ v ↦ hu.iteratedFDeriv_apply hU j v) r hr hball hM

/-- Uniform-step interior estimate for an arbitrary iterated Fréchet derivative.

Suppose `u` is harmonic on an open set `U`. If `Metric.closedBall x (k * r)` lies in
`U` and `|u| ≤ M` there, then

`‖D^k u(x)‖ ≤ n^k M / r^k`.

The radius `r` is spent once at each induction step. The order-zero case is the original
pointwise bound, so the theorem includes all derivative orders in one statement. -/
theorem IsHarmonicPDE.norm_iteratedFDeriv_le
    {n k : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U)
    {x : ℝ^n} {r M : ℝ}
    (hr : 0 < r)
    (hball : Metric.closedBall x ((k : ℝ) * r) ⊆ U)
    (hM : ∀ y ∈ Metric.closedBall x ((k : ℝ) * r), |u y| ≤ M) :
    ‖iteratedFDeriv ℝ k u x‖ ≤ (n : ℝ) ^ k * M / r ^ k := by
  simpa using
    IsHarmonicPDE.norm_iteratedFDeriv_radii_le
      (u := u) (U := U) hu hU (fun _ : Fin k ↦ r) (fun _ ↦ hr)
      (by simpa using hball) (by simpa using hM)

/-- Uniform-step estimate for a positive derivative order.

Harmonicity on an open set and a bound on the original function control the derivative
of order `k + 1`. The ball radius is `(k + 1) * r`, spending radius `r` at each step. -/
theorem IsHarmonicPDE.norm_iteratedFDeriv_succ_le
    {n k : ℕ} [Fact (0 < n)] {u : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hU : IsOpen U)
    {x : ℝ^n} {r M : ℝ}
    (hr : 0 < r)
    (hball : Metric.closedBall x (((k + 1 : ℕ) : ℝ) * r) ⊆ U)
    (hM : ∀ y ∈ Metric.closedBall x (((k + 1 : ℕ) : ℝ) * r), |u y| ≤ M) :
    ‖iteratedFDeriv ℝ (k + 1) u x‖ ≤
      (n : ℝ) ^ (k + 1) * M / r ^ (k + 1) :=
  hu.norm_iteratedFDeriv_le hU hr hball hM

end LaplacianEquation
