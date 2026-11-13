/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.MvPolynomial
public import PDE.FDeriv.Euclidean.Laplacian
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.FDeriv.Calculus
import PDE.FDeriv.Laplacian.Product

/-!
# Polynomials and radial factors on Euclidean space

A polynomial `P` in `n` variables defines the smooth function `x ↦ P(x)` on `ℝ^n`; its coordinate
derivatives and its Laplacian are the evaluations of the algebraic partial derivatives
`MvPolynomial.pderiv i P` and of the polynomial Laplacian `∑ᵢ pderiv i (pderiv i P)`. A
homogeneous polynomial of degree `m` satisfies `P(c x) = c^m P(x)`.

For a function `F` of one variable and any `C²` function `q`, the product `F(‖x‖²) q(x)` has

`∂ᵢ (F(‖x‖²) q) = 2 xᵢ F'(‖x‖²) q + F(‖x‖²) ∂ᵢ q` and
`Δ (F(‖x‖²) q) = (4 ‖x‖² F'' + 2n F') q + 4 F' ∑ⱼ xⱼ ∂ⱼ q + F Δq`,

with `F'` and `F''` taken at `‖x‖²`. For a homogeneous `q` of degree `m`, Euler's identity
`∑ⱼ xⱼ ∂ⱼ q = m q` turns the middle term into `4 m F' q`.
-/

@[expose] public section

open PDE (partialDeriv laplacian)
open MvPolynomial Filter
open scoped Topology ContDiff

namespace MvPolynomial

variable {n : ℕ}

/-- The Laplacian `∑ᵢ ∂ᵢ∂ᵢ` of a real polynomial in `n` variables. -/
noncomputable def polynomialLaplacian (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, pderiv i (pderiv i P)

/-- The Laplacian commutes with every partial derivative. -/
theorem polynomialLaplacian_pderiv (i : Fin n) (P : MvPolynomial (Fin n) ℝ) :
    polynomialLaplacian (pderiv i P) = pderiv i (polynomialLaplacian P) := by
  rw [polynomialLaplacian, polynomialLaplacian, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [pderiv_comm j i P, pderiv_comm j i (pderiv j P)]

/-- The Laplacian commutes with finite sums. -/
theorem polynomialLaplacian_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin n) ℝ) :
    polynomialLaplacian (∑ j ∈ s, f j) = ∑ j ∈ s, polynomialLaplacian (f j) := by
  simp only [polynomialLaplacian, map_sum]
  exact Finset.sum_comm

/-- The Laplacian commutes with multiplication by a constant. -/
theorem polynomialLaplacian_C_mul (a : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    polynomialLaplacian (C a * P) = C a * polynomialLaplacian P := by
  simp only [polynomialLaplacian, pderiv_C_mul, Finset.mul_sum]

/-- A homogeneous polynomial of degree `m` scales by `c ^ m`: `P(c x) = c ^ m P(x)`. -/
theorem IsHomogeneous.eval_smul {σ : Type*} {P : MvPolynomial σ ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) (c : ℝ) (x : σ → ℝ) :
    eval (c • x) P = c ^ m * eval x P := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdeg : ∑ i ∈ d.support, d i = m := by
    have h := hP (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end MvPolynomial

namespace EuclideanLaplacian

variable {n : ℕ}

/-- Polynomial evaluation on `ℝ^n` is smooth. -/
theorem contDiff_eval_ofLp (P : MvPolynomial (Fin n) ℝ) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun y : ℝ^n ↦ eval y.ofLp P) := by
  have h : ContDiff ℝ k (fun z : Fin n → ℝ ↦ eval z P) :=
    (AnalyticOnNhd.eval_mvPolynomial P).contDiff
  exact h.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).contDiff

/-- The coordinate derivatives of polynomial evaluation are the evaluations of the algebraic
partial derivatives. -/
theorem partialDeriv_eval_ofLp (P : MvPolynomial (Fin n) ℝ) (i : Fin n) (x : ℝ^n) :
    ∂[i] (fun y : ℝ^n ↦ eval y.ofLp P) x = eval x.ofLp (pderiv i P) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)
  have hP : DifferentiableAt ℝ (fun z : Fin n → ℝ ↦ eval z P) (L x) :=
    (AnalyticOnNhd.eval_mvPolynomial P (L x) (Set.mem_univ _)).differentiableAt
  have hcomp : (fun y : ℝ^n ↦ eval y.ofLp P) = (fun z : Fin n → ℝ ↦ eval z P) ∘ L := rfl
  unfold partialDeriv
  rw [hcomp, fderiv_comp x hP L.differentiableAt, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.fderiv]
  have hsingle : (L : ℝ^n →L[ℝ] Fin n → ℝ) (EuclideanSpace.single i 1) = Pi.single i 1 :=
    rfl
  rw [hsingle]
  exact fderiv_eval_single P (L x) i

/-- The coordinate derivative of polynomial evaluation, as a function. -/
theorem partialDeriv_eval_ofLp_fun (P : MvPolynomial (Fin n) ℝ) (i : Fin n) :
    (fun x ↦ ∂[i] (fun y : ℝ^n ↦ eval y.ofLp P) x) = fun x ↦ eval x.ofLp (pderiv i P) :=
  funext (partialDeriv_eval_ofLp P i)

/-- The Laplacian of polynomial evaluation is the evaluation of the algebraic Laplacian. -/
theorem laplacian_eval_ofLp (P : MvPolynomial (Fin n) ℝ) (x : ℝ^n) :
    laplacian (fun y : ℝ^n ↦ eval y.ofLp P) x = eval x.ofLp (polynomialLaplacian P) := by
  unfold laplacian
  rw [polynomialLaplacian, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [partialDeriv_eval_ofLp_fun, partialDeriv_eval_ofLp]

/-- The Laplacian of a radial factor times a `C²` function:
`Δ (F(‖x‖²) q) = (4 ‖x‖² F'' + 2n F') q + 4 F' ∑ⱼ xⱼ ∂ⱼ q + F Δq`. -/
theorem laplacian_comp_norm_sq_mul {F : ℝ → ℝ} {q : ℝ^n → ℝ} {x : ℝ^n}
    (hF : ContDiffAt ℝ 2 F (‖x‖ ^ 2)) (hq : ContDiffAt ℝ 2 q x) :
    laplacian (fun y : ℝ^n ↦ F (‖y‖ ^ 2) * q y) x =
      (4 * ‖x‖ ^ 2 * deriv (deriv F) (‖x‖ ^ 2) + 2 * n * deriv F (‖x‖ ^ 2)) * q x +
        4 * deriv F (‖x‖ ^ 2) * ∑ j, x j * ∂[j] q x + F (‖x‖ ^ 2) * laplacian q x := by
  have hFn : ContDiffAt ℝ 2 (fun y : ℝ^n ↦ F (‖y‖ ^ 2)) x :=
    hF.comp x ((contDiff_norm_sq ℝ (n := 2)).contDiffAt)
  rw [PDE.laplacian_mul hFn hq, laplacian_comp_norm_sq F x hF]
  have hd : DifferentiableAt ℝ F (‖x‖ ^ 2) := hF.differentiableAt (by norm_num)
  simp only [partialDeriv_comp_norm_sq _ hd]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- The radial derivative of a radial factor times a function:
`∑ⱼ xⱼ ∂ⱼ (F(‖x‖²) q) = 2 ‖x‖² F'(‖x‖²) q + F(‖x‖²) ∑ⱼ xⱼ ∂ⱼ q`. -/
theorem sum_mul_partialDeriv_comp_norm_sq_mul {F : ℝ → ℝ} {q : ℝ^n → ℝ} {x : ℝ^n}
    (hF : DifferentiableAt ℝ F (‖x‖ ^ 2)) (hq : DifferentiableAt ℝ q x) :
    ∑ j, x j * ∂[j] (fun y : ℝ^n ↦ F (‖y‖ ^ 2) * q y) x =
      2 * ‖x‖ ^ 2 * deriv F (‖x‖ ^ 2) * q x + F (‖x‖ ^ 2) * ∑ j, x j * ∂[j] q x := by
  simp only [partialDeriv_comp_norm_sq_mul _ hF hq]
  have hnorm : ‖x‖ ^ 2 = ∑ j, x j * x j := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hnorm, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end EuclideanLaplacian
