/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SecondDirectionalDerivative
public import Mathlib.Analysis.Complex.Exponential
import CAS.ExactTactic

/-!
# Elliptic operators with a factored principal part

We use the sign convention of Evans's nondivergence form (2) in §6.4,

`Lu = -∑ₖ D²u[σₖ, σₖ] + Du[b] + cu`.

In Euclidean coordinates the principal matrix is `σσᵀ`. The factors are the coefficient data here;
they need not be continuous to prove the pointwise maximum principle. At a local maximum the drift
vanishes and the principal part is nonnegative, which is Evans's observation (1) in this factored
form.

An exponential of a linear functional supplies the strict barrier used by the weak maximum
principle. Only a positive lower bound in that one direction and an upper bound on the drift in the
same direction are needed for this barrier. Uniform ellipticity is a sufficient, stronger
assumption.

## Main definitions

* `factoredOperator`: the operator `L` with principal factors `σ`, drift `b` and potential `c`.

## Main results

* `factoredOperator_nonneg_at_localMax`: `Lu ≥ 0` at a local maximum where `cu ≥ 0`.
* `factoredOperator_exp_clm`: the residual of the barrier `exp (μℓ)` for a continuous linear
  functional `ℓ`.
* `strict_subsolution_le_of_boundary_le`: a strict subsolution on an open set with compact closure
  stays below a boundary upper bound `M` with `cM ≥ 0`, as in steps 1-3 of Evans's proof of §6.4.1,
  Theorem 1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.4, (1) and the nondivergence form (2), p. 344, and §6.4.1,
  steps 1-4 of the proof of Theorem 1 (Weak maximum principle), (5)-(10), pp. 345-346.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace EllipticMaximum

open PDE.Analysis Set
open scoped Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- A nondivergence operator with principal coefficient `σσᵀ`, drift `b`, and potential `c`.
Its classical interpretation requires two derivatives of the argument. -/
def factoredOperator (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    (u : E → ℝ) (x : E) : ℝ :=
  -(∑ k, secondDirectionalDerivative u x (σ x k)) + fderiv ℝ u x (b x) + c x * u x

/-- At a local maximum, the operator is nonnegative whenever its potential term is
nonnegative. No strict ellipticity or coefficient regularity is needed for this local fact. -/
theorem factoredOperator_nonneg_at_localMax
    (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    {u : E → ℝ} {x : E} (hmax : IsLocalMax u x) (hu : ContDiffAt ℝ 2 u x)
    (hcu : 0 ≤ c x * u x) :
    0 ≤ factoredOperator σ b c u x := by
  have hprincipal : ∑ k, secondDirectionalDerivative u x (σ x k) ≤ 0 :=
    Finset.sum_nonpos fun k _ ↦
      secondDirectionalDerivative_nonpos_at_localMax hmax hu.continuousAt _
  simp only [factoredOperator, hmax.fderiv_eq_zero, zero_apply, add_zero]
  exact add_nonneg (neg_nonneg.mpr hprincipal) hcu

/-- The operator commutes with addition at a common `C²` point. -/
theorem factoredOperator_add (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    {u v : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    factoredOperator σ b c (fun y ↦ u y + v y) x =
      factoredOperator σ b c u x + factoredOperator σ b c v x := by
  have hderiv : fderiv ℝ (fun y ↦ u y + v y) x = fderiv ℝ u x + fderiv ℝ v x :=
    fderiv_add (hu.differentiableAt (by norm_num)) (hv.differentiableAt (by norm_num))
  simp only [factoredOperator, secondDirectionalDerivative_add hu hv,
    Finset.sum_add_distrib, hderiv, add_apply]
  ring

/-- The operator commutes with scalar multiplication at a differentiability point. -/
theorem factoredOperator_const_mul (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    {u : E → ℝ} {x : E} (hu : DifferentiableAt ℝ u x) (a : ℝ) :
    factoredOperator σ b c (fun y ↦ a * u y) x = a * factoredOperator σ b c u x := by
  have hderiv : fderiv ℝ (fun y ↦ a * u y) x = a • fderiv ℝ u x := by
    simpa only [smul_eq_mul] using fderiv_fun_const_smul hu a
  simp only [factoredOperator, secondDirectionalDerivative_const_mul,
    ← Finset.mul_sum, hderiv, smul_apply, smul_eq_mul]
  ring

/-- Subtracting a constant changes only the potential term. -/
theorem factoredOperator_sub_const (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    (u : E → ℝ) (x : E) (a : ℝ) :
    factoredOperator σ b c (fun y ↦ u y - a) x =
      factoredOperator σ b c u x - c x * a := by
  simp only [factoredOperator, secondDirectionalDerivative, deriv_sub_const_fun,
    fderiv_sub_const]
  ring

/-- The operator commutes with negation, including its totalized values. -/
theorem factoredOperator_neg (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    (u : E → ℝ) (x : E) :
    factoredOperator σ b c (fun y ↦ -u y) x = -factoredOperator σ b c u x := by
  have hderiv : fderiv ℝ (fun y ↦ -u y) x = -fderiv ℝ u x := fderiv_neg
  simp only [factoredOperator, secondDirectionalDerivative_neg, Finset.sum_neg_distrib,
    hderiv, neg_apply]
  ring

/-- The operator of a difference is the difference of the operators at a common `C²` point. -/
theorem factoredOperator_sub (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    {u v : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hv : ContDiffAt ℝ 2 v x) :
    factoredOperator σ b c (fun y ↦ u y - v y) x =
      factoredOperator σ b c u x - factoredOperator σ b c v x := by
  simp only [sub_eq_add_neg]
  rw [factoredOperator_add σ b c hu hv.neg, factoredOperator_neg]

/-- The affine-line curvature of an exponential of a linear functional. -/
theorem secondDirectionalDerivative_exp_clm (ℓ : E →L[ℝ] ℝ) (μ : ℝ) (x v : E) :
    secondDirectionalDerivative (fun y ↦ Real.exp (μ * ℓ y)) x v =
      (μ * ℓ v) ^ 2 * Real.exp (μ * ℓ x) := by
  have hline : (fun s : ℝ ↦ Real.exp (μ * ℓ (x + s • v))) =
      fun s : ℝ ↦ Real.exp (μ * (ℓ x + s * ℓ v)) := by
    funext s
    simp only [map_add, map_smul, smul_eq_mul]
  have hfirst (s : ℝ) :
      HasDerivAt (fun t : ℝ ↦ Real.exp (μ * (ℓ x + t * ℓ v)))
        (μ * ℓ v * Real.exp (μ * (ℓ x + s * ℓ v))) s := by
    cas
  have hsecond :
      HasDerivAt (fun s : ℝ ↦ μ * ℓ v * Real.exp (μ * (ℓ x + s * ℓ v)))
        ((μ * ℓ v) ^ 2 * Real.exp (μ * ℓ x)) 0 := by
    cas
  simp only [secondDirectionalDerivative, hline,
    show deriv (fun s : ℝ ↦ Real.exp (μ * (ℓ x + s * ℓ v))) =
      (fun s ↦ μ * ℓ v * Real.exp (μ * (ℓ x + s * ℓ v))) from
        funext fun s ↦ (hfirst s).deriv]
  exact hsecond.deriv

/-- The residual of the exponential barrier, before choosing its growth rate. -/
theorem factoredOperator_exp_clm (σ : E → ι → E) (b : E → E) (c : E → ℝ)
    (ℓ : E →L[ℝ] ℝ) (μ : ℝ) (x : E) :
    factoredOperator σ b c (fun y ↦ Real.exp (μ * ℓ y)) x =
      Real.exp (μ * ℓ x) *
        (-(μ ^ 2 * ∑ k, (ℓ (σ x k)) ^ 2) + μ * ℓ (b x) + c x) := by
  have hderiv : fderiv ℝ (fun y ↦ Real.exp (μ * ℓ y)) x =
      Real.exp (μ * ℓ x) • (μ • ℓ) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using (ℓ.hasFDerivAt.const_smul μ).exp.fderiv
  simp only [factoredOperator, secondDirectionalDerivative_exp_clm, hderiv,
    smul_apply, smul_eq_mul, mul_pow,
    ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- A strict subsolution cannot exceed a compatible boundary upper bound on a domain with
compact closure. The condition `0 ≤ cM` permits arbitrary bounds when `c = 0`. -/
theorem strict_subsolution_le_of_boundary_le
    {Ω : Set E} (hΩopen : IsOpen Ω) (hΩcompact : IsCompact (closure Ω))
    (σ : E → ι → E) (b : E → E) (c : E → ℝ) {u : E → ℝ} {M : ℝ}
    (hc : ∀ x ∈ Ω, 0 ≤ c x) (hcM : ∀ x ∈ Ω, 0 ≤ c x * M)
    (hucont : ContinuousOn u (closure Ω))
    (hureg : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x)
    (hsub : ∀ x ∈ Ω, factoredOperator σ b c u x < 0)
    (hboundary : ∀ x ∈ frontier Ω, u x ≤ M) :
    ∀ x ∈ closure Ω, u x ≤ M := by
  intro x hx
  by_contra hnot
  obtain ⟨z, hz, hzmax⟩ := hΩcompact.exists_isMaxOn ⟨x, hx⟩ hucont
  have hzM : M < u z := (lt_of_not_ge hnot).trans_le (hzmax hx)
  have hznot : z ∉ frontier Ω := fun h ↦ (not_lt_of_ge (hboundary z h)) hzM
  have hzΩ : z ∈ Ω := by
    have hz' : z ∈ closure Ω \ frontier Ω := ⟨hz, hznot⟩
    simpa only [closure_sdiff_frontier, hΩopen.interior_eq] using hz'
  have hzlocal : IsLocalMax u z := by
    filter_upwards [hΩopen.mem_nhds hzΩ] with y hy
    exact hzmax (subset_closure hy)
  have hcz : 0 ≤ c z * u z :=
    (hcM z hzΩ).trans (mul_le_mul_of_nonneg_left hzM.le (hc z hzΩ))
  exact (not_lt_of_ge
    (factoredOperator_nonneg_at_localMax σ b c hzlocal (hureg z hzΩ) hcz)) (hsub z hzΩ)

end EllipticMaximum
