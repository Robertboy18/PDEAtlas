/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Elliptic.Regularity.Analytic.System
public import PDE.FDeriv.PartialDeriv.Analytic
public import PDE.Analysis.Calculus.Gradient
public import PDE.Analysis.Calculus.Legendre.Linearization
public import PDE.Elliptic.Regularity.Quasilinear.Interior.HigherOrder.Coefficients

/-!
# Smooth solutions of Euler–Lagrange equations with analytic density are analytic

## Motivation

Is a smooth solution `u` of `div(∇F(∇u)) = 0` on an open set real-analytic when the density `F`
is real-analytic and its Hessian is positive definite at the gradients of `u`?

## The idea

Yes. Differentiate the equation in the direction `k`. Since second derivatives commute, the
gradient `v = (∂ₖ u)` solves the autonomous diagonal system

`∑ᵢ ∂ᵢ (∑ⱼ aᵢⱼ(v) ∂ⱼ vₖ) = 0`, with `aᵢⱼ = ∂ⱼ∂ᵢF`.

The coefficients are analytic functions of the gradient and the matrix `a(∇u(x))` is the Hessian
of `F` at `∇u(x)`, which is positive definite. The derivative bounds for such systems give
`|Dⁱ(∇u)| ≤ i! M K₀ⁱ` near every point, these are bounds `|Dⁱu| ≤ i! M Kⁱ` for `i ≥ 1`, and
bounds of this kind make `u` analytic.

## Main results

* `sum_partialDeriv_flux_gradient_eq_zero`: the differentiated equation at every point, for all
  `C³` solutions on all open sets and all densities that are `C³` at the gradients.
* `exists_iteratedCoordinateNorm_le_of_gradientDensity`: every point of the open set has a ball
  on which `|Dⁱu| ≤ i! M Kⁱ` for all `i ≥ 1`. All dimensions, all open sets, all smooth
  solutions, all densities analytic at the gradients with positive definite Hessian there.
* `analyticOnNhd_of_gradientDensity`: under the same hypotheses `u` is real-analytic on the
  open set.

## Relations

`analyticOnNhd_of_gradientDensity` follows from
`exists_iteratedCoordinateNorm_le_of_gradientDensity` and
`PDE.analyticAt_of_iteratedCoordinateNorm_le`. The bounds are
`exists_familyNorm_le_of_autonomous_system` applied to the gradient, with the equation from
`sum_partialDeriv_flux_gradient_eq_zero`. The coefficients are the ones of
`PDE.Elliptic.Regularity.Quasilinear.Bootstrap.contDiff_infty_hessianEntry`, and
`PDE.Elliptic.Regularity.Quasilinear.Bootstrap.hasZeroWeakDivergenceOn_linearized_gradientDensity`
is the weak form of the differentiated equation. The smooth counterpart of the theorem is
`PDE.Elliptic.Regularity.Quasilinear.contDiffOn_infty_of_gradientDensity`. For local minimizers
in `W^{1,2}_loc` the theorem is applied in
`PDE.CalculusOfVariations.exists_analytic_of_isLocalMinimizerOn`.

## What stays open

Densities that depend on `x` or `u`, and systems of equations for vector-valued `u`, are not
covered. Nothing is said about the boundary.

## References

* S. Blatt, *On the analyticity of solutions to non-linear elliptic partial differential
  equations*, arXiv:2009.08762v2, 2024, Theorem 1.1. That theorem covers fully nonlinear
  equations; here the equation is the Euler–Lagrange equation of a gradient density, and the
  proof is the one of `PDE.Elliptic.Regularity.Analytic.System`.
  <https://arxiv.org/abs/2009.08762>
-/

@[expose] public noncomputable section

open Filter Set Metric
open scoped ContDiff Topology Gradient RealInnerProductSpace
open PDE.Analysis PDE.Elliptic.Regularity.Quasilinear
open SobolevSpace.GraphSpace.BoundaryRegularity (principalEnergy)

namespace PDE.Elliptic.Regularity.Analytic

variable {n : ℕ} {Ω : Set (ℝ^n)} {F u : ℝ^n → ℝ}

/-- **The Hessian in coordinates.** For a density `F` that is `C²` at `p`, the quadratic form
of the matrix `(∂ⱼ∂ᵢF(p))` at a tuple `ξ` is the second derivative `D²F(p)(ξ, ξ)`. -/
theorem principalEnergy_jacobianMatrix_gradient {p : ℝ^n} (hF : ContDiffAt ℝ 2 F p)
    (ξ : Fin n → ℝ) :
    principalEnergy (fun i j ↦ jacobianMatrix (∇ F) p i j) ξ =
      fderiv ℝ (fderiv ℝ F) p (WithLp.toLp 2 ξ) (WithLp.toLp 2 ξ) := by
  have hd : DifferentiableAt ℝ (∇ F) p := (contDiffAt_gradient (m := 1) hF).differentiableAt_one
  rw [← inner_fderiv_gradient_at hF, PiLp.inner_apply]
  simp only [principalEnergy]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← sum_jacobianMatrix_mul hd (WithLp.toLp 2 ξ) i]
  simp only [RCLike.inner_apply, RCLike.conj_to_real, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The flux of the differentiated equation.** At a point where `u` is `C²` and `F` is `C²`
at the gradient, the flux of the component `k` of the gradient in the system with coefficients
`∂ⱼ∂ᵢF` is the `k`-th derivative of the `i`-th component of `∇F(∇u)`. This is the chain rule
and the symmetry of the second derivatives of `u`. -/
theorem flux_gradient_eq_partialDeriv {y : ℝ^n} (hu : ContDiffAt ℝ 2 u y)
    (hF : ContDiffAt ℝ 2 F (∇ u y)) (k i : Fin n) :
    flux (fun i j p ↦ jacobianMatrix (∇ F) (WithLp.toLp 2 p) i j) (fun _ _ _ ↦ 0)
      (fun z l ↦ ∇ u z l) k i y = (∂[k] (fun z ↦ ∇ F (∇ u z) i)) y := by
  have hdF : DifferentiableAt ℝ (fun p ↦ ∇ F p i) (∇ u y) :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).differentiableAt.comp _
      (contDiffAt_gradient (m := 1) hF).differentiableAt_one
  have hdu : DifferentiableAt ℝ (∇ u) y := (contDiffAt_gradient (m := 1) hu).differentiableAt_one
  rw [partialDeriv_comp k (fun p ↦ ∇ F p i) (∇ u) y hdF hdu]
  simp only [flux, sub_zero]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  change jacobianMatrix (∇ F) (∇ u y) i j * (∂[j] (fun z ↦ ∇ u z k)) y =
    (∂[j] (fun p ↦ ∇ F p i)) (∇ u y) * (∂[k] (fun z ↦ ∇ u z j)) y
  have hcomm : (∂[j] (fun z ↦ ∇ u z k)) y = (∂[k] (fun z ↦ ∇ u z j)) y := by
    simp only [gradient_apply_eq_partialDeriv]
    exact partialDeriv_partialDeriv_comm_at j k hu
  rw [hcomm]
  rfl

/-- **The differentiated Euler–Lagrange equation.** Let `u` be `C³` on the open set `Ω`, let `F`
be `C³` at the gradients of `u`, and let `div(∇F(∇u)) = 0` on `Ω`. Then at every point of `Ω`
and for every `k` the gradient `v = (∂ₗ u)` satisfies `∑ᵢ ∂ᵢ (∑ⱼ aᵢⱼ(v) ∂ⱼ vₖ) = 0` with the
coefficients `aᵢⱼ = ∂ⱼ∂ᵢF`. The left side is the `k`-th derivative of the divergence, which
vanishes on the open set. -/
theorem sum_partialDeriv_flux_gradient_eq_zero (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ 3 u Ω)
    (hF : ∀ x ∈ Ω, ContDiffAt ℝ 3 F (∇ u x))
    (heq : ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ u y)) x = 0) {x : ℝ^n} (hx : x ∈ Ω)
    (k : Fin n) :
    ∑ i, (∂[i] (flux (fun i j p ↦ jacobianMatrix (∇ F) (WithLp.toLp 2 p) i j) (fun _ _ _ ↦ 0)
      (fun z l ↦ ∇ u z l) k i)) x = 0 := by
  have hux (y : ℝ^n) (hy : y ∈ Ω) : ContDiffAt ℝ 3 u y := hu.contDiffAt (hΩ.mem_nhds hy)
  -- the components of `∇F(∇u)` are `C²` on `Ω`
  have hw (i : Fin n) (y : ℝ^n) (hy : y ∈ Ω) : ContDiffAt ℝ 2 (fun z ↦ ∇ F (∇ u z) i) y :=
    (EuclideanSpace.proj i : ℝ^n →L[ℝ] ℝ).contDiff.contDiffAt.comp y
      ((contDiffAt_gradient (m := 2) (hF y hy)).comp y (contDiffAt_gradient (m := 2) (hux y hy)))
  -- near `x` the flux is the `k`-th derivative of the `i`-th component of `∇F(∇u)`
  have h1 (i : Fin n) :
      (∂[i] (flux (fun i j p ↦ jacobianMatrix (∇ F) (WithLp.toLp 2 p) i j) (fun _ _ _ ↦ 0)
        (fun z l ↦ ∇ u z l) k i)) x =
        (∂[i] (fun y ↦ (∂[k] (fun z ↦ ∇ F (∇ u z) i)) y)) x :=
    partialDeriv_congr_nhds i (Filter.eventually_of_mem (hΩ.mem_nhds hx) fun y hy ↦
      flux_gradient_eq_partialDeriv ((hux y hy).of_le (by norm_num))
        ((hF y hy).of_le (by norm_num)) k i)
  -- the two derivatives commute
  have h2 (i : Fin n) : (∂[i] (fun y ↦ (∂[k] (fun z ↦ ∇ F (∇ u z) i)) y)) x =
      (∂[k] (fun y ↦ (∂[i] (fun z ↦ ∇ F (∇ u z) i)) y)) x :=
    partialDeriv_partialDeriv_comm_at i k (hw i x hx)
  -- the sum over `i` is the `k`-th derivative of the divergence
  have h3 : (∂[k] (fun y ↦ ∑ i, (∂[i] (fun z ↦ ∇ F (∇ u z) i)) y)) x =
      ∑ i, (∂[k] (fun y ↦ (∂[i] (fun z ↦ ∇ F (∇ u z) i)) y)) x :=
    partialDeriv_sum Finset.univ (fun i _ ↦
      ((hw i x hx).partialDeriv i (k := 1) (by norm_num)).differentiableAt_one) k
  -- the divergence vanishes near `x`
  have h4 : (∂[k] (fun y ↦ ∑ i, (∂[i] (fun z ↦ ∇ F (∇ u z) i)) y)) x = 0 := by
    have h0 : (fun y ↦ ∑ i, (∂[i] (fun z ↦ ∇ F (∇ u z) i)) y) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) :=
      Filter.eventually_of_mem (hΩ.mem_nhds hx) fun y hy ↦ heq y hy
    rw [partialDeriv_congr_nhds k h0, partialDeriv_const]
  rw [Finset.sum_congr rfl fun i _ ↦ (h1 i).trans (h2 i), ← h3, h4]

/-- **Derivative bounds for solutions of Euler–Lagrange equations.** Let `Ω ⊆ ℝ^n` be open, let
`u` be smooth on `Ω` with `div(∇F(∇u)) = 0` there, let `F` be real-analytic at the gradients
`∇u(x)`, `x ∈ Ω`, and let the Hessian of `F` be positive definite at these gradients. Then
every point of `Ω` is the centre of a ball in `Ω` on which `|Dⁱu| ≤ i! M Kⁱ` in the coordinate
norm, for all `i ≥ 1`. The gradient solves a system with analytic coefficients
(`sum_partialDeriv_flux_gradient_eq_zero`), and
`exists_familyNorm_le_of_autonomous_system` bounds its derivatives. -/
theorem exists_iteratedCoordinateNorm_le_of_gradientDensity (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ ∞ u Ω) (hF : ∀ x ∈ Ω, AnalyticAt ℝ F (∇ u x))
    (hpos : ∀ x ∈ Ω, ∃ lam > 0, ∀ ξ : ℝ^n, lam * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) (∇ u x) ξ ξ)
    (heq : ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ u y)) x = 0) {x₀ : ℝ^n} (hx₀ : x₀ ∈ Ω) :
    ∃ r > 0, ∃ M K : ℝ, 0 < M ∧ 0 < K ∧ ball x₀ r ⊆ Ω ∧
      ∀ i, 1 ≤ i → ∀ x ∈ ball x₀ r, iteratedCoordinateNorm i u x ≤ i.factorial * M * K ^ i := by
  -- the gradient is a smooth family
  have hg : ContDiffOn ℝ ∞ (fun z l ↦ ∇ u z l) Ω := contDiffOn_pi.mpr fun l ↦ by
    have hl : (fun z ↦ ∇ u z l) = ∂[l] u := funext fun z ↦ gradient_apply_eq_partialDeriv u z l
    rw [hl]
    exact hu.partialDeriv l hΩ le_rfl
  -- the coefficients are analytic at the gradients
  have ha : ∀ x ∈ Ω, ∀ i j, AnalyticAt ℝ
      (fun p : Fin n → ℝ ↦ jacobianMatrix (∇ F) (WithLp.toLp 2 p) i j) (fun l ↦ ∇ u x l) := by
    intro x hx i j
    have h2 : AnalyticAt ℝ (∂[j] (∂[i] F)) (∇ u x) := ((hF x hx).partialDeriv i).partialDeriv j
    have hlin : AnalyticAt ℝ (fun p : Fin n → ℝ ↦ (WithLp.toLp 2 p : ℝ^n)) (fun l ↦ ∇ u x l) :=
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).symm :
        (Fin n → ℝ) →L[ℝ] ℝ^n).analyticAt _
    refine (h2.comp_of_eq hlin rfl).congr (Filter.Eventually.of_forall fun p ↦ ?_)
    exact (jacobianMatrix_gradient_apply F (WithLp.toLp 2 p) i j).symm
  -- the matrix of coefficients at the gradient is the Hessian, which is positive definite
  have hell : ∀ x ∈ Ω, ∃ lam > 0, ∀ ξ : Fin n → ℝ, lam * ∑ i, ξ i ^ 2 ≤
      principalEnergy (fun i j ↦ jacobianMatrix (∇ F) (WithLp.toLp 2 fun l ↦ ∇ u x l) i j) ξ := by
    intro x hx
    obtain ⟨lam, hlam, h⟩ := hpos x hx
    refine ⟨lam, hlam, fun ξ ↦ ?_⟩
    have hn : ‖(WithLp.toLp 2 ξ : ℝ^n)‖ ^ 2 = ∑ i, ξ i ^ 2 := EuclideanSpace.real_norm_sq_eq _
    have h2 : principalEnergy
        (fun i j ↦ jacobianMatrix (∇ F) (WithLp.toLp 2 fun l ↦ ∇ u x l) i j) ξ =
        fderiv ℝ (fderiv ℝ F) (∇ u x) (WithLp.toLp 2 ξ) (WithLp.toLp 2 ξ) :=
      principalEnergy_jacobianMatrix_gradient (p := ∇ u x) (hF x hx).contDiffAt ξ
    rw [h2, ← hn]
    exact h (WithLp.toLp 2 ξ)
  -- the differentiated equation
  have heq' : ∀ x ∈ Ω, ∀ k, ∑ i, (∂[i] (flux
      (fun i j p ↦ jacobianMatrix (∇ F) (WithLp.toLp 2 p) i j) (fun _ _ _ ↦ 0)
      (fun z l ↦ ∇ u z l) k i)) x = 0 := fun x hx k ↦
    sum_partialDeriv_flux_gradient_eq_zero hΩ (hu.of_le (by simp))
      (fun y hy ↦ (hF y hy).contDiffAt) heq hx k
  obtain ⟨r, hr, M, K₀, hM, hK₀, hsub, hb⟩ := exists_familyNorm_le_of_autonomous_system hΩ hg ha
    (fun _ _ _ _ ↦ analyticAt_const) hell heq' hx₀
  refine ⟨r, hr, M, max K₀ 1, hM, by positivity, hsub, fun i hi x hx ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  -- the derivatives of order `j + 1` of `u` are the derivatives of order `j` of the gradient
  have hid : iteratedCoordinateNorm (j + 1) u x = familyNorm j (fun z l ↦ ∇ u z l) x := by
    simp only [iteratedCoordinateNorm, familyNorm, familyNormSq, iteratedCoordinateNormSq,
      gradient_apply_eq_partialDeriv]
  rw [hid]
  refine (hb j x hx).trans ?_
  have h1 : (j.factorial : ℝ) ≤ (j + 1).factorial :=
    Nat.cast_le.mpr (Nat.factorial_le (Nat.le_succ j))
  have h2 : K₀ ^ j ≤ max K₀ 1 ^ (j + 1) :=
    (pow_le_pow_left₀ hK₀.le (le_max_left _ _) j).trans
      (pow_le_pow_right₀ (le_max_right _ _) (Nat.le_succ j))
  exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hM.le) h2 (pow_nonneg hK₀.le j)
    (mul_nonneg (Nat.cast_nonneg _) hM.le)

/-- **Analyticity of solutions of Euler–Lagrange equations with analytic density.** Let
`Ω ⊆ ℝ^n` be open and let `u` be smooth on `Ω` with `div(∇F(∇u)) = 0` at every point of `Ω`.
If `F` is real-analytic at the gradients `∇u(x)`, `x ∈ Ω`, and its Hessian is positive definite
at these gradients, then `u` is real-analytic on `Ω`. All dimensions and all open sets; the
ellipticity constant may depend on the point, and `F` need not be convex or analytic away
from the gradients of `u`. The derivative bounds of
`exists_iteratedCoordinateNorm_le_of_gradientDensity` make the Taylor series of `u`
converge. -/
theorem analyticOnNhd_of_gradientDensity (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hF : ∀ x ∈ Ω, AnalyticAt ℝ F (∇ u x))
    (hpos : ∀ x ∈ Ω, ∃ lam > 0, ∀ ξ : ℝ^n, lam * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) (∇ u x) ξ ξ)
    (heq : ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ u y)) x = 0) : AnalyticOnNhd ℝ u Ω := by
  intro x₀ hx₀
  obtain ⟨r, hr, M, K, -, -, hsub, hb⟩ :=
    exists_iteratedCoordinateNorm_le_of_gradientDensity hΩ hu hF hpos heq hx₀
  exact analyticAt_of_iteratedCoordinateNorm_le hr (hu.mono hsub) hb

end PDE.Elliptic.Regularity.Analytic
