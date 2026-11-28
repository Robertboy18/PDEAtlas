/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.OneUnknown
public import PDE.CalculusOfVariations.LocalMinimizer.Analytic
public import PDE.HilbertProblems.Twentieth
import PDE.Analysis.Calculus.Gradient.HessianBounds
import PDE.Analysis.Calculus.Gradient.HessianNorm
import PDE.Analysis.Calculus.Gradient.QuadraticGrowth
import PDE.CalculusOfVariations.LocalMinimizer.Classical

/-!
# Hilbert's 19th problem: are the solutions of regular variational problems analytic?

## Motivation

The title of Hilbert's nineteenth problem is the question (Newson's translation, p. 469):

> Are the solutions of regular problems in the calculus of variations always necessarily
> analytic?

A regular variation problem is, for him, a problem `∬ F(p, q, z; x, y) dx dy = Minimum` with
`p = z_x`, `q = z_y`, where `F` is analytic and `F_pp F_qq - F_pq² > 0` "for all values of the
arguments which fall within the range of discussion". He asks "whether all solutions of
regular variation problems must necessarily be analytic functions", and continues:

> In other words, does every lagrangian partial differential equation of a regular variation
> problem have the property of admitting analytic integrals exclusively? And is this the case
> even when the function is constrained to assume, as, e. g., in Dirichlet's problem on the
> potential function, boundary values which are continuous, but not analytic?

## The idea

For one unknown function and an integrand `F(∇z)` of the gradient alone, in any number of
variables, the answer is yes when the regularity is uniform: `F` is real-analytic and
`θ |ξ|² ≤ D²F(p)(ξ, ξ) ≤ Λ |ξ|²` with `θ > 0`. A local minimizer in `W^{1,2}_loc` has a
representative that is real-analytic and solves the Euler–Lagrange equation at every point.
The proof is in the general theory, in three steps: the first derivatives are Hölder
continuous (`PDE.CalculusOfVariations.exists_holder_gradient_of_isLocalMinimizerOn`), the
minimizer is smooth (`PDE.CalculusOfVariations.exists_smooth_of_isLocalMinimizerOn`), and a
smooth solution of the equation is analytic
(`PDE.Elliptic.Regularity.Analytic.analyticOnNhd_of_gradientDensity`).

A solution of the Euler–Lagrange equation with two continuous derivatives is a local
minimizer, because the integrand is convex. So it is analytic. This is the answer to the
question in Hilbert's second form, for these integrands.

For two variables the uniform bounds give `F_pp > 0` and Hilbert's inequality. So the
integrands of the theorem are regular in his sense, with a positive definite second
derivative.

The question about boundary values joins the nineteenth problem with the twentieth. A
solution of the variational problem with boundary values `g` exists for every
`g ∈ W^{1,2}(Ω)`, by the twentieth problem; such a `g` need not be continuous, let alone
analytic. The solution is a local minimizer, so it has a representative that is analytic in
`Ω`. The boundary condition is the weak one, `u - g ∈ W₀^{1,2}(Ω)`.

## Main results

* `IsRegular.exists_analytic` (all dimensions, all open sets, all integrands that are regular
  in the sense of `IsRegular`, all local minimizers in `W^{1,2}_loc`): a real-analytic
  representative that solves the Euler–Lagrange equation.
* `IsRegular.analyticOnNhd_of_contDiffOn` (all dimensions, all open sets, all such integrands,
  all solutions of class `C²`): a function with two continuous derivatives that solves the
  Euler–Lagrange equation at every point is real-analytic.
* `IsRegular.hilbert_inequality` (two variables, all such integrands): `F_pp > 0` and
  `F_pp F_qq - F_pq² > 0` at every point.
* `exists_analytic_of_isSolution` (all `n ≥ 1`, all bounded open sets, all such integrands, all
  boundary data in `W^{1,2}`, all solutions in the sense of the twentieth problem): a solution
  of the variational problem with given boundary values has a representative that is
  real-analytic in `Ω`.
* `exists_analytic_solution` (same scope): for every boundary datum a solution exists, and it
  has a representative that is real-analytic in `Ω`.
* `isRegular_normSq` (one integrand, all dimensions): Dirichlet's integrand `|ξ|² / 2` is
  regular, so the premises hold for it. It is the only instance of `IsRegular` in the library.

## Relations

* `IsRegular.exists_analytic` is
  `PDE.CalculusOfVariations.exists_analytic_of_isLocalMinimizerOn` with the hypotheses on `F`
  collected in `IsRegular`, and `IsRegular.analyticOnNhd_of_contDiffOn` is
  `PDE.CalculusOfVariations.analyticOnNhd_of_contDiffOn_two` in the same way.
* A regular integrand that is not quadratic: for `|ξ|² / 2 + (1 - cos ξᵢ) / 2` analyticity
  and the two bounds on the second derivative are proved in the example module of
  `PDE.Examples.CalculusOfVariations.cosineDensity`, and the general analyticity theorem is
  applied to it there. They are stated as hypotheses of the general theorems, not as an
  instance of the structure of this file.
* `exists_analytic_solution` is `PDE.HilbertProblems.Twentieth.exists_solution` followed by
  `exists_analytic_of_isSolution`. The integrand of the twentieth problem for one unknown is
  `integrand F`, through `PDE.CalculusOfVariations.oneUnknownDensity`, and
  `isConvexIntegrand_integrand` shows that it is a convex integrand of growth `2`.
* `PDE.CalculusOfVariations.exists_analytic_minimizer_prescribed_boundary` is the same
  conclusion stated for one function in `H¹(Ω)`, with its own existence step.

## What stays open

* Integrands that depend on `x` or `z`, as Hilbert's `F(p, q, z; x, y)` does.
* Regular problems that are not uniformly regular. The area integrand `√(1 + p² + q²)` of the
  minimal surface equation, which Hilbert names, has `F_pp F_qq - F_pq² > 0` with no positive
  lower bound, and is not covered.
* Several unknown functions. There the answer is no in general. De Giorgi's discontinuous
  solution of a linear elliptic system, and the integral of Giusti and Miranda, whose
  Euler–Lagrange system is solved by the discontinuous function `x / |x|`, are entries of
  BlowupZoo and not part of this library.
* Boundary values that are only continuous. Hilbert asks about a continuous boundary function.
  Here the datum is a function `g ∈ W^{1,2}(Ω)` and the boundary condition is
  `u - g ∈ W₀^{1,2}(Ω)`. A continuous function on the boundary need not have an extension in
  `W^{1,2}(Ω)`, and it is not proved that the solution takes continuous boundary values at
  every point of the boundary.
* Uniqueness of the solution with given boundary values.
* Analyticity up to the boundary.

## References

* D. Hilbert, *Mathematical problems*, translated by M. W. Newson, Bull. Amer. Math. Soc. 8
  (1902), 437-479, problem 19 on pp. 469-470. <https://doi.org/10.1090/S0002-9904-1902-00923-3>
  Online: <https://mathcs.clarku.edu/~djoyce/hilbert/problems.html>.
* The sources of the regularity theorem are those of
  `PDE.CalculusOfVariations.LocalMinimizer.Analytic`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.Analysis PDE.CalculusOfVariations
open scoped ENNReal NNReal Sobolev Gradient

namespace PDE.HilbertProblems.Nineteenth

/-! ### Regular integrands -/

/-- A uniformly regular integrand `F(∇z)` of one unknown function of `n` variables: `F` is
real-analytic, and its second derivative satisfies `θ |ξ|² ≤ D²F(p)(ξ, ξ) ≤ Λ |ξ|²` for all
`p` and `ξ`, with `θ > 0`. For two variables this implies Hilbert's inequality
`F_pp F_qq - F_pq² > 0` (`IsRegular.hilbert_inequality`). -/
structure IsRegular {n : ℕ} (F : ℝ^n → ℝ) : Prop where
  /-- The integrand is real-analytic. -/
  analytic : AnalyticOnNhd ℝ F univ
  /-- The second derivative is uniformly positive definite. -/
  elliptic : ∃ θ : ℝ, 0 < θ ∧ ∀ p ξ, θ * ‖ξ‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ F) p ξ ξ
  /-- The second derivative is bounded. -/
  bounded : ∃ Λ : ℝ, ∀ p ξ, fderiv ℝ (fderiv ℝ F) p ξ ξ ≤ Λ * ‖ξ‖ ^ 2

variable {n : ℕ} {Ω : Set (ℝ^n)} {F : ℝ^n → ℝ}

/-- **Hilbert's nineteenth problem for one unknown.** Let `Ω ⊆ ℝⁿ` be open and let `F` be a
uniformly regular integrand. Every local minimizer of `∫ F(∇u)` in `W^{1,2}_loc(Ω)` has a
representative that is real-analytic on `Ω` and satisfies the Euler–Lagrange equation
`div(∇F(∇v)) = 0` at every point of `Ω`.

This is `PDE.CalculusOfVariations.exists_analytic_of_isLocalMinimizerOn`. -/
theorem IsRegular.exists_analytic (hF : IsRegular F) (hΩ : IsOpen Ω)
    {u : ℝ^n → ℝ} (hu : IsLocallyWkpOn 1 2 Ω u) (hmin : IsLocalMinimizerOn F Ω u) :
    ∃ v : ℝ^n → ℝ, AnalyticOnNhd ℝ v Ω ∧ v =ᵐ[volume.restrict Ω] u ∧
      ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  obtain ⟨θ, hθ, hell⟩ := hF.elliptic
  obtain ⟨Λ, hbound⟩ := hF.bounded
  exact exists_analytic_of_isLocalMinimizerOn hΩ hF.analytic hθ hell hbound hu hmin

/-- **Solutions of the Lagrangian equation are analytic.** Let `Ω ⊆ ℝⁿ` be open and let `F`
be a uniformly regular integrand. Every function `v` with two continuous derivatives on `Ω`
that satisfies the Euler–Lagrange equation `div(∇F(∇v)) = 0` at every point of `Ω` is
real-analytic on `Ω`. In Hilbert's words, the equation admits "analytic integrals
exclusively" among the functions of class `C²`.

This is `PDE.CalculusOfVariations.analyticOnNhd_of_contDiffOn_two`: a classical solution is a
local minimizer, because `F` is convex. -/
theorem IsRegular.analyticOnNhd_of_contDiffOn (hF : IsRegular F) (hΩ : IsOpen Ω)
    {v : ℝ^n → ℝ} (hv : ContDiffOn ℝ 2 v Ω)
    (hdiv : ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0) :
    AnalyticOnNhd ℝ v Ω := by
  obtain ⟨θ, hθ, hell⟩ := hF.elliptic
  obtain ⟨Λ, hbound⟩ := hF.bounded
  exact analyticOnNhd_of_contDiffOn_two hΩ hF.analytic hθ hell hbound hv hdiv

/-- **Hilbert's inequality.** For two variables, a uniformly regular integrand satisfies
`F_pp > 0` and `F_pp F_qq - F_pq² > 0` at every point, where `F_pp`, `F_pq` and `F_qq` are the
second derivatives of `F` in the two coordinate directions. So it defines a regular variation
problem in Hilbert's sense, with a positive definite second derivative.

With `a = F_pp`, `c = F_qq`, `d = F_pq` the lower bound says that
`(a - θ) s² + 2 d s t + (c - θ) t² ≥ 0` for all `s`, `t`. Hence `d² ≤ (a - θ)(c - θ)`, and
`a c - d² ≥ θ (a + c) - θ² ≥ θ²`. -/
theorem IsRegular.hilbert_inequality {F : ℝ^2 → ℝ} (hF : IsRegular F) (p : ℝ^2) :
    0 < fderiv ℝ (fderiv ℝ F) p (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) ∧
    0 < fderiv ℝ (fderiv ℝ F) p (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) *
        fderiv ℝ (fderiv ℝ F) p (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) -
      fderiv ℝ (fderiv ℝ F) p (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) ^ 2 := by
  obtain ⟨θ, hθ, hell⟩ := hF.elliptic
  set b := fderiv ℝ (fderiv ℝ F) p with hb
  set e₀ : ℝ^2 := EuclideanSpace.single 0 1 with he₀
  set e₁ : ℝ^2 := EuclideanSpace.single 1 1 with he₁
  -- the second derivative is symmetric
  have hF2 : ContDiff ℝ 2 F := hF.analytic.contDiff
  have hsymm : b e₁ e₀ = b e₀ e₁ :=
    ((hF2.contDiffAt (x := p)).isSymmSndFDerivAt (by simp)).eq e₁ e₀
  -- the quadratic form on the vector `s e₀ + t e₁`
  have hquad (s t : ℝ) : θ * (s ^ 2 + t ^ 2) ≤
      s ^ 2 * b e₀ e₀ + 2 * (s * t) * b e₀ e₁ + t ^ 2 * b e₁ e₁ := by
    have h := hell p (s • e₀ + t • e₁)
    have hnorm : ‖s • e₀ + t • e₁‖ ^ 2 = s ^ 2 + t ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
      simp [he₀, he₁]
    rw [hnorm] at h
    have hexp : b (s • e₀ + t • e₁) (s • e₀ + t • e₁) =
        s ^ 2 * b e₀ e₀ + 2 * (s * t) * b e₀ e₁ + t ^ 2 * b e₁ e₁ := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hsymm]
      ring
    rwa [hexp] at h
  set a := b e₀ e₀
  set c := b e₁ e₁
  set d := b e₀ e₁
  have ha : θ ≤ a := by
    have h := hquad 1 0
    norm_num at h
    exact h
  have hc : θ ≤ c := by
    have h := hquad 0 1
    norm_num at h
    exact h
  -- `d² ≤ (a - θ) (c - θ)`
  have hdet : d ^ 2 ≤ (a - θ) * (c - θ) := by
    rcases eq_or_lt_of_le hc with hc0 | hcpos
    · -- `c = θ`: then `d = 0`
      have hd : d = 0 := by
        by_contra hd
        have h := hquad 1 (-(a - θ + 1) / (2 * d))
        have h2 : 2 * ((1 : ℝ) * (-(a - θ + 1) / (2 * d))) * d = -(a - θ + 1) := by
          field_simp
        rw [h2, ← hc0] at h
        linarith
      rw [hd, ← hc0]
      simp
    · have h := hquad (c - θ) (-d)
      by_contra hlt
      nlinarith [mul_pos (sub_pos.mpr hcpos) (sub_pos.mpr (not_le.mp hlt))]
  refine ⟨hθ.trans_le ha, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left ha hθ.le, mul_le_mul_of_nonneg_left hc hθ.le,
    mul_pos hθ hθ]

/-! ### The join with the twentieth problem -/

/-- The integrand of the twentieth problem for one unknown function that corresponds to
`F(∇z)`: it reads the one row of the matrix of derivatives as the gradient. -/
def integrand (F : ℝ^n → ℝ) : ℝ^n → ℝ^1 × ℝ^(1 * n) → ℝ :=
  oneUnknownDensity fun _ z ↦ F z.2

/-- The integrand of a uniformly regular problem is a convex integrand of growth `2` on every
bounded set: the lower bound on the second derivative gives convexity and coercivity, and the
upper bound gives quadratic growth. So the twentieth problem applies to it. -/
theorem isConvexIntegrand_integrand (hb : Bornology.IsBounded Ω) (hF : IsRegular F) :
    Twentieth.IsConvexIntegrand Ω 2 (integrand F) := by
  obtain ⟨θ, hθ, hell⟩ := hF.elliptic
  obtain ⟨Λ, hbound⟩ := hF.bounded
  have hF2 : ContDiff ℝ 2 F := hF.analytic.contDiff
  have hnorm (p : ℝ^n) : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ.toNNReal :=
    norm_hessian_le_of_quadratic_le hF2.contDiffAt hθ.le (hell p) (hbound p)
  have := isFiniteMeasure_domainMeasure_of_isBounded hb
  refine ⟨measurable_oneUnknownDensity (hF2.continuous.measurable.comp measurable_snd.snd),
    Filter.Eventually.of_forall fun _ ξ ↦
      (continuous_const : Continuous fun _ : ℝ^1 ↦ F (rowEquiv n ξ)),
    Filter.Eventually.of_forall fun _ _ ↦
      (((strongConvexOn_of_hessian_bound hF2 hell).strictConvexOn hθ).convexOn.comp_linearMap
        (rowEquiv n).toLinearEquiv.toLinearMap),
    ⟨θ / 4, by positivity, fun _ ↦ |F 0| + ‖fderiv ℝ F 0‖ ^ 2 / θ, integrable_const _,
      Filter.Eventually.of_forall fun x s ξ ↦ ?_⟩,
    ⟨Λ.toNNReal + 1, fun _ ↦ |F 0| + ‖fderiv ℝ F 0‖ ^ 2, integrable_const _,
      Filter.Eventually.of_forall fun x z ↦ ?_⟩⟩
  · -- coercivity, from the lower bound of the second derivative
    have h := quadratic_lower_bound_of_hessian_bound hF2 hθ hell (rowEquiv n ξ)
    rw [LinearIsometryEquiv.norm_map] at h
    have h' : θ / 4 * ‖ξ‖ ^ 2 - (|F 0| + ‖fderiv ℝ F 0‖ ^ 2 / θ) ≤ integrand F x (s, ξ) := h
    simpa only [NNReal.coe_ofNat, Real.rpow_two] using h'
  · -- growth, from the upper bound of the second derivative
    have h := quadratic_upper_bound_of_hessian_bound hF2 (NNReal.coe_nonneg _) hnorm
      (rowEquiv n z.2)
    rw [LinearIsometryEquiv.norm_map] at h
    have hz : ‖z.2‖ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le z) 2
    have hpos : (0 : ℝ) ≤ (Λ.toNNReal : ℝ) + 1 := by positivity
    have h' := mul_le_mul_of_nonneg_left hz hpos
    simp only [NNReal.coe_ofNat, Real.rpow_two]
    exact h.trans (by linarith)

section Join

/-- **A solution with given boundary values is analytic inside.** Let `Ω ⊆ ℝⁿ` be bounded and
open and let `F` be a uniformly regular integrand. If `u` solves the variational problem of the
twentieth problem for the integrand `F(∇z)` of one unknown, with the boundary values of any
`g ∈ W^{1,2}(Ω)`, then `u` has a representative that is real-analytic on `Ω` and satisfies the
Euler–Lagrange equation at every point of `Ω`. The datum need not be continuous or analytic.

A minimizer in the boundary class is a local minimizer
(`isLocalMinimizerOn_of_prescribed_boundary`), and `IsRegular.exists_analytic` applies. -/
theorem exists_analytic_of_isSolution (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hF : IsRegular F) {g u : Fin 1 → W^{1,((2 : ℝ≥0) : ℝ≥0∞)}(Ω)}
    (hu : Twentieth.IsSolution (integrand F) g u) :
    ∃ v : ℝ^n → ℝ, AnalyticOnNhd ℝ v Ω ∧
      v =ᵐ[volume.restrict Ω] baseRepresentative (u 0) ∧
      ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  obtain ⟨θ, hθ, hell⟩ := hF.elliptic
  obtain ⟨Λ, hbound⟩ := hF.bounded
  have hF2 : ContDiff ℝ 2 F := hF.analytic.contDiff
  have hnorm (p : ℝ^n) : ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ Λ.toNNReal :=
    norm_hessian_le_of_quadratic_le hF2.contDiffAt hθ.le (hell p) (hbound p)
  -- the component minimizes the scalar integral in the scalar boundary class
  have hmin := (forall_integral_oneUnknownDensity_le_iff (fun _ z ↦ F z.2) g u).mp
    fun v hv ↦ hu.energy_le (isConvexIntegrand_integrand hb hF) v hv
  obtain ⟨hloc, hlm⟩ := isLocalMinimizerOn_of_prescribed_boundary hΩ hb
    (hF2.differentiable (by norm_num)) (lipschitzWith_gradient_of_hessian_bound hF2 hnorm)
    (g 0) (u 0) (hu.1 0) hmin
  exact hF.exists_analytic hΩ hloc hlm

/-- **The nineteenth and the twentieth problem together.** Let `Ω ⊆ ℝⁿ` be bounded and open,
`n ≥ 1`, and let `F` be a uniformly regular integrand. For every boundary datum
`g ∈ W^{1,2}(Ω)` the variational problem for `∫ F(∇z)` has a solution with the boundary values
of `g`, in the sense `u - g ∈ W₀^{1,2}(Ω)`, and the solution has a representative that is
real-analytic in `Ω`.

Existence is `Twentieth.exists_solution`; analyticity is `exists_analytic_of_isSolution`. -/
theorem exists_analytic_solution [Fact (0 < n)] (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hF : IsRegular F) (g : Fin 1 → W^{1,((2 : ℝ≥0) : ℝ≥0∞)}(Ω)) :
    ∃ u, Twentieth.IsSolution (integrand F) g u ∧
      ∃ v : ℝ^n → ℝ, AnalyticOnNhd ℝ v Ω ∧
        v =ᵐ[volume.restrict Ω] baseRepresentative (u 0) ∧
        ∀ x ∈ Ω, PDE.divergence (fun y ↦ ∇ F (∇ v y)) x = 0 := by
  obtain ⟨u, hu⟩ := Twentieth.exists_solution hΩ.measurableSet hb (by norm_num)
    (isConvexIntegrand_integrand hb hF) g
  exact ⟨u, hu, exists_analytic_of_isSolution hΩ hb hF hu⟩

end Join

/-! ### Dirichlet's integrand is regular -/

/-- Dirichlet's integrand `|ξ|² / 2` is uniformly regular in every dimension, with
`θ = Λ = 1`: its second derivative is the inner product. So the premises of the theorems of
this file are satisfiable, and the solutions of Dirichlet's problem have analytic
representatives inside. -/
theorem isRegular_normSq (n : ℕ) : IsRegular fun ξ : ℝ^n ↦ ‖ξ‖ ^ 2 / 2 := by
  have hderiv (ξ : ℝ^n) : HasFDerivAt (fun ξ : ℝ^n ↦ ‖ξ‖ ^ 2 / 2) (innerSL ℝ ξ) ξ := by
    simp only [div_eq_mul_inv]
    refine ((hasStrictFDerivAt_norm_sq ξ).hasFDerivAt.mul_const (2⁻¹ : ℝ)).congr_fderiv ?_
    ext η
    simp
  have hd : fderiv ℝ (fun ξ : ℝ^n ↦ ‖ξ‖ ^ 2 / 2) = fun ξ ↦ innerSL ℝ ξ :=
    funext fun ξ ↦ (hderiv ξ).fderiv
  have hinner (p : ℝ^n) : fderiv ℝ (fun ξ : ℝ^n ↦ innerSL ℝ ξ) p = innerSL ℝ :=
    (innerSL ℝ : ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ).hasFDerivAt.fderiv
  have hdd (p ξ : ℝ^n) : fderiv ℝ (fderiv ℝ fun ξ : ℝ^n ↦ ‖ξ‖ ^ 2 / 2) p ξ ξ = ‖ξ‖ ^ 2 := by
    rw [hd, hinner]
    exact real_inner_self_eq_norm_sq ξ
  exact ⟨((contDiff_norm_sq ℝ).div_const 2).analyticOnNhd,
    ⟨1, one_pos, fun p ξ ↦ by rw [hdd, one_mul]⟩, ⟨1, fun p ξ ↦ by rw [hdd, one_mul]⟩⟩

end PDE.HilbertProblems.Nineteenth
