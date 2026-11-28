/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.EulerLagrange.Systems
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Dirichlet
public import PDE.CalculusOfVariations.PowerDirichlet
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Operators

/-!
# Hilbert's 20th problem: the general problem of boundary values

## Motivation

Hilbert's twentieth problem is about "the existence of solutions of partial differential
equations when the values on the boundary of the region are prescribed". He expects a proof
"by means of a general principle whose nature is indicated by Dirichlet's principle", and asks
(Newson's translation, p. 470):

> Has not every regular variation problem a solution, provided certain assumptions regarding
> the given boundary conditions are satisfied (say that the functions concerned in these
> boundary conditions are continuous and have in sections one or more derivatives), and
> provided also if need be that the notion of a solution shall be suitably extended?

In his nineteenth problem a regular variation problem is a double integral
`∬ F(p, q, z; x, y) dx dy = Minimum` with `p = z_x`, `q = z_y`, where `F` is analytic and
`F_pp F_qq - F_pq² > 0`. The inequality says that the matrix of second derivatives of `F` in
`p` and `q` is definite. When it is positive definite, that is when also `F_pp > 0`, `F` is
strictly convex in the derivatives.

## The idea

For integrands that are convex in the derivatives and grow like a power `p` of them, the
answer is yes, with the notion of a solution extended as Hilbert allows. This is a sufficient
condition from the direct method, not a theorem about every regular problem. The unknown is
a system `u` of `m` Sobolev functions of `n` variables in `W^{1,p}(Ω)` with `1 < p < ∞`. It
takes the boundary values of `g` when each component of `u - g` lies in `W₀^{1,p}(Ω)`, the
closure of the smooth functions with compact support in `Ω`. It solves the problem when it
minimizes `J(u) = ∫ F(x, u, Du) dx` among the systems with these boundary values.

The general principle is the direct method. A minimizing sequence is bounded because `F` grows
like `|Du|ᵖ` from below. A subsequence converges weakly, and its values converge strongly on a
bounded set. Convexity of `F` in `Du` makes `J` lower semicontinuous along it, so the limit is
a minimizer. Of Hilbert's regularity only convexity in the derivatives is used; it need not be
strict, and `F` need not be differentiable. The growth conditions are assumptions on the
integrand, which Hilbert's question does not make. His assumptions are on the boundary data,
and here the datum is any element of `W^{1,p}`.

On an open set `W^{1,p}(Ω)` and `W₀^{1,p}(Ω)` are the usual Sobolev spaces. The theorems are
stated for bounded measurable sets, on which these spaces are the graph spaces of the
library; on a set with empty interior the class of a datum can be a single system.

When `F` is differentiable and its derivative grows like `|(u, Du)|^{p-1}`, a solution
satisfies the Euler–Lagrange equations of the problem in the weak sense: the first variation
`∫ dF(x, u, Du)(φ, Dφ) dx` vanishes for every `φ` with zero boundary values. So the boundary
value problem for these equations has a solution. Dirichlet's principle is the case
`F = |Du|²`: Dirichlet's integral has a minimizer with given boundary values, and every
minimizer is weakly harmonic.

## Main results

* `exists_solution` (all `m`, all `n ≥ 1`, all bounded measurable sets, all `1 < p < ∞`, all
  convex integrands of growth `p` in the sense of `IsConvexIntegrand`, all data in `W^{1,p}`):
  the variational problem has a solution.
* `exists_solution_of_contDiffUpToBoundary` (the same on all bounded open sets): the boundary
  values may be given by functions that are continuously differentiable up to the boundary.
  `classicalData_ae` says that the Sobolev datum has these values and these derivatives.
* `IsSolution.isWeakSolution` (all solutions, all measurable integrands with a derivative of
  growth `p - 1` in the sense of `HasDerivativeGrowth`): a solution is a weak solution of the
  Euler–Lagrange system.
* `exists_isWeakSolution` (all cases of `exists_solution` with such a derivative): the boundary
  value problem for the Euler–Lagrange system has a weak solution, and it is a minimizer.
* `dirichlet_principle` (one family of integrands, `F = |Du|ᵖ`; all `m`, `n ≥ 1`, bounded
  measurable sets, `1 < p < ∞` and data): every premise above holds for it, so the integral
  has a minimizer with given boundary values, which solves `div(|Du|^{p-2} Du) = 0` weakly.
* `IsConvexIntegrand.add_bounded` (all convex integrands of growth `p`, bounded sets) and
  `isConvexIntegrand_powerDirichlet_add_cos` (one family, all `p ≥ 1`): the class contains
  integrands that depend on the point and the value and are not convex in the value.

## Relations

The general theorems are in the namespace `PDE.CalculusOfVariations`.

* `exists_solution` is `exists_minimizer_integral_vectorWkp_prescribed_boundary`, which rests
  on the lower semicontinuity theorem
  `lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient`. Without the upper
  growth bound `exists_minimizer_vectorWkpIntegral_prescribed_boundary` gives a minimizer of
  the extended energy, which may be `+∞` on every system of the class.
* `IsSolution.isWeakSolution` is `integral_firstVariation_eq_zero_of_integral_vectorWkp_le`.
* `isConvexIntegrand_powerDirichlet` and `hasDerivativeGrowth_powerDirichlet` show that the
  two sets of premises are satisfiable; `dirichlet_principle` is `exists_isWeakSolution` for
  them.
* On a bounded open set of positive dimension the linear problem `-div(a ∇u) + c u = f` in
  `Ω`, `u = g` on the boundary, has exactly one weak solution, for a bounded measurable matrix
  `a` that is uniformly elliptic almost everywhere, a bounded measurable `c ≥ 0`, `f ∈ L²(Ω)`
  and `g ∈ W^{1,2}(Ω)`:
  `SobolevSpace.GraphSpace.existsUnique_isInteriorWeakFullDivergenceSolution_prescribed_boundary`.
  For a load in the dual of `H¹₀(Ω)`, on a bounded set, it is
  `SobolevSpace.GraphSpace.existsUnique_interiorFullDivergenceOperator_prescribed_boundary`.
  Both follow from the Lax–Milgram theorem with data,
  `PDE.Analysis.Variational.existsUnique_eq_add_and_forall_eq`. For the Laplacian this is
  `SobolevSpace.GraphSpace.existsUnique_weak_harmonic_extension`. These are stated for one
  unknown in `H¹(Ω)`; the identification with the system of one unknown here is not proved.

## What stays open

* Attainment of the boundary values in the classical sense, and regularity up to the
  boundary. The boundary condition here is `u - g ∈ W₀^{1,p}`, and the set needs no regularity.
  Interior regularity is the nineteenth problem.
* Boundary data that are continuous and differentiable "in sections". The datum here is any
  element of `W^{1,p}`; the proved classical case is continuous differentiability up to the
  boundary.
* Problems that are not coercive with an exponent `p > 1`. The area integrand of Hilbert's
  "surfaces of least area" has linear growth and is not covered. Surfaces of constant positive
  Gaussian curvature are not treated.
* Integrands whose lower bound depends on the value, such as `|Du|² / 2 - f(x) u` of Poisson's
  equation: `IsConvexIntegrand` asks for `c |Du|ᵖ - b(x) ≤ F` uniformly in `u`. The classical
  theorem allows a lower bound `c |Du|ᵖ - C |u|^q - b(x)` with `q < p`. For Poisson's equation
  the linear theorem above gives the solution.
* Boundary conditions on "the differential coefficients or any relations between these and the
  values of the function".
* Uniqueness for the integrands of this file. Strict convexity of the integral on the boundary
  class would give it. The library proves uniqueness in other settings: the linear theorems
  above, `PDE.CalculusOfVariations.existsUnique_minimizer_matrixWkpIntegral_of_finite_competitor`
  for smooth strictly convex densities and trace classes on `C¹` domains, and
  `SobolevSpace.GraphSpace.existsUnique_weak_solution_strictMonotone_wkp_prescribed_boundary`
  for strictly monotone equations.
* Integrands that are not convex in `Du`.

## References

* D. Hilbert, *Mathematical problems*, translated by M. W. Newson, Bull. Amer. Math. Soc. 8
  (1902), 437-479, problem 19 on pp. 469-470 and problem 20 on p. 470.
  <https://doi.org/10.1090/S0002-9904-1902-00923-3>
  Online: <https://mathcs.clarku.edu/~djoyce/hilbert/problems.html>. Hilbert's footnote to
  problem 20 refers to his lecture on Dirichlet's principle, Jahresber. d. Deutschen
  Math.-Vereinigung 8 (1900), p. 184.
* The direct method and the lower semicontinuity theorem for integrands that are measurable in
  `x`, continuous in `u` and convex in `Du` are stated in
  <https://en.wikipedia.org/wiki/Direct_method_in_the_calculus_of_variations> (read 27 November
  2026), which refers to B. Dacorogna, *Direct Methods in the Calculus of Variations*, Springer,
  1989. The book was not opened; the Lean modules named above give their own sources.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace PDE.CalculusOfVariations
open scoped ENNReal NNReal Sobolev Gradient

namespace PDE.HilbertProblems.Twentieth

/-! ### The variational problem -/

/-- The integral of the variational problem, `J(u) = ∫ F(x, u, Du) dx` over `Ω`, for a system
`u` of `m` Sobolev functions of `n` variables. `F x (s, ξ)` is the integrand at the point `x`,
the value `s ∈ ℝᵐ` and the matrix of derivatives `ξ ∈ ℝ^(m * n)`. This is a Bochner integral:
it is zero when `F(x, u, Du)` is not integrable. `IsSolution` therefore asks for integrability,
and a convex integrand of growth `p` is integrable on every system
(`IsConvexIntegrand.integrable`). -/
def energy {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ) (u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) : ℝ :=
  ∫ x, F x (vectorWkpValueCLM u x, ∇ u x) ∂domainMeasure n Ω

/-- `u` has the boundary values of `g` in the extended sense: each component of `u - g` lies in
`W₀^{1,p}(Ω)`, the closure of the smooth functions with compact support in `Ω`. -/
def HasBoundaryValues {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (g u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) : Prop :=
  ∀ i, u i - g i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)

/-- `u` solves the variational problem with boundary values `g`: it has these boundary values,
its integral is finite, and no system with these boundary values and a finite integral has a
smaller one. "Finite" means that `F(x, u, Du)` is integrable. For an integrand that is bounded
below by an integrable function, a system on which `F(x, v, Dv)` is not integrable has
integral `+∞`, so this is minimality among all systems with the boundary values. -/
def IsSolution {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ) (g u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) : Prop :=
  HasBoundaryValues g u ∧
    Integrable (fun x ↦ F x (vectorWkpValueCLM u x, ∇ u x)) (domainMeasure n Ω) ∧
    ∀ v : Fin m → W^{1,(p : ℝ≥0∞)}(Ω), HasBoundaryValues g v →
      Integrable (fun x ↦ F x (vectorWkpValueCLM v x, ∇ v x)) (domainMeasure n Ω) →
      energy F u ≤ energy F v

/-- `u` is a weak solution of the Euler–Lagrange system of an integrand with derivative `dF`:
for every system `φ` with zero boundary values the first variation
`∫ dF(x, u, Du)(φ, Dφ) dx` exists and is zero. With `dF(x, s, ξ)(v, η) = F_s v + F_ξ η` this
is the weak form of `div F_ξ(x, u, Du) = F_s(x, u, Du)`. -/
def IsWeakSolution {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (dF : ℝ^n → ℝ^m × ℝ^(m * n) → (ℝ^m × ℝ^(m * n)) →L[ℝ] ℝ)
    (u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) : Prop :=
  ∀ φ : Fin m → W^{1,(p : ℝ≥0∞)}(Ω),
    (∀ i, φ i ∈ wkp0SubmoduleOn (n := n) (k := 1) (p := (p : ℝ≥0∞)) (Ω := Ω)) →
    Integrable (fun x ↦ dF x (vectorWkpValueCLM u x, ∇ u x) (vectorWkpValueCLM φ x, ∇ φ x))
      (domainMeasure n Ω) ∧
    (∫ x, dF x (vectorWkpValueCLM u x, ∇ u x) (vectorWkpValueCLM φ x, ∇ φ x)
      ∂domainMeasure n Ω) = 0

/-- A convex integrand of growth `p` on `Ω`: `F(x, s, ξ)` is jointly measurable and, for almost
every `x` in `Ω`, continuous in the value `s`, convex in the derivatives `ξ`, at least
`c |ξ|ᵖ - b(x)` with `c > 0` and `b` integrable, and at most `a(x) + D |(s, ξ)|ᵖ` with `a`
integrable. The norm of the pair `(s, ξ)` is the larger of the two Euclidean norms. Convexity
in `ξ` is what existence uses of a positive definite second derivative, Hilbert's regularity.
The two bounds keep a minimizing sequence bounded and the integral finite. -/
structure IsConvexIntegrand {m n : ℕ} (Ω : Set (ℝ^n)) (p : ℝ≥0)
    (F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ) : Prop where
  /-- The integrand is jointly measurable. -/
  measurable : Measurable (Function.uncurry F)
  /-- The integrand is continuous in the value. -/
  continuous_value : ∀ᵐ x ∂domainMeasure n Ω, ∀ ξ : ℝ^(m * n),
    Continuous fun s : ℝ^m ↦ F x (s, ξ)
  /-- The integrand is convex in the derivatives. -/
  convex_gradient : ∀ᵐ x ∂domainMeasure n Ω, ∀ s : ℝ^m,
    ConvexOn ℝ univ fun ξ : ℝ^(m * n) ↦ F x (s, ξ)
  /-- Coercivity: the integrand is at least `c |ξ|ᵖ - b(x)`. -/
  coercive : ∃ c : ℝ, 0 < c ∧ ∃ b : ℝ^n → ℝ, Integrable b (domainMeasure n Ω) ∧
    ∀ᵐ x ∂domainMeasure n Ω, ∀ (s : ℝ^m) (ξ : ℝ^(m * n)), c * ‖ξ‖ ^ (p : ℝ) - b x ≤ F x (s, ξ)
  /-- Growth: the integrand is at most `a(x) + D |(s, ξ)|ᵖ`. -/
  growth : ∃ D : ℝ, ∃ a : ℝ^n → ℝ, Integrable a (domainMeasure n Ω) ∧
    ∀ᵐ x ∂domainMeasure n Ω, ∀ z : ℝ^m × ℝ^(m * n), F x z ≤ a x + D * ‖z‖ ^ (p : ℝ)

/-- The integrand has a derivative of growth `p - 1`: for almost every `x` in `Ω`, `dF x z` is
the derivative of `F x` at every `z = (s, ξ)` and its norm is at most `h(x) + C |z|^{p-1}`,
with `h` in `L^q` for the conjugate exponent `q`; and `dF` is jointly measurable in the
point, the state and the direction. -/
structure HasDerivativeGrowth {m n : ℕ} (Ω : Set (ℝ^n)) (p : ℝ≥0)
    (F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ)
    (dF : ℝ^n → ℝ^m × ℝ^(m * n) → (ℝ^m × ℝ^(m * n)) →L[ℝ] ℝ) : Prop where
  /-- The derivative is jointly measurable. -/
  measurable : Measurable fun z : (ℝ^n) × (ℝ^m × ℝ^(m * n)) × (ℝ^m × ℝ^(m * n)) ↦
    dF z.1 z.2.1 z.2.2
  /-- `dF` is the derivative of the integrand in the value and the derivatives. -/
  hasFDerivAt : ∀ᵐ x ∂domainMeasure n Ω, ∀ z, HasFDerivAt (F x) (dF x z) z
  /-- The derivative has growth of order `p - 1`. -/
  growth : ∃ C : ℝ, ∃ h : ℝ^n → ℝ,
    MemLp h (ENNReal.conjExponent (p : ℝ≥0∞)) (domainMeasure n Ω) ∧
    ∀ᵐ x ∂domainMeasure n Ω, ∀ z, ‖dF x z‖ ≤ h x + C * ‖z‖ ^ ((p : ℝ) - 1)

/-! ### Existence -/

section Existence

variable {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
  {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ}

/-- The integral of a convex integrand of growth `p` is finite on every Sobolev system. -/
theorem IsConvexIntegrand.integrable (hF : IsConvexIntegrand Ω p F)
    (u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
    Integrable (fun x ↦ F x (vectorWkpValueCLM u x, ∇ u x)) (domainMeasure n Ω) := by
  obtain ⟨c, hc, b, hb, hlower⟩ := hF.coercive
  obtain ⟨D, a, ha, hupper⟩ := hF.growth
  exact integrable_vectorWkp_density_of_le hF.measurable ha hb hc.le hlower hupper u

/-- **Hilbert's twentieth problem, existence.** On a bounded measurable set of positive
dimension, for `1 < p < ∞`, every variational problem with a convex integrand of growth `p`
has a solution for every boundary datum `g ∈ W^{1,p}`: a system `u` with the boundary values
of `g` whose integral `∫ F(x, u, Du)` is finite and least among all systems with these
boundary values.
The number of unknown functions is arbitrary, the integrand need not be differentiable and the
boundary of the set need not be regular.

This is the direct method, with lower semicontinuity from convexity in the derivatives:
`exists_minimizer_integral_vectorWkp_prescribed_boundary`. -/
theorem exists_solution [Fact (0 < n)]
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (hp : 1 < p)
    (hF : IsConvexIntegrand Ω p F) (g : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
    ∃ u, IsSolution F g u := by
  obtain ⟨c, hc, b, hb, hlower⟩ := hF.coercive
  obtain ⟨D, a, ha, hupper⟩ := hF.growth
  obtain ⟨u, hu, hmin⟩ := exists_minimizer_integral_vectorWkp_prescribed_boundary hΩ hbounded
    hp hF.measurable ha hb hF.continuous_value hF.convex_gradient hc hlower hupper g
  exact ⟨u, hu, hF.integrable u, fun v hv _ ↦ hmin v hv⟩

/-- For a convex integrand of growth `p` a solution minimizes the integral among all systems
with its boundary values: every such system has a finite integral. -/
theorem IsSolution.energy_le (hF : IsConvexIntegrand Ω p F)
    {g u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)} (hu : IsSolution F g u)
    (v : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) (hv : HasBoundaryValues g v) :
    energy F u ≤ energy F v :=
  hu.2.2 v hv (hF.integrable v)

omit [Fact (1 ≤ (p : ℝ≥0∞))] in
/-- On a bounded set, adding a bounded term `h(x, u)` that is measurable and continuous in `u`
keeps a convex integrand of growth `p`. The term need not be convex in `u`, so the integrands
of `exists_solution` need not be convex in the value. -/
theorem IsConvexIntegrand.add_bounded (hbounded : Bornology.IsBounded Ω)
    (hF : IsConvexIntegrand Ω p F) {h : ℝ^n → ℝ^m → ℝ}
    (hh : Measurable (Function.uncurry h))
    (hcont : ∀ᵐ x ∂domainMeasure n Ω, Continuous (h x)) {M : ℝ} (hM : ∀ x s, |h x s| ≤ M) :
    IsConvexIntegrand Ω p fun x z ↦ F x z + h x z.1 := by
  have := isFiniteMeasure_domainMeasure_of_isBounded hbounded
  obtain ⟨c, hc, b, hb, hlow⟩ := hF.coercive
  obtain ⟨D, a, ha, hup⟩ := hF.growth
  refine ⟨hF.measurable.add (hh.comp (measurable_fst.prodMk measurable_snd.fst)), ?_, ?_,
    ⟨c, hc, fun x ↦ b x + M, hb.add (integrable_const M), ?_⟩,
    ⟨D, fun x ↦ a x + M, ha.add (integrable_const M), ?_⟩⟩
  · filter_upwards [hF.continuous_value, hcont] with x hx hc ξ
    exact (hx ξ).add hc
  · filter_upwards [hF.convex_gradient] with x hx s
    exact (hx s).add_const (h x s)
  · filter_upwards [hlow] with x hx s ξ
    have h1 := hx s ξ
    have h2 := (abs_le.mp (hM x s)).1
    linarith
  · filter_upwards [hup] with x hx z
    have h1 := hx z
    have h2 := (abs_le.mp (hM x z.1)).2
    linarith

end Existence

/-! ### Boundary values that are continuously differentiable up to the boundary -/

section ClassicalData

variable {m n : ℕ} {Ω : Set (ℝ^n)} {g : Fin m → ℝ^n → ℝ}

/-- The Sobolev system of boundary data `g` that are continuously differentiable up to the
boundary of a bounded open set: each `g i` is continuously differentiable in `Ω`, and it and
its first derivatives are uniformly continuous there, so they extend continuously to the
closure. Such a system lies in `W^{1,p}` for every `p`. It depends only on the values of `g`
inside `Ω`; the boundary values meant are those of the continuous extension. -/
def classicalData (hg : ∀ i, ContDiffUpToBoundary 1 (g i) Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (p : ℝ≥0) :
    Fin m → W^{1,(p : ℝ≥0∞)}(Ω) :=
  fun i ↦ (hg i).toWkpSpaceOn hopen hbounded p

/-- The Sobolev datum of classical boundary data has the values of `g` and the gradient of
`g`, almost everywhere in `Ω`. -/
theorem classicalData_ae (hg : ∀ i, ContDiffUpToBoundary 1 (g i) Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))]
    (i : Fin m) :
    (wkpBaseCoordinateCLM (classicalData hg hopen hbounded p i) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] g i ∧
      (wkpGradientCLM (classicalData hg hopen hbounded p i) : ℝ^n → ℝ^n)
        =ᵐ[domainMeasure n Ω] ∇ (g i) :=
  ⟨(hg i).toWkpSpaceOn_base_ae hopen hbounded p, (hg i).gradient_toWkpSpaceOn_ae hopen hbounded p⟩

/-- **Existence for classical boundary values.** On a bounded open set of positive dimension,
for `1 < p < ∞` and a convex integrand of growth `p`, the variational problem has a solution
with the boundary values of any functions `g i` that are continuously differentiable up to the
boundary. This is `exists_solution` for the datum `classicalData`. -/
theorem exists_solution_of_contDiffUpToBoundary [Fact (0 < n)]
    {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))] {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) (hp : 1 < p)
    (hF : IsConvexIntegrand Ω p F) (hg : ∀ i, ContDiffUpToBoundary 1 (g i) Ω) :
    ∃ u, IsSolution F (classicalData hg hopen hbounded p) u :=
  exists_solution hopen.measurableSet hbounded hp hF _

end ClassicalData

/-! ### The Euler–Lagrange system -/

section EulerLagrange

variable {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
  {F : ℝ^n → ℝ^m × ℝ^(m * n) → ℝ}
  {dF : ℝ^n → ℝ^m × ℝ^(m * n) → (ℝ^m × ℝ^(m * n)) →L[ℝ] ℝ}

/-- **A solution of the variational problem solves the Euler–Lagrange system weakly.** Let
`F` be measurable with a derivative of growth `p - 1`, and let `u` solve the variational
problem with some boundary values. Then the first variation of the integral at `u` vanishes
in every direction with zero boundary values. No convexity is assumed.

This is `integral_firstVariation_eq_zero_of_integral_vectorWkp_le`: the integral is finite
and differentiable along `u + t φ` because the derivative has conjugate growth, and its
derivative at the minimum `t = 0` is zero. -/
theorem IsSolution.isWeakSolution (hF : Measurable (Function.uncurry F))
    (hdF : HasDerivativeGrowth Ω p F dF) {g u : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)}
    (hu : IsSolution F g u) :
    IsWeakSolution dF u := by
  obtain ⟨C, h, hh, hgrowth⟩ := hdF.growth
  intro φ hφ
  exact integral_firstVariation_eq_zero_of_integral_vectorWkp_le
    (p := (p : ℝ≥0∞)) (q := ENNReal.conjExponent (p : ℝ≥0∞)) ENNReal.coe_ne_top hF
    hdF.measurable hdF.hasFDerivAt hh
    (by simpa only [ENNReal.coe_toReal] using hgrowth) g u hu.1 hu.2.1 hu.2.2 φ hφ

/-- **Hilbert's twentieth problem for the Euler–Lagrange system.** On a bounded measurable set
of positive dimension, for `1 < p < ∞`, a convex integrand of growth `p` with a derivative of
growth `p - 1` and every boundary datum `g ∈ W^{1,p}`, there is a system `u` with the boundary
values of `g` that is a weak solution of the Euler–Lagrange system. It is a solution of the
variational problem. -/
theorem exists_isWeakSolution [Fact (0 < n)]
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (hp : 1 < p)
    (hF : IsConvexIntegrand Ω p F) (hdF : HasDerivativeGrowth Ω p F dF)
    (g : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
    ∃ u, IsSolution F g u ∧ IsWeakSolution dF u := by
  obtain ⟨u, hu⟩ := exists_solution hΩ hbounded hp hF g
  exact ⟨u, hu, hu.isWeakSolution hF.measurable hdF⟩

end EulerLagrange

/-! ### Dirichlet's principle: the premises are satisfiable -/

section Dirichlet

open PDE.CalculusOfVariations.PowerDirichlet

variable {m n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0}

/-- The integrand `|Du|ᵖ` is a convex integrand of growth `p`, for every `p ≥ 1`, every number
of unknowns and every set. For `p = 2` it is the integrand of Dirichlet's integral. -/
theorem isConvexIntegrand_powerDirichlet (hp : 1 ≤ p) :
    IsConvexIntegrand Ω p (density m n (p : ℝ)) where
  measurable := measurable_density
  continuous_value := Filter.Eventually.of_forall fun _ ξ ↦
    (continuous_const : Continuous fun _ : ℝ^m ↦ ‖ξ‖ ^ (p : ℝ))
  convex_gradient := Filter.Eventually.of_forall fun x s ↦
    convexOn_density (by exact_mod_cast hp) x s
  coercive := ⟨1, one_pos, 0, integrable_zero _ _ _, Filter.Eventually.of_forall fun x s ξ ↦ by
    rw [one_mul, Pi.zero_apply, sub_zero]
    exact le_rfl⟩
  growth := ⟨1, 0, integrable_zero _ _ _, Filter.Eventually.of_forall fun x z ↦ by
    rw [Pi.zero_apply, zero_add, one_mul]
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_snd_le z) (NNReal.coe_nonneg p)⟩

/-- The integrand `|Du|ᵖ` has the derivative `(v, η) ↦ p |Du|^{p-2} ⟪Du, η⟫`, of growth
`p - 1`, for every `p > 1`. -/
theorem hasDerivativeGrowth_powerDirichlet (hp : 1 < p) :
    HasDerivativeGrowth Ω p (density m n (p : ℝ)) (densityDeriv m n (p : ℝ)) where
  measurable := measurable_densityDeriv
  hasFDerivAt := Filter.Eventually.of_forall fun x z ↦
    hasFDerivAt_density (by exact_mod_cast hp) x z
  growth := ⟨p, 0, MemLp.zero, Filter.Eventually.of_forall fun x z ↦ by
    rw [Pi.zero_apply, zero_add]
    exact norm_densityDeriv_le (by exact_mod_cast hp) x z⟩

/-- An integrand that depends on the point and the value: on a bounded set,
`|Du|ᵖ + cos(|x| + |u|)` is a convex integrand of growth `p`, for every `p ≥ 1`. For at least
one unknown function it is not convex in the value. So `exists_solution` applies to it when
`p > 1` and the set is measurable, in positive dimension. -/
theorem isConvexIntegrand_powerDirichlet_add_cos (hbounded : Bornology.IsBounded Ω)
    (hp : 1 ≤ p) :
    IsConvexIntegrand Ω p fun x z ↦
      density m n (p : ℝ) x z + Real.cos (‖x‖ + ‖z.1‖) :=
  (isConvexIntegrand_powerDirichlet hp).add_bounded hbounded
    (h := fun x s ↦ Real.cos (‖x‖ + ‖s‖))
    (Real.continuous_cos.comp (continuous_fst.norm.add continuous_snd.norm)).measurable
    (Filter.Eventually.of_forall fun _ ↦
      Real.continuous_cos.comp (continuous_const.add continuous_norm))
    (M := 1) (fun _ _ ↦ Real.abs_cos_le_one _)

/-- **Dirichlet's principle.** On a bounded measurable set of positive dimension, for every
number of unknowns, every `1 < p < ∞` and every boundary datum `g ∈ W^{1,p}`, the integral
`∫ |Du|ᵖ` has a minimizer `u` with the boundary values of `g`, and
`∫ p |Du|^{p-2} ⟪Du, Dφ⟫ = 0` for every `φ` with zero boundary values. For `p = 2` the integral
is Dirichlet's and `u` is weakly harmonic. Every premise of `exists_isWeakSolution` holds
here. -/
theorem dirichlet_principle [Fact (0 < n)] [Fact (1 ≤ (p : ℝ≥0∞))]
    (hΩ : MeasurableSet Ω) (hbounded : Bornology.IsBounded Ω) (hp : 1 < p)
    (g : Fin m → W^{1,(p : ℝ≥0∞)}(Ω)) :
    ∃ u, IsSolution (density m n (p : ℝ)) g u ∧ IsWeakSolution (densityDeriv m n (p : ℝ)) u :=
  exists_isWeakSolution hΩ hbounded hp (isConvexIntegrand_powerDirichlet hp.le)
    (hasDerivativeGrowth_powerDirichlet hp) g

end Dirichlet

end PDE.HilbertProblems.Twentieth
