/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.PrincipalForms

/-!
# Nemytskii loads for semilinear Dirichlet equations

A weak solution of the semilinear Dirichlet problem

`-Δu + g(x, u) = f` in `Ω`, `u = 0` on `∂Ω`

is a `u ∈ H¹₀(Ω)` such that `∫ ∇u·∇v + ∫ g(x, u) v = ∫ f v` for every
`v ∈ H¹₀(Ω)`, the nonlinear integrand being integrable. The monotonicity and
variational theories instead work with an abstract load `N : H¹₀(Ω) → L²(Ω)`
representing the Nemytskii operator `u ↦ g(·, u(·))`. We define the
integral weak formulation and prove that, whenever `N u` represents
`g(x, u(x))` in `L²`, the dual pairing of `N u` with a test function is the
Nemytskii integral, so the integral and abstract formulations coincide.

## Main results

* `IsDirichletSemilinearWeakSolution`: the integral weak formulation,
  including integrability of the nonlinear pairing.
* `isDirichletSemilinearWeakSolution_zero`: `u = 0` solves the homogeneous
  problem when `g(x, 0) = 0` almost everywhere.
* `dirichletNemytskii_pairing_eq_integral`,
  `isDirichletSemilinearWeakSolution_iff_nemytskii_load`: the equivalence of
  the represented load and the integral equation.

## Implementation notes

Integrability is part of the definition because the Bochner integral is
totalized: without it the integral identity could hold vacuously for a
nonintegrable integrand. Which nonlinearities admit an `L²` representative
depends on the dimension and the Sobolev embedding, so `N` and its
representation property are hypotheses rather than constructions here.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.3, Definitions (iii) (weak solution of
  `-Δu = f(u)` with zero boundary values), p. 544.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Pointwise product between a Nemytskii nonlinearity evaluated at `u`
and the base coordinate of a test function `v`. -/
def dirichletNemytskiiIntegrand
    (g : ℝ^n → ℝ → ℝ)
    (u v : H¹₀(Ω)) (x : ℝ^n) : ℝ :=
  g x
      ((baseCoordCLM (n := n) (Ω := Ω) u :
          ℝ^n → ℝ) x) *
    (baseCoordCLM (n := n) (Ω := Ω) v :
        ℝ^n → ℝ) x

/-- The integral weak formulation of

`-Δu + g(x, u) = f`

with homogeneous Dirichlet boundary data. Integrability of the nonlinear
pairing is included explicitly because the Bochner integral is totalized on
nonintegrable functions. -/
def IsDirichletSemilinearWeakSolution
    (g : ℝ^n → ℝ → ℝ)
    (f : DerivLp n 2 Ω) (u : H¹₀(Ω)) : Prop :=
  (∀ v : H¹₀(Ω),
      Integrable
        (dirichletNemytskiiIntegrand g u v)
        (domainMeasure n Ω)) ∧
    ∀ v : H¹₀(Ω),
      dirichletForm (n := n) (Ω := Ω) u v +
          ∫ x, dirichletNemytskiiIntegrand g u v x
            ∂domainMeasure n Ω =
        loadFunctional (n := n) (Ω := Ω) f v

namespace IsDirichletSemilinearWeakSolution

/-- The nonlinear pairing of a semilinear weak solution with every test
function is integrable. -/
theorem integrable_nemytskiiIntegrand
    {g : ℝ^n → ℝ → ℝ}
    {f : DerivLp n 2 Ω} {u : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution g f u)
    (v : H¹₀(Ω)) :
    Integrable
      (dirichletNemytskiiIntegrand g u v)
      (domainMeasure n Ω) :=
  hu.1 v

/-- The tested integral identity satisfied by a semilinear weak solution. -/
theorem equation
    {g : ℝ^n → ℝ → ℝ}
    {f : DerivLp n 2 Ω} {u : H¹₀(Ω)}
    (hu : IsDirichletSemilinearWeakSolution g f u)
    (v : H¹₀(Ω)) :
    dirichletForm (n := n) (Ω := Ω) u v +
        ∫ x, dirichletNemytskiiIntegrand g u v x
          ∂domainMeasure n Ω =
      loadFunctional (n := n) (Ω := Ω) f v :=
  hu.2 v

end IsDirichletSemilinearWeakSolution

/-- Moving a reaction to the right gives the literal integral-gradient equation
against every test. Integrability remains part of the equivalence. -/
theorem isDirichletSemilinearWeakSolution_neg_zero_iff
    (g : ℝ^n → ℝ → ℝ) (u : H¹₀(Ω)) :
    IsDirichletSemilinearWeakSolution (fun x z ↦ -g x z) 0 u ↔
      ∀ v : H¹₀(Ω),
        Integrable (dirichletNemytskiiIntegrand g u v) (domainMeasure n Ω) ∧
          (∫ x, inner ℝ (∇ (u : H¹(Ω)) x) (∇ (v : H¹(Ω)) x) ∂domainMeasure n Ω) =
            ∫ x, dirichletNemytskiiIntegrand g u v x ∂domainMeasure n Ω := by
  have hneg (v : H¹₀(Ω)) :
      dirichletNemytskiiIntegrand (fun x z ↦ -g x z) u v =
        -dirichletNemytskiiIntegrand g u v := by
    funext x
    exact neg_mul _ _
  constructor
  · intro hu v
    refine ⟨?_, ?_⟩
    · have hi := hu.1 v
      rw [hneg] at hi
      exact integrable_neg_iff.mp hi
    · have heq := hu.2 v
      simp only [hneg, Pi.neg_apply, integral_neg, loadFunctional_zero, zero_apply] at heq
      rw [dirichletForm_eq_integral_gradient,
        add_neg_eq_zero] at heq
      exact heq
  · intro hu
    constructor
    · intro v
      rw [hneg]
      exact (hu v).1.neg
    · intro v
      simp only [hneg, Pi.neg_apply, integral_neg, loadFunctional_zero, zero_apply]
      rw [dirichletForm_eq_integral_gradient,
        (hu v).2, add_neg_cancel]

/-- If the semilinear term vanishes at zero almost everywhere, then the zero
function solves the zero-forcing Dirichlet equation. -/
theorem isDirichletSemilinearWeakSolution_zero
    (g : ℝ^n → ℝ → ℝ)
    (hzero : ∀ᵐ x ∂domainMeasure n Ω, g x 0 = 0) :
    IsDirichletSemilinearWeakSolution (Ω := Ω) g 0 0 := by
  have hbaseZero :
      ((baseCoordCLM (n := n) (Ω := Ω)
          (0 : H¹₀(Ω)) : DerivLp n 2 Ω) :
          ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun _ ↦ (0 : ℝ) := by
    rw [map_zero]
    filter_upwards [
      MeasureTheory.Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)] with x hx
    simpa using hx
  have hintegrand (v : H¹₀(Ω)) :
      dirichletNemytskiiIntegrand g 0 v =ᵐ[
          domainMeasure n Ω]
        fun _ ↦ (0 : ℝ) := by
    filter_upwards [hbaseZero, hzero] with x hx hg
    simp only [dirichletNemytskiiIntegrand, hx, hg, zero_mul]
  constructor
  · intro v
    exact
      (MeasureTheory.integrable_zero (ℝ^n) ℝ
        (domainMeasure n Ω)).congr (hintegrand v).symm
  · intro v
    rw [MeasureTheory.integral_congr_ae (hintegrand v)]
    simp only [map_zero, zero_apply, MeasureTheory.integral_zero,
      zero_add, loadFunctional_zero]

/-- An `L²` representative of the Nemytskii term makes its product with
every `H¹₀` test function integrable. -/
theorem integrable_dirichletNemytskiiIntegrand
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (u v : H¹₀(Ω)) :
    Integrable
      (dirichletNemytskiiIntegrand g u v)
      (domainMeasure n Ω) := by
  have hinner := MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
    (N u) (baseCoordCLM (n := n) (Ω := Ω) v)
  apply hinner.congr
  filter_upwards [hNrep u] with x hx
  rw [hx]
  exact (mul_comm _ _).symm

/-- If `N(u)` represents `g(x,u(x))` in `L²(Ω)`, its dual pairing with
`v ∈ H¹₀(Ω)` is the corresponding Nemytskii integral. -/
theorem dirichletNemytskii_pairing_eq_integral
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (u v : H¹₀(Ω)) :
    loadFunctional (n := n) (Ω := Ω) (N u) v =
      ∫ x, dirichletNemytskiiIntegrand g u v x
        ∂domainMeasure n Ω := by
  rw [loadFunctional_apply, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hNrep u] with x hx
  rw [hx]
  exact mul_comm _ _

/-- A represented Nemytskii map turns the integral weak equation into the
abstract strong-dual equation used by monotonicity and variational arguments. -/
theorem isDirichletSemilinearWeakSolution_iff_nemytskii_load
    (g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (f : DerivLp n 2 Ω) (u : H¹₀(Ω)) :
    IsDirichletSemilinearWeakSolution g f u ↔
      ∀ v : H¹₀(Ω),
        dirichletForm (n := n) (Ω := Ω) u v +
            loadFunctional (n := n) (Ω := Ω) (N u) v =
          loadFunctional (n := n) (Ω := Ω) f v := by
  constructor
  · intro hu v
    rw [dirichletNemytskii_pairing_eq_integral
      (n := n) (Ω := Ω) g N hNrep u v]
    exact hu.equation v
  · intro hu
    constructor
    · exact integrable_dirichletNemytskiiIntegrand
        (n := n) (Ω := Ω) g N hNrep u
    · intro v
      rw [← dirichletNemytskii_pairing_eq_integral
        (n := n) (Ω := Ω) g N hNrep u v]
      exact hu v

end SobolevSpace.GraphSpace
