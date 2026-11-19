/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Semilinear.DirichletNemytskii
import PDE.CalculusOfVariations.IntegralEnergy
import PDE.Elliptic.Semilinear.Variational

/-!
# Variational semilinear Dirichlet equations

We specialize the direct method to a semilinear Dirichlet energy
on `H¹₀(Ω)`. For a scalar potential `G(x,s)`, the nonlinear part is

`Phi(u) = ∫_Ω G(x,u(x)) dx`.

The hypotheses record the analytic input needed at this level: integrability,
pointwise convexity, and a Fréchet derivative represented by an `L²`
Nemytskii map. Differentiability and convexity automatically provide the
affine lower bound used by the direct method. No contraction or smallness
assumption is used.

## Main results

* `dirichletIntegralPotential`: the functional `Phi(u) = ∫_Ω G(x, u(x)) dx` on `H¹₀(Ω)`.
* `convexOn_dirichletIntegralPotential`: pointwise convexity of `G(x, ·)` for a.e. `x` gives
  convexity of `Phi`, provided the integrands are integrable.
* `existsUnique_dirichlet_semilinear_of_variational`: on a bounded domain with `0 < n`, the
  weak problem `-Δu + g(x, u) = f` has exactly one solution in `H¹₀(Ω)` whenever `Phi` is
  Fréchet differentiable with derivative represented by the `L²` Nemytskii map of `g`.

## Implementation notes

The Nemytskii map `N` and the identity `N u = g(·, u)` a.e. are hypotheses, as is the Fréchet
derivative `DPhi u = ⟪N u, ·⟫`; their derivation from growth conditions on `G` depends on the
dimension and the Sobolev embedding. The theorems pass from these facts, via convexity of the
energy, to existence and uniqueness.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.2, Theorems 2 and 3 (existence and uniqueness of
  minimizers), and §8.2.3, Theorem 4 (Solution of Euler-Lagrange equation).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The integral potential induced on `H¹₀(Ω)` by a scalar density
`G : Ω × ℝ → ℝ`. -/
noncomputable def dirichletIntegralPotential
    (G : ℝ^n → ℝ → ℝ)
    (u : H¹₀(Ω)) : ℝ :=
  ∫ x, G x
      ((baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) x)
    ∂domainMeasure n Ω

/-- Pointwise convexity of an integrable density gives convexity of its
integral functional on `H¹₀(Ω)`. -/
theorem convexOn_dirichletIntegralPotential
    (G : ℝ^n → ℝ → ℝ)
    (hGint : ∀ u : H¹₀(Ω),
      Integrable
        (fun x ↦ G x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
        (domainMeasure n Ω))
    (hGconvex : ∀ᵐ x ∂domainMeasure n Ω,
      ConvexOn ℝ Set.univ (G x)) :
    ConvexOn ℝ Set.univ
      (dirichletIntegralPotential (n := n) (Ω := Ω) G) := by
  exact PDE.CalculusOfVariations.convexOn_integral_Lp_comp
    (baseCoordCLM (n := n) (Ω := Ω)).toLinearMap hGconvex hGint

/-- A nonnegative density induces a nonnegative integral potential. -/
theorem dirichletIntegralPotential_nonneg
    (G : ℝ^n → ℝ → ℝ)
    (hGnonneg : ∀ᵐ x ∂domainMeasure n Ω, ∀ s, 0 ≤ G x s)
    (u : H¹₀(Ω)) :
    0 ≤ dirichletIntegralPotential
      (n := n) (Ω := Ω) G u := by
  apply integral_nonneg_of_ae
  filter_upwards [hGnonneg] with x hx
  exact hx _

/-- The direct method produces the unique `H¹₀(Ω)` weak solution of

`-Δu + g(x,u) = f`

from an integrable convex potential whose Fréchet derivative is represented
by the `L²` Nemytskii map `N`. Convexity of the energy supplies uniqueness
directly; no separate monotonicity or Lipschitz assumption is needed. -/
theorem existsUnique_dirichlet_semilinear_of_variational
    (hn : 0 < n)
    (hΩbounded : Bornology.IsBounded Ω)
    (G g : ℝ^n → ℝ → ℝ)
    (N : H¹₀(Ω) → DerivLp n 2 Ω)
    (hGint : ∀ u : H¹₀(Ω),
      Integrable
        (fun x ↦ G x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
        (domainMeasure n Ω))
    (hGconvex : ∀ᵐ x ∂domainMeasure n Ω,
      ConvexOn ℝ Set.univ (G x))
    (hNrep : ∀ u : H¹₀(Ω),
      ((N u : DerivLp n 2 Ω) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ g x
          ((baseCoordCLM (n := n) (Ω := Ω) u :
              ℝ^n → ℝ) x))
    (hNemytskiiDerivative : ∀ u : H¹₀(Ω),
      HasFDerivAt
        (dirichletIntegralPotential (n := n) (Ω := Ω) G)
        (loadFunctional (n := n) (Ω := Ω) (N u)) u)
    (f : DerivLp n 2 Ω) :
    ∃! u : H¹₀(Ω),
      IsDirichletSemilinearWeakSolution g f u := by
  rcases dirichletForm_isCoercive
      (n := n) (Ω := Ω) hn hΩbounded with
    ⟨c, hc, hcoercive⟩
  have hPhiConvex :
      ConvexOn ℝ Set.univ
        (dirichletIntegralPotential (n := n) (Ω := Ω) G) :=
    convexOn_dirichletIntegralPotential
      (n := n) (Ω := Ω) G hGint hGconvex
  obtain ⟨u, hu, huUnique⟩ :=
    @PDE.Elliptic.Semilinear.existsUnique_variational_weak_solution
      (H¹₀(Ω))
      inferInstance
      inferInstance
      inferInstance
      (dirichletForm (n := n) (Ω := Ω))
      (dirichletForm_symm (n := n) (Ω := Ω))
      c hc hcoercive
      (dirichletIntegralPotential (n := n) (Ω := Ω) G)
      hPhiConvex
      (fun w ↦ loadFunctional (n := n) (Ω := Ω) (N w))
      hNemytskiiDerivative
      (loadFunctional (n := n) (Ω := Ω) f)
  refine ⟨u, ?_, fun w hw ↦ huUnique w ?_⟩
  · exact
      (isDirichletSemilinearWeakSolution_iff_nemytskii_load
        (n := n) (Ω := Ω) g N hNrep f u).mpr hu
  · exact
      (isDirichletSemilinearWeakSolution_iff_nemytskii_load
        (n := n) (Ω := Ω) g N hNrep f w).mp hw

end SobolevSpace.GraphSpace
