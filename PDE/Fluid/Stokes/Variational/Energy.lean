/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Divergence.ZeroBoundary
public import PDE.Analysis.Variational.QuadraticEnergy.Stationarity

/-!
# The constrained Stokes energy and its first variation

For viscosity one, the steady Stokes energy is
`½ ‖∇u‖² - ⟪f, u⟫`. Its Dirichlet term includes every entry of the weak
matrix gradient. The L² force defines a continuous load on H¹₀. Evans (§8.4.4(a)) considers the
same energy `I[w]` over divergence-free fields in `H¹₀(U; ℝ³)`, for `U ⊂ ℝ³` bounded and simply
connected.

Incompressibility is a linear constraint, so a minimum among divergence-free
fields is stationary in every divergence-free direction. This gives the weak
Stokes equation before introducing pressure. `Variational.Existence` constructs
the unique minimizer on bounded domains in positive dimension; the pressure modules recover
`∇p = Δu + f` under their stated domain assumptions.

The pointwise spacetime operator `IncompressibleFlow.stokesMomentumResidual`
in `PDE.Fluid.Incompressible.ModelHierarchy` is `∂ₜu + ∇p - νΔu - f`.
For smooth time-independent fields at `ν = 1`, its zero equation is
`∇p = Δu + f`. Here `Variational.Residual` defines `Δu + f` distributionally
from the H¹₀ field. The pressure theorem
`exists_pressure_distribution_of_minimizes_energy` reconstructs a locally L² pressure
on arbitrary open domains in positive dimension. Its gradient identity is
distributional.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.4(a), p. 497.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace IncompressibleFlow.Stokes

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal RealInnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The full matrix Dirichlet energy with its signed L² load. -/
def energy (f : Lp (ℝ^n) 2 (domainMeasure n Ω))
    (u : H¹₀(Ω; ℝ^n)) : ℝ :=
  1 / 2 * ‖∇ u‖ ^ 2 - ⟪f, toLp u⟫

/-- The energy is the integral of the squared matrix gradient minus the
force pairing. Both terms are integrable. -/
theorem energy_eq_integral (f : Lp (ℝ^n) 2 (domainMeasure n Ω))
    (u : H¹₀(Ω; ℝ^n)) :
    energy f u = ∫ x, (1 / 2 * ‖∇ u x‖ ^ 2 -
      ⟪f x, toLp u x⟫) ∂domainMeasure n Ω := by
  rw [energy, Lp.norm_sq_eq_integral_norm_sq, L2.inner_def,
    integral_sub ((Lp.memLp (∇ u)).norm.integrable_sq.const_mul _)
      (L2.integrable_inner f (toLp u)), integral_const_mul]

/-- An energy minimizer satisfies the weak Stokes equation in every
divergence-free direction. -/
theorem stationary_of_minimizes_energy
    (f : Lp (ℝ^n) 2 (domainMeasure n Ω)) (u : H¹₀(Ω; ℝ^n))
    (hu : ∇· u = 0)
    (hmin : ∀ w : H¹₀(Ω; ℝ^n), ∇· w = 0 →
      energy f u ≤ energy f w)
    (v : H¹₀(Ω; ℝ^n)) (hv : ∇· v = 0) :
    ⟪∇ u, ∇ v⟫ =
      ⟪f, toLp v⟫ := by
  let B := (innerSL ℝ).bilinearComp
    (gradient (n := n) (m := n) (Ω := Ω)) gradient
  let ell := (innerSL ℝ f).comp toLp
  have hB (a b : H¹₀(Ω; ℝ^n)) : B a b = B b a := by
    simp only [B, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
    exact real_inner_comm _ _
  have henergy (a : H¹₀(Ω; ℝ^n)) :
      PDE.Analysis.Variational.energy B ell a = energy f a := by
    simp only [PDE.Analysis.Variational.energy, B, ell,
      ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply, real_inner_self_eq_norm_sq, energy]
  exact PDE.Analysis.Variational.stationary_of_energy_minimizes_line B ell hB u v
    (fun t ↦ by
      simp only [henergy]
      apply hmin
      simp only [map_add, map_smul, hu, hv, smul_zero, add_zero])

end IncompressibleFlow.Stokes
