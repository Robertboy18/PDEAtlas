/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Profiles
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.Weak
import Mathlib.Analysis.Convex.Deriv
import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Shock
import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.ConvexShock

/-!
# Entropy inequality for Burgers shocks

A compressive Burgers shock (`uR < uL`, propagating at the Rankine–Hugoniot speed
`s = (uL + uR)/2`) satisfies the entropy inequality `∂ₜ η(u) + ∂ₓ q(u) ≤ 0` for every entropy
pair `(η, q)` with `η` convex. Because the profile is a planar shock, its weak entropy integral
reduces to the coefficient

`(q(uL) - q(uR)) - (η(uL) - η(uR)) · s`

times the nonnegative trace of the test function on the shock line. The general
convex-flux theorem proves this coefficient is nonnegative using monotonicity
of the flux and entropy derivatives. Here `f'(v) = v`, so convexity follows directly from the
identity derivative.

The last two theorems transfer the conclusion to the unified `riemannSolution` on the decreasing
branch, where it coincides with the shock profile.

## Main results

* `shockProfile_isEntropyWeakSolution`: for `uR < uL`, the Burgers shock is an entropy weak
  solution on all of spacetime.
* `riemannSolution_isWeakSolution_of_lt`, `riemannSolution_isEntropyWeakSolution_of_lt`: the
  same statements for the decreasing-data Riemann solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.4.1, equation (17); §3.4.4, Theorem 4(i),
  equations (54)-(55); §11.4.3, equations (36)-(38).
  <https://doi.org/10.1090/gsm/019>
* P. D. Lax, *Hyperbolic Systems of Conservation Laws and the Mathematical Theory of Shock Waves*,
  Society for Industrial and Applied Mathematics, 1973, for entropy/entropy-flux pairs and the
  entropy inequality across a shock.
  <https://doi.org/10.1137/1.9781611970562>
-/

@[expose] public section

namespace BurgersEquation.Riemann

noncomputable section

open TopologicalSpace

open PDE.Hyperbolic.ConservationLaw.Scalar
open PDE.Common

/-- A compressive Burgers shock satisfies every convex entropy inequality.

The weak entropy production is the product of the entropy jump coefficient and the
nonnegative trace of the test function on the shock interface. -/
theorem shockProfile_isEntropyWeakSolution {uL uR : ℝ} (hLR : uR < uL) :
    _root_.PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropyWeakSolution flux (⊤ : Opens ℝ^2)
      (shockProfile uL uR) := by
  have hreg : ContDiff ℝ 1 flux := by unfold flux; fun_prop
  have hconvex : ConvexOn ℝ (Set.Icc uR uL) flux := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc uR uL) hreg.continuous.continuousOn
      hreg.differentiable_one.differentiableOn
    intro x _ y _ hxy
    simpa only [deriv_flux] using hxy
  rw [shockProfile_eq_planarShock]
  exact (rankineHugoniot_shockSpeed uL uR).isEntropyWeakSolution_planarShock_of_convex
    hLR.le hconvex hreg

/-- The decreasing-data Riemann solution is a weak Burgers solution on spacetime. -/
theorem riemannSolution_isWeakSolution_of_lt {uL uR : ℝ} (h : uR < uL) :
    PDE.Hyperbolic.ConservationLaw.Scalar.IsWeakSolution
      flux (⊤ : Opens ℝ^2) (riemannSolution uL uR) := by
  simpa [riemannSolution_of_lt (uL := uL) (uR := uR) h] using
    (shockProfile_isWeakSolution (uL := uL) (uR := uR))

/-- The decreasing-data Riemann solution satisfies every convex entropy inequality. -/
theorem riemannSolution_isEntropyWeakSolution_of_lt {uL uR : ℝ} (h : uR < uL) :
    _root_.PDE.Hyperbolic.ConservationLaw.Scalar.IsEntropyWeakSolution flux (⊤ : Opens ℝ^2)
      (riemannSolution uL uR) := by
  simpa [riemannSolution_of_lt (uL := uL) (uR := uR) h] using
    (shockProfile_isEntropyWeakSolution (uL := uL) (uR := uR) h)

end

end BurgersEquation.Riemann
