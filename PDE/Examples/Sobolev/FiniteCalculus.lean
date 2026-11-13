/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.Finite
public import PDE.Spaces.Sobolev.Calculus.Composition.HigherOrder.FiniteWholeSpace

/-!
# Quantitative finite Sobolev calculus in three dimensions

`H²(ℝ³)` lies above the continuity threshold `2 > 3/2`, although `2 ≤ 3`. In this space a
product of three factors carrying at most two derivatives in total is in `L²`, with one
constant for all inputs, and the cubic reaction `u₀u₁ + u₂³` of three functions is again in
`H²(ℝ³)`, with a bound monotone in the three input norms.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

namespace PDE.Examples.SobolevFiniteCalculus

/-- Three factors may share at most two derivatives, with one constant for
all allocations and all inputs. -/
theorem three_factor_derivative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : Fin 3 → DerivIndex 3 2,
      (∑ i, (a i).toList.length) ≤ 2 → ∀ U : Fin 3 → W^{2,2}(ℝ^3),
      MemLp (fun x ↦ ∏ i, (U i).val (a i) x) 2 (domainMeasure 3 univ) ∧
      lpNorm (fun x ↦ ∏ i, (U i).val (a i) x) 2 (domainMeasure 3 univ) ≤
        C * ∏ i, ‖U i‖ :=
  Product.exists_constant_prod_derivatives_le (by norm_num)

/-- The cubic reaction `u₀u₁ + u₂³` of three `H²(ℝ³)` functions is represented by an
element of `H²(ℝ³)`, whose norm is bounded by a continuous function nondecreasing in each
of the three input norms. -/
theorem polynomial_composition_bound :
    ∃ Φ : (Fin 3 → ℝ) → ℝ, Continuous Φ ∧ Monotone Φ ∧
      ∀ U : Fin 3 → W^{2,2}(ℝ^3), ∃ W : W^{2,2}(ℝ^3),
        baseRepresentative W =ᵐ[volume] (fun x ↦
          baseRepresentative (U 0) x * baseRepresentative (U 1) x +
            baseRepresentative (U 2) x ^ 3) ∧
        ‖W‖ ≤ Φ (fun i ↦ ‖U i‖) :=
  Composition.exists_finite_composition_bound (by norm_num)
    (f := fun t : Fin 3 → ℝ ↦ t 0 * t 1 + t 2 ^ 3) (by fun_prop) (by simp)

end PDE.Examples.SobolevFiniteCalculus
