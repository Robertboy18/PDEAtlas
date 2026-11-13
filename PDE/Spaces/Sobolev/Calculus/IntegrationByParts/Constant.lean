/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.DomainCore
public import PDE.Spaces.Sobolev.Calculus.Product.FirstOrder

/-!
# Constant fluxes against zero-boundary tests

Each derivative of an `H¹₀` field pairs to zero with a constant.
This is the integration-by-parts fact that permits an arbitrary affine
part in a gradient density: its constant flux contributes nothing to
the weak Dirichlet equation.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal RealInnerProductSpace Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)} [IsFiniteMeasure (domainMeasure n Ω)]

/-- Constant `L²` fields annihilate every derivative of an `H¹₀` test. -/
theorem inner_constant_derivCoordCLM_eq_zero
    (c : ℝ) (q : DerivLp n 2 Ω)
    (hq : (q : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun _ ↦ c)
    (i : Fin n) (v : H¹₀(Ω)) :
    ⟪q, derivCoordCLM i v⟫ = 0 := by
  let U := wkpConstant (n := n) (p := 2) (Ω := Ω) c
  have hU : U.val (baseIndex n 1) = q :=
    Lp.ext ((wkpConstant_base_ae c).trans hq.symm)
  have hD : U.val (singleDerivIndex n i) = 0 := by
    apply Lp.ext
    exact (wkpConstant_deriv_ae c i).trans (Lp.coeFn_zero _ _ _).symm
  have hweak := U.property (singleDerivIndex n i)
  simp only [singleDerivIndex_toList, hU, hD] at hweak
  simpa using weakDerivative_integrationByParts_H10 i q 0 hweak v

end SobolevSpace.GraphSpace
