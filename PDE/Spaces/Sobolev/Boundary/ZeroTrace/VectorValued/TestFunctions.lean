/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation
import PDE.Spaces.Sobolev.Approximation.VectorValued.ClassicalDerivatives

/-!
# Banach-valued test functions in Sobolev spaces

A smooth function compactly supported in the domain determines its Sobolev graph through
its classical derivatives. We use Mathlib's test functions with the Banach codomain;
finite sums of scalar functions multiplied by vectors are not required.

Compact support puts every derivative in every `Lp` space, including exponent infinity.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A Banach-valued test function, included in the Sobolev graph through its derivatives. -/
def testFunctionToWkp (φ : 𝓓(Ω, F)) : W^{k,p}(Ω; F) :=
  ofWeakDerivatives (fun a ↦ iteratedPartialDeriv a.toList (φ : ℝ^n → F))
    (fun a ↦ (PDE.contDiff_top_iteratedPartialDeriv φ.contDiff a.toList).continuous
      |>.memLp_of_hasCompactSupport (φ.hasCompactSupport.iteratedPartialDeriv a.toList))
    (fun a ↦ by
      simpa only [baseIndex_toList, iteratedPartialDeriv] using
        hasWeakDerivativeOn_iteratedPartialDeriv φ.contDiff a.toList)

/-- Each coordinate is represented by the corresponding classical derivative. -/
theorem testFunctionToWkp_coordinate_ae (φ : 𝓓(Ω, F)) (a : DerivIndex n k) :
    ((testFunctionToWkp (k := k) (p := p) φ).val a : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] iteratedPartialDeriv a.toList (φ : ℝ^n → F) :=
  ofWeakDerivatives_apply_ae _ _ _ _

/-- The base coordinate of the Sobolev inclusion represents the test function itself. -/
theorem testFunctionToWkp_base_ae (φ : 𝓓(Ω, F)) :
    ((testFunctionToWkp (k := k) (p := p) φ).val (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] (φ : ℝ^n → F) := by
  simpa only [baseIndex_toList, iteratedPartialDeriv] using
    testFunctionToWkp_coordinate_ae (k := k) (p := p) φ (baseIndex n k)

/-- Inclusion of Banach-valued test functions into the Sobolev graph is linear. -/
def testFunctionToWkpLinear : 𝓓(Ω, F) →ₗ[ℝ] W^{k,p}(Ω; F) where
  toFun := testFunctionToWkp
  map_add' φ ψ := WkpSpaceOn.ext_of_base_ae
    ((testFunctionToWkp_base_ae (φ + ψ)).trans
      ((Lp.coeFn_add _ _).trans
        ((testFunctionToWkp_base_ae φ).add (testFunctionToWkp_base_ae ψ))).symm)
  map_smul' c φ := WkpSpaceOn.ext_of_base_ae
    ((testFunctionToWkp_base_ae (c • φ)).trans
      ((Lp.coeFn_smul c _).trans
        ((testFunctionToWkp_base_ae φ).const_smul c)).symm)

/-- Applying the linear inclusion recovers the classical Sobolev constructor. -/
@[simp] theorem testFunctionToWkpLinear_apply (φ : 𝓓(Ω, F)) :
    testFunctionToWkpLinear (k := k) (p := p) φ = testFunctionToWkp φ :=
  rfl

end SobolevSpace.VectorValued
