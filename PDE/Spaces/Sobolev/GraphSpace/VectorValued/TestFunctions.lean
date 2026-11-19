/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation
import PDE.Spaces.Sobolev.Calculus.Differentiation.ClassicalHigherOrder

/-!
# Vector multiples of test functions in Sobolev spaces

A real test function multiplied by any vector in a Banach space defines a Sobolev
bundle of every finite order and every exponent, including infinity. Its coordinates are
the classical scalar derivatives multiplied by that vector. Compact support supplies all
`Lp` membership proofs, even on an unbounded domain.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem testFunction_derivative_memLp (φ : 𝓓(Ω, ℝ)) (v : F)
    (a : DerivIndex n k) :
    MemLp (fun x ↦ iteratedPartialDeriv a.toList φ.toFun x • v) p
      (domainMeasure n Ω) :=
  (ContinuousLinearMap.toSpanSingleton ℝ v).comp_memLp'
    ((iteratedPartialDerivTest a.toList φ).contDiff.continuous.memLp_of_hasCompactSupport
      (iteratedPartialDerivTest a.toList φ).hasCompactSupport)

private theorem testFunction_derivative_weak (φ : 𝓓(Ω, ℝ)) (v : F)
    (a : DerivIndex n k) :
    HasWeakDerivativeOn Ω a.toList (fun x ↦ φ x • v)
      (fun x ↦ iteratedPartialDeriv a.toList φ.toFun x • v) :=
  (hasWeakDerivativeOn_real_iff.mpr
    (hasWeakDerivativeOn_iteratedPartialDeriv_of_contDiffOn Ω.isOpen
      (φ.contDiff.of_le (by simp)).contDiffOn a.toList a.toList_length_le)).map
    (ContinuousLinearMap.toSpanSingleton ℝ v)

/-- A real test function multiplied by a fixed vector gives a Sobolev bundle, with no
additional integrability assumptions on the domain. -/
def ofTestFunction (φ : 𝓓(Ω, ℝ)) (v : F) : W^{k,p}(Ω; F) :=
  ofWeakDerivatives (fun a x ↦ iteratedPartialDeriv a.toList φ.toFun x • v)
    (fun a ↦ by exact testFunction_derivative_memLp φ v a) (fun a ↦ by
      simpa only [baseIndex_toList, iteratedPartialDeriv, TestFunction.toFun_eq_coe] using
        testFunction_derivative_weak φ v a)

/-- Each derivative coordinate of the test-function bundle has its classical representative. -/
theorem ofTestFunction_apply_ae (φ : 𝓓(Ω, ℝ)) (v : F) (a : DerivIndex n k) :
    ((ofTestFunction (p := p) φ v).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      fun x ↦ iteratedPartialDeriv a.toList φ.toFun x • v :=
  ofWeakDerivatives_apply_ae _ _ _ _

/-- The base coordinate represents the original vector multiple of the test function. -/
theorem ofTestFunction_base_ae (φ : 𝓓(Ω, ℝ)) (v : F) :
    ((ofTestFunction (k := k) (p := p) φ v).val (baseIndex n k) : ℝ^n → F)
      =ᵐ[domainMeasure n Ω] fun x ↦ φ x • v := by
  simpa only [baseIndex_toList, iteratedPartialDeriv, TestFunction.toFun_eq_coe] using
    ofTestFunction_apply_ae (p := p) φ v (baseIndex n k)

end SobolevSpace.VectorValued
