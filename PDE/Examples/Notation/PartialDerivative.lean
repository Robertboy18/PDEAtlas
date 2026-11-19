/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Operator.Notation
public import PDE.DistributionTheory.Schwartz.PartialDerivative
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Derivatives

/-!
# Partial-derivative notation across function spaces

The same `∂[i]` notation differentiates ordinary functions, Schwartz functions,
Sobolev functions, and distributions. These examples show repeated derivatives,
the Sobolev norm estimate, and the distributional integration-by-parts sign.
-/

@[expose] public noncomputable section

open PDE TopologicalSpace
open scoped Distributions ENNReal SchwartzMap Sobolev

namespace PDE.Examples.PartialDerivativeNotation

section Classical

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (u : ℝ^n → F) (i j : Fin n) (x : ℝ^n)

example : ∂[i] u x = partialDeriv i u x := rfl

example : ∂[i] ∂[j] u x = partialDeriv i (partialDeriv j u) x := rfl

end Classical

section Schwartz

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (φ : 𝓢(ℝ^n, F)) (i j : Fin n) (x : ℝ^n)

/-- Application selects the bundled Schwartz derivative before evaluating at a point. -/
theorem schwartz_partialDeriv_apply :
    ∂[i] φ x = partialDeriv i (φ : ℝ^n → F) x :=
  congrFun (SchwartzMap.coe_partialDeriv i φ) x

/-- Iterated bundled derivatives can be moved across the function coercion. -/
theorem schwartz_mixed_coe :
    ⇑(∂[i] ∂[j] φ) = ∂[i] ∂[j] (φ : ℝ^n → F) := by
  simp only [SchwartzMap.coe_partialDeriv]

end Schwartz

section Sobolev

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set ℝ^n} (i j : Fin n)

/-- Resolving nested weak derivatives retains their lower-order Sobolev norms. -/
theorem sobolev_mixed_norm_le (u : W^{k + 2,p}(Ω)) :
    ‖(∂[i] ∂[j] u : W^{k,p}(Ω))‖ ≤ ‖u‖ :=
  (SobolevSpace.GraphSpace.norm_partialDeriv_le i (∂[j] u)).trans
    (SobolevSpace.GraphSpace.norm_partialDeriv_le j u)

/-- The notation preserves the continuous linear map needed by continuity automation. -/
example : Continuous (fun u : W^{k + 1,p}(Ω) ↦ (∂[i] u : W^{k,p}(Ω))) := by
  fun_prop

end Sobolev

section VectorSobolev

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (i j : Fin n)

example : Continuous (fun u : W^{k + 1,p}(Ω; F) ↦ (∂[i] u : W^{k,p}(Ω; F))) := by
  fun_prop

/-- Mixed weak derivatives still commute when nested without parentheses. -/
example (u : W^{k + 2,p}(Ω; F)) :
    (∂[i] ∂[j] u : W^{k,p}(Ω; F)) = ∂[j] ∂[i] u :=
  SobolevSpace.VectorValued.partialDeriv_commute i j u

end VectorSobolev

section Distributions

variable {n : ℕ} {Ω : Opens ℝ^n} (T : 𝓓'(Ω, ℝ)) (φ : 𝓓(Ω, ℝ))
  (i j : Fin n)

/-- The distributional derivative retains the integration-by-parts sign. -/
example :
    ∂[i] T φ = -T (TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i 1) φ) :=
  Distribution.lineDerivCLM_apply

example : Continuous (fun T : 𝓓'(Ω, ℝ) ↦ ∂[i] T) :=
  (Distribution.lineDerivCLM (EuclideanSpace.single i 1)).continuous

end Distributions

end PDE.Examples.PartialDerivativeNotation
