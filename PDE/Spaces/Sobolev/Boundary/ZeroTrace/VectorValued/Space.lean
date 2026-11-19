/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.TestFunctions
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Topology

/-!
# Banach-valued Sobolev spaces with zero boundary values

`W₀^{k,p}(Ω; F)` is the closure of `𝓓(Ω, F)` in the Sobolev graph norm.
This definition makes sense on every open set, before choosing a boundary trace.
The domain may be unbounded or have an irregular boundary, and the codomain may be
infinite dimensional.

The closed-subspace construction supplies completeness for `1 ≤ p ≤ ∞`.
It also gives the approximation principle used to pass boundary identities from test
functions to the whole space. On C¹ domains `ZeroTrace.VectorValued.Trace.C1Converse`
characterizes it as a trace kernel.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The closure of compactly supported smooth Banach-valued functions in the Sobolev norm. -/
def wkp0SubmoduleOn : ClosedSubmodule ℝ (W^{k,p}(Ω; F)) :=
  Submodule.closure (LinearMap.range (testFunctionToWkpLinear (k := k) (p := p)))

/-- The Sobolev space with zero boundary values, defined by supported smooth approximation. -/
abbrev Wkp0SpaceOn (n k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (Ω : Opens ℝ^n)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :=
  (wkp0SubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω) (F := F)).toSubmodule

/-- Banach-valued Sobolev functions with zero boundary values. -/
scoped[Sobolev] notation "W₀^{" k "," p "}(" Ω "; " F ")" =>
  SobolevSpace.VectorValued.Wkp0SpaceOn _ k p Ω F

/-- Every test function belongs to the supported smooth closure. -/
theorem testFunctionToWkp_mem_Wkp0 (φ : 𝓓(Ω, F)) :
    testFunctionToWkp (k := k) (p := p) φ ∈
      (wkp0SubmoduleOn (k := k) (p := p) (Ω := Ω) (F := F)).toSubmodule :=
  subset_closure ⟨φ, rfl⟩

/-- The canonical test-function inclusion into the space with zero boundary values. -/
def testFunctionToWkp0 (φ : 𝓓(Ω, F)) : W₀^{k,p}(Ω; F) :=
  ⟨testFunctionToWkp φ, testFunctionToWkp_mem_Wkp0 φ⟩

/-- Forgetting the boundary constraint recovers the same Sobolev graph element. -/
@[simp] theorem testFunctionToWkp0_coe (φ : 𝓓(Ω, F)) :
    (testFunctionToWkp0 (k := k) (p := p) φ : W^{k,p}(Ω; F)) = testFunctionToWkp φ :=
  rfl

/-- Inclusion of test functions into the supported smooth closure is linear. -/
def testFunctionToWkp0Linear : 𝓓(Ω, F) →ₗ[ℝ] W₀^{k,p}(Ω; F) :=
  testFunctionToWkpLinear.codRestrict
    (wkp0SubmoduleOn (k := k) (p := p) (Ω := Ω) (F := F)).toSubmodule
    testFunctionToWkp_mem_Wkp0

/-- The linear inclusion uses the canonical test-function representative. -/
@[simp] theorem testFunctionToWkp0Linear_apply (φ : 𝓓(Ω, F)) :
    testFunctionToWkp0Linear (k := k) (p := p) φ = testFunctionToWkp0 φ :=
  rfl

/-- Test functions are dense in the space with zero boundary values. -/
theorem denseRange_testFunctionToWkp0Linear :
    DenseRange (testFunctionToWkp0Linear (k := k) (p := p) (Ω := Ω) (F := F)) := by
  rw [DenseRange, Subtype.dense_iff]
  intro U hU
  change U ∈ closure (((↑) : W₀^{k,p}(Ω; F) → W^{k,p}(Ω; F)) ''
    Set.range (testFunctionToWkp0Linear (k := k) (p := p) (Ω := Ω) (F := F)))
  have himage :
      ((↑) : W₀^{k,p}(Ω; F) → W^{k,p}(Ω; F)) ''
        Set.range (testFunctionToWkp0Linear (k := k) (p := p) (Ω := Ω) (F := F)) =
      (LinearMap.range (testFunctionToWkpLinear (k := k) (p := p) (Ω := Ω) (F := F)) :
        Set (W^{k,p}(Ω; F))) := by
    ext V
    constructor
    · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
      exact ⟨φ, rfl⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨testFunctionToWkp0 φ, ⟨φ, rfl⟩, rfl⟩
  rw [himage]
  exact hU

/-- A closed property proved on test functions extends to their Sobolev closure. -/
theorem Wkp0SpaceOn.closed_property_of_testFunctions {S : Set (W^{k,p}(Ω; F))}
    (hS : IsClosed S) (hφ : ∀ φ : 𝓓(Ω, F), testFunctionToWkp (k := k) (p := p) φ ∈ S)
    (U : W₀^{k,p}(Ω; F)) : (U : W^{k,p}(Ω; F)) ∈ S := by
  apply closure_minimal _ hS U.property
  rintro V ⟨φ, rfl⟩
  exact hφ φ

/-- A Sobolev limit of test functions has zero boundary values in the closure sense. -/
theorem mem_Wkp0_of_tendsto_testFunctionToWkp (U : W^{k,p}(Ω; F))
    (φ : ℕ → 𝓓(Ω, F))
    (hφ : Tendsto (fun j ↦ testFunctionToWkp (k := k) (p := p) (φ j)) atTop (𝓝 U)) :
    U ∈ (wkp0SubmoduleOn (k := k) (p := p) (Ω := Ω) (F := F)).toSubmodule :=
  (wkp0SubmoduleOn (k := k) (p := p) (Ω := Ω) (F := F)).isClosed'.mem_of_tendsto hφ
    (Eventually.of_forall fun j ↦ testFunctionToWkp_mem_Wkp0 (φ j))

/-- The space with zero boundary values is complete at every exponent at least one. -/
instance : CompleteSpace (W₀^{k,p}(Ω; F)) :=
  (wkp0SubmoduleOn (k := k) (p := p) (Ω := Ω) (F := F)).isClosed'.completeSpace_coe

end SobolevSpace.VectorValued
