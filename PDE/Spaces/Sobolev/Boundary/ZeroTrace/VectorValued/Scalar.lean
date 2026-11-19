/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Space
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Scalar

/-!
# Scalar compatibility of the supported Sobolev closure

At real codomain the test functions are the same compactly supported smooth functions
as the scalar supported test functions. The scalar graph isometry identifies their images
and therefore their closures. Restricting that isometry identifies the two zero-boundary
spaces without changing any derivative coordinate or its norm.

This holds on every open domain, in every finite order and dimension, for all `1 ≤ p`,
including infinity.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued

variable {n k : ℕ} {p : ℝ≥0∞} {Ω : Opens ℝ^n}

/-- A test function on an open domain is exactly a whole-space test function whose
topological support lies in that domain. -/
def scalarTestFunctionEquiv :
    𝓓(Ω, ℝ) ≃ₗ[ℝ] GraphSpace.TestFunctionOn n Ω where
  toFun φ :=
    ⟨⟨φ, φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩, φ.tsupport_subset⟩
  invFun φ := ⟨φ.1, φ.1.contDiff, φ.1.hasCompactSupport, φ.property⟩
  left_inv φ := by ext; rfl
  right_inv φ := by apply Subtype.ext; ext; rfl
  map_add' φ ψ := by apply Subtype.ext; ext; rfl
  map_smul' c φ := by apply Subtype.ext; ext; rfl

/-- The test-function identification leaves the ambient function unchanged. -/
theorem scalarTestFunctionEquiv_toFun (φ : 𝓓(Ω, ℝ)) :
    (scalarTestFunctionEquiv φ).1.toFun = φ.toFun :=
  rfl

variable [Fact (1 ≤ p)]

/-- The Banach-valued and scalar inclusions of a supported smooth function agree under the
isometry of their Sobolev graphs. -/
theorem scalarEquiv_testFunctionToWkp (φ : 𝓓(Ω, ℝ)) :
    scalarEquiv (testFunctionToWkp (k := k) (p := p) φ) =
      GraphSpace.testFunctionToWkp (scalarTestFunctionEquiv φ) := by
  apply scalarEquiv.symm.injective
  apply WkpSpaceOn.ext_of_base_ae
  refine (testFunctionToWkp_base_ae (k := k) (p := p) φ).trans ?_
  symm
  have h := GraphSpace.testFunctionToWkp_coordinate_ae (k := k) (p := p)
    (scalarTestFunctionEquiv φ) (GraphSpace.baseIndex n k)
  simp only [GraphSpace.baseIndex_toList, iteratedPartialDeriv,
    scalarTestFunctionEquiv_toFun] at h
  simpa only [scalarEquiv_symm_coordinate, TestFunction.toFun_eq_coe] using h

private theorem range_testFunctionToWkpLinear_map_scalarEquiv :
    (LinearMap.range (testFunctionToWkpLinear (n := n) (k := k) (p := p)
      (Ω := Ω) (F := ℝ))).map scalarEquiv.toContinuousLinearEquiv.toLinearMap =
      LinearMap.range (GraphSpace.testFunctionToWkpLinear (n := n) (k := k)
        (p := p) (Ω := Ω)) := by
  ext u
  constructor
  · rintro ⟨v, ⟨φ, rfl⟩, rfl⟩
    exact ⟨scalarTestFunctionEquiv φ, (scalarEquiv_testFunctionToWkp φ).symm⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨testFunctionToWkp (scalarTestFunctionEquiv.symm φ),
      ⟨scalarTestFunctionEquiv.symm φ, rfl⟩, ?_⟩
    change scalarEquiv (testFunctionToWkp (scalarTestFunctionEquiv.symm φ)) =
      GraphSpace.testFunctionToWkp φ
    simpa only [LinearEquiv.apply_symm_apply] using
      scalarEquiv_testFunctionToWkp (k := k) (p := p) (scalarTestFunctionEquiv.symm φ)

/-- The scalar graph isometry maps the supported smooth closure onto the
scalar supported smooth closure. -/
theorem wkp0SubmoduleOn_map_scalarEquiv :
    (wkp0SubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω) (F := ℝ)).mapEquiv
        scalarEquiv.toContinuousLinearEquiv =
      GraphSpace.wkp0SubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω) := by
  rw [wkp0SubmoduleOn, ← ClosedSubmodule.closure_map_eq_mapEquiv_closure]
  rw [range_testFunctionToWkpLinear_map_scalarEquiv]
  rfl

/-- Membership in either real supported closure is equivalent under the original
Sobolev graph isometry. -/
theorem scalarEquiv_mem_wkp0_iff (u : W^{k,p}(Ω; ℝ)) :
    scalarEquiv u ∈ GraphSpace.wkp0SubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω) ↔
      u ∈ wkp0SubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω) (F := ℝ) := by
  rw [← wkp0SubmoduleOn_map_scalarEquiv]
  exact ClosedSubmodule.mem_mapEquiv_iff' _ _ _

/-- Scalar specialization of the zero-boundary Sobolev space preserves the
full derivative-coordinate norm, including its maximum convention at infinity. -/
def scalarZeroEquiv : W₀^{k,p}(Ω; ℝ) ≃ₗᵢ[ℝ] W₀^{k,p}(Ω) :=
  (LinearIsometryEquiv.submoduleMap
    (wkp0SubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω) (F := ℝ)).toSubmodule
    scalarEquiv).trans
      (LinearIsometryEquiv.ofEq _ _
        (congrArg ClosedSubmodule.toSubmodule wkp0SubmoduleOn_map_scalarEquiv))

/-- Forgetting the supported closure agrees with the scalar isometry of the ambient graph. -/
@[simp] theorem scalarZeroEquiv_coe (u : W₀^{k,p}(Ω; ℝ)) :
    (scalarZeroEquiv u : W^{k,p}(Ω)) = scalarEquiv (u : W^{k,p}(Ω; ℝ)) :=
  rfl

/-- Scalar specialization of the supported closure preserves every `Lp` derivative. -/
@[simp] theorem scalarZeroEquiv_coordinate (u : W₀^{k,p}(Ω; ℝ))
    (a : GraphSpace.DerivIndex n k) :
    (scalarZeroEquiv u : W^{k,p}(Ω)).val a = (u : W^{k,p}(Ω; ℝ)).val a :=
  rfl

end SobolevSpace.VectorValued
