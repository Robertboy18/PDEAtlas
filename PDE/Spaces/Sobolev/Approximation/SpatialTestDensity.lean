/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.H1Operator
public import PDE.Spaces.Sobolev.Approximation.Density.Global
public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert

/-!
# Strong H¹ approximation of spatial tests

The whole-space Sobolev density theorem supplies smooth compactly supported
approximations in each component of a finite product. Mollification also converges in
H¹: its base row converges in L², and the derivative-kernel identity reduces each first
weak derivative to the same L² convergence theorem.

These two approximations have different uses in weak formulations. Compactly supported
smooth tests enter the distribution identity; mollified H¹ tests allow measurability to
be recovered from the mollified transport operators.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology Distributions Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

open scoped SobolevSpace.WholeSpaceHilbert

variable {n : ℕ}

/-- Mollifying the base coordinate of an H¹ function converges in the full H¹
norm. The derivative rows are controlled by their own L² approximate identities. -/
theorem tendsto_mollifierH1CLM_base (μ : Mollifier n) (ε : ℕ → ℝ)
    (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0)) (U : W^{1,2}(ℝ^n)) :
    Tendsto (fun k ↦ mollifierH1CLM μ (hε k) (wkpCoordinateCLM (baseIndex n 1) U))
      atTop (𝓝 U) := by
  have hrow (v : DerivLp n 2 univ) :
      Tendsto (fun k ↦ mollifierRowCLM μ (hε k) v) atTop (𝓝 v) := by
    have h := (wholeSpaceL2Equiv (n := n)).symm.continuous.continuousAt.tendsto.comp
      (tendsto_mollifierL2CLM μ ε hε hε0 (wholeSpaceL2Equiv v))
    change Tendsto
      (fun k ↦ wholeSpaceL2Equiv.symm
        (mollifierL2CLM μ (hε k) (wholeSpaceL2Equiv v)))
      atTop (𝓝 (wholeSpaceL2Equiv.symm (wholeSpaceL2Equiv v))) at h
    simpa only [mollifierRowCLM, ContinuousLinearMap.comp_apply,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometryEquiv.symm_apply_apply] using h
  apply tendsto_subtype_rng.mpr
  let e := PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : DerivIndex n 1 ↦ DerivLp n 2 univ)
  have hcoords : Tendsto
      (fun k a ↦ wkpCoordinateCLM a
        (mollifierH1CLM μ (hε k) (wkpCoordinateCLM (baseIndex n 1) U)))
      atTop (𝓝 (fun a ↦ wkpCoordinateCLM a U)) := by
    apply tendsto_pi_nhds.mpr
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with ha | ⟨j, ha⟩
    · subst a
      simpa only [mollifierH1CLM_base] using hrow (wkpCoordinateCLM (baseIndex n 1) U)
    · subst a
      simpa only [mollifierH1CLM_derivative, mollifierDerivativeRowCLM_base] using
        hrow (wkpCoordinateCLM (singleDerivIndex n j) U)
  exact e.symm.continuous.continuousAt.tendsto.comp hcoords

/-- Smooth compactly supported functions are dense in every finite product of the
whole-space H¹ graph space. The approximation uses the canonical smooth Sobolev
constructor, so its coordinates are the classical derivatives. -/
theorem exists_testFunctionProduct_tendsto_H1
    {ι : Type*} [Finite ι] (U : PiLp 2 (fun _ : ι ↦ W^{1,2}(ℝ^n))) :
    ∃ φ : ℕ → ι → 𝓓((⊤ : Opens (ℝ^n)), ℝ),
      Tendsto (fun k ↦ WithLp.toLp 2 (fun p ↦
        globalTestFunctionToWkpOn (n := n) (k := 1) (p := 2) (Ω := univ) (φ k p)))
        atTop (𝓝 U) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have happrox (p : ι) := globalApproximation_WkpSpace
    (p := 2) (standardMollifier n) (by norm_num) 1 (U p)
  choose f hf hcs hconv using happrox
  let φ (k : ℕ) (p : ι) : 𝓓((⊤ : Opens (ℝ^n)), ℝ) :=
    ⟨f p k, hf p k, hcs p k, subset_univ _⟩
  refine ⟨φ, ?_⟩
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ W^{1,2}(ℝ^n))
  have hcoords : Tendsto
      (fun k p ↦ globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (φ k p))
      atTop (𝓝 (fun p ↦ U p)) := by
    apply tendsto_pi_nhds.mpr
    intro p
    have hsub : Tendsto
        (fun k ↦ globalTestFunctionToWkpOn (k := 1) (p := 2) (Ω := univ) (φ k p) - U p)
        atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (hconv p)
    simpa only [sub_add_cancel, zero_add] using hsub.add_const (U p)
  exact e.symm.continuous.continuousAt.tendsto.comp hcoords

end SobolevSpace.Approximation
