/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Space
import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.WholeSpace.CompactSupport

/-!
# Zero boundary values on the whole space

At finite exponents, compact smooth approximation puts every whole-space first-order
Sobolev function in the supported smooth closure. There is no physical boundary on which
to impose a condition.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- At finite exponents, every whole-space first-order Sobolev function lies in the
closure of compactly supported smooth functions. -/
theorem wkpSpace_mem_Wkp0_univ (hp : p ≠ ∞) (U : W^{1,p}(ℝ^n; F)) :
    U ∈ (wkp0SubmoduleOn (k := 1) (p := p) (Ω := ⊤) (F := F)).toSubmodule := by
  apply closure_minimal _ (wkp0SubmoduleOn (k := 1) (p := p) (Ω := ⊤)
    (F := F)).isClosed' (dense_compact_smooth_univ hp U)
  rintro V ⟨f, hf, hfc, hV⟩
  let φ : 𝓓((⊤ : Opens ℝ^n), F) := ⟨f, hf, hfc, subset_univ _⟩
  have heq : V = testFunctionToWkp (k := 1) (p := p) φ := by
    apply WkpSpaceOn.ext_of_base_ae
    have hφ := testFunctionToWkp_base_ae (k := 1) (p := p) φ
    simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ, φ,
      TestFunction.coe_mk] at hφ ⊢
    exact hV.trans hφ.symm
  rw [heq]
  exact testFunctionToWkp_mem_Wkp0 φ

/-- The supported smooth closure is the entire whole-space first-order Sobolev graph
when the exponent is finite. -/
theorem wkp0SubmoduleOn_eq_top_univ (hp : p ≠ ∞) :
    (wkp0SubmoduleOn (n := n) (k := 1) (p := p) (Ω := ⊤) (F := F)).toSubmodule = ⊤ := by
  ext U
  exact iff_true_intro (wkpSpace_mem_Wkp0_univ hp U)

end SobolevSpace.VectorValued
