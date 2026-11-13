/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.ZeroTrace.HalfSpaceCutoff
public import PDE.Spaces.Sobolev.Approximation.VectorValued.ZeroTrace.HalfSpaceMollification

/-!
# Interior approximation of a Banach-valued Sobolev zero extension

A whole-space first-order Sobolev function vanishing almost everywhere below the boundary
restricts to the supported-smooth closure `W₀^{1,p}` on the upper half-space.

At scale `ε`, shift the standard radius-two mollification upward by `3 * ε`. Its positive
boundary gap permits compact cutoffs supported inside the domain. These cutoffs converge
in the first-order graph norm. Letting the mollification scale tend to zero then gives
membership in the closed test-function core. The proof includes `p = 1`, arbitrary real
Banach codomains, and boundary dimension zero.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued.HalfSpace

open Approximation GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A global Sobolev function vanishing below the boundary restricts to the
closure of Banach-valued test functions inside the upper half-space. -/
theorem restrict_mem_Wkp0_of_zero_below (hp : p ≠ ∞)
    (U : W^{1,p}(ℝ^(n + 1); F))
    (hU : ∀ᵐ x ∂volume, x (Fin.last n) ≤ 0 → U.val (baseIndex (n + 1) 1) x = 0) :
    restrictCLM (show
      (⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩ :
        Opens ℝ^(n + 1)) ≤ ⊤ from le_top) U ∈
      (wkp0SubmoduleOn (k := 1) (p := p)
        (Ω := ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩)
        (F := F)).toSubmodule := by
  let Ω : Opens ℝ^(n + 1) :=
    ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let a (j : ℕ) : ℝ^(n + 1) := -(3 * ε j) • EuclideanSpace.single (Fin.last n) 1
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [a, mul_zero, neg_zero, zero_smul] using
      (hε0.const_mul 3).neg.smul_const (EuclideanSpace.single (Fin.last n) (1 : ℝ))
  obtain ⟨hf, A, hA, ht⟩ :=
    translated_mollification_approximation (standardMollifier (n + 1)) hp U ε hε hε0 a ha
  have hmem (j : ℕ) :
      restrictCLM (show Ω ≤ ⊤ from le_top) (A j) ∈
        (wkp0SubmoduleOn (k := 1) (p := p) (Ω := Ω) (F := F)).toSubmodule := by
    apply restrict_mem_Wkp0_of_smooth_zero_strip hp (A j) (hf j)
      (by simpa only [baseIndex_toList, iteratedPartialDeriv] using
        hA j (baseIndex (n + 1) 1)) (hε j)
    intro x hx
    exact shifted_mollifyVector_eq_zero (hε j) hU hx
  apply (wkp0SubmoduleOn (k := 1) (p := p) (Ω := Ω) (F := F)).isClosed'.mem_of_tendsto
    (((restrictCLM (show Ω ≤ ⊤ from le_top)).continuous.tendsto U).comp ht)
  exact Eventually.of_forall hmem

/-- Vanishing almost everywhere on the open lower half-space suffices; the representative
may take arbitrary values on the boundary hyperplane, which has ambient measure zero. -/
theorem restrict_mem_Wkp0_of_zero_on_lower (hp : p ≠ ∞)
    (U : W^{1,p}(ℝ^(n + 1); F))
    (hU : (U.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F)
      =ᵐ[volume.restrict (ℝ^(n + 1)₋ : Set ℝ^(n + 1))] 0) :
    restrictCLM (show
      (⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩ :
        Opens ℝ^(n + 1)) ≤ ⊤ from le_top) U ∈
      (wkp0SubmoduleOn (k := 1) (p := p)
        (Ω := ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩)
        (F := F)).toSubmodule := by
  apply restrict_mem_Wkp0_of_zero_below hp U
  filter_upwards [(ae_restrict_iff'
    (SobolevSpace.HalfSpace.isOpen_lower (n + 1)).measurableSet).mp hU,
    SobolevSpace.HalfSpace.compl_upper_ae_eq_lower (n := n + 1)] with x hx hset hlast
  have hnot : x ∈ (ℝ^(n + 1)₊ : Set ℝ^(n + 1))ᶜ := not_lt_of_ge hlast
  exact hx (hset ▸ hnot)

end SobolevSpace.VectorValued.HalfSpace
