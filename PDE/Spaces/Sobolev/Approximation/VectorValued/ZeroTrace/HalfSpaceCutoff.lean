/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.ZeroTrace.HalfSpaceSupport
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Space
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Restriction
import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.WholeSpace.CompactSupport

/-!
# Compact cutoffs of smooth functions with a boundary gap

A globally smooth Sobolev representative vanishing in a strip at the boundary restricts
to `W₀^{1,p}` on the upper half-space. Expanding scalar cutoffs give Banach-valued
Mathlib test functions supported inside the domain, and the first-order cutoff theorem
gives convergence in the Sobolev graph norm at every finite exponent.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued.HalfSpace

open Approximation GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Compact cutoffs of a smooth representative with a positive boundary gap converge
to its restriction in the closure defining `W₀^{1,p}`. -/
theorem restrict_mem_Wkp0_of_smooth_zero_strip (hp : p ≠ ∞)
    (U : W^{1,p}(ℝ^(n + 1); F)) {f : ℝ^(n + 1) → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hbase : (U.val (baseIndex (n + 1) 1) : ℝ^(n + 1) → F) =ᵐ[volume] f)
    {δ : ℝ} (hδ : 0 < δ) (hzero : ∀ x, x (Fin.last n) ≤ δ → f x = 0) :
    restrictCLM (show
      (⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩ :
        Opens ℝ^(n + 1)) ≤ ⊤ from le_top) U ∈
      (wkp0SubmoduleOn (k := 1) (p := p)
        (Ω := ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩)
        (F := F)).toSubmodule := by
  let Ω : Opens ℝ^(n + 1) :=
    ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩
  let R (j : ℕ) : ℝ := j + 1
  have hRpos (j : ℕ) : 0 < R j := by dsimp [R]; positivity
  have hR : Tendsto R atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hs : tsupport f ⊆ Ω := tsupport_subset_upper_of_zero_strip hδ hzero
  let φ (j : ℕ) : 𝓓(Ω, F) :=
    ⟨fun x ↦ cutoff (R j) x • f x, (cutoff_contDiff (R j)).smul hf,
      (cutoff_hasCompactSupport (hRpos j).ne').smul_right,
      (tsupport_smul_subset_right _ _).trans hs⟩
  let A (j : ℕ) : W^{1,p}(ℝ^(n + 1); F) :=
    compactSmoothMultiplierCLM (cutoff (R j)) (cutoff_contDiff (R j))
      (cutoff_hasCompactSupport (hRpos j).ne') U
  have hφ (j : ℕ) :
      testFunctionToWkp (k := 1) (p := p) (φ j) =
        restrictCLM (show Ω ≤ ⊤ from le_top) (A j) := by
    apply WkpSpaceOn.ext_of_base_ae
    have hcut := compactSmoothMultiplierCLM_base_ae (cutoff (R j))
      (cutoff_contDiff (R j)) (cutoff_hasCompactSupport (hRpos j).ne') U
    simp only [domainMeasure, Opens.coe_top, Measure.restrict_univ] at hcut
    filter_upwards [testFunctionToWkp_base_ae (k := 1) (p := p) (φ j),
      restrictCLM_apply_ae (show Ω ≤ ⊤ from le_top) (A j) (baseIndex (n + 1) 1),
      hcut.filter_mono (ae_mono Measure.restrict_le_self),
      hbase.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hres hc hb
    exact hx.trans ((hres.trans (hc.trans (congrArg (cutoff (R j) x • ·) hb))).symm)
  apply mem_Wkp0_of_tendsto_testFunctionToWkp _ φ
  simp_rw [hφ]
  exact ((restrictCLM (show Ω ≤ ⊤ from le_top)).continuous.tendsto U).comp
    (tendsto_compactSmoothMultiplierCLM_cutoff hp U hRpos hR)

end SobolevSpace.VectorValued.HalfSpace
