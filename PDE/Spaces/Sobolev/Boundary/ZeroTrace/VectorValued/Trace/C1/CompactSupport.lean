/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Definitions
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Space
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.SmoothMultiplier
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Naturality

/-!
# Compact interior support in Banach-valued Sobolev spaces

An interior smooth cutoff sends the ambient smooth core into Banach-valued
test functions. Ambient density and closedness then put every localized Sobolev
field in `W₀^{1,p}(Ω; F)`. Consequently, a field with a compactly supported base
representative inside the domain belongs to that same closure, without any
smoothness assumption on the representative.

The domain has a finite C¹ extension atlas, the exponent is finite and at least
one, and the target is an arbitrary real Banach space. Boundary dimension zero
and the empty domain are included.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.C1

open GraphSpace

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Multiplication by a smooth cutoff supported inside the domain takes every
Sobolev field into the closure of the Banach-valued interior test functions. -/
theorem compactSmoothMultiplierCLM_mem_Wkp0 (hp : p ≠ ∞)
    (ψ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ)) (hψ : tsupport ψ.toFun ⊆ Ω)
    (U : W^{1,p}(Ω; F)) :
    compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport U ∈
      (wkp0SubmoduleOn (k := 1) (p := p) (Ω := Ω) (F := F)).toSubmodule := by
  refine (dense_compact_smooth hp).induction ?_
    ((wkp0SubmoduleOn (k := 1) (p := p) (Ω := Ω) (F := F)).isClosed'.preimage
      (compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport).continuous) U
  rintro V ⟨f, hf, _, hbase⟩
  let φ : 𝓓(Ω, F) :=
    ⟨fun x ↦ ψ x • f x, ψ.contDiff.smul hf, ψ.hasCompactSupport.smul_right,
      (tsupport_smul_subset_left ψ f).trans hψ⟩
  have heq : compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport V =
      testFunctionToWkp (k := 1) (p := p) φ := by
    apply WkpSpaceOn.ext_of_base_ae
    filter_upwards
      [compactSmoothMultiplierCLM_base_ae ψ.toFun ψ.contDiff ψ.hasCompactSupport V,
        hbase, testFunctionToWkp_base_ae (k := 1) (p := p) φ] with x hx hfx hφx
    rw [hx, hfx, hφx]
    rfl
  rw [heq]
  exact testFunctionToWkp_mem_Wkp0 φ

/-- A Sobolev field with a compactly supported base representative inside the
domain belongs to `W₀^{1,p}(Ω; F)`. The representative need not be smooth or continuous. -/
theorem mem_Wkp0_of_compactSupport (hp : p ≠ ∞) (U : W^{1,p}(Ω; F))
    (f : ℝ^(m + 1) → F)
    (hU : (U.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω] f)
    (hf : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    U ∈ (wkp0SubmoduleOn (k := 1) (p := p) (Ω := Ω) (F := F)).toSubmodule := by
  obtain ⟨ψ, hψ, heq, _⟩ :=
    TestFunction.exists_eq_one_on_compact Ω.isOpen hf hs
  have hcut : compactSmoothMultiplierCLM ψ.toFun ψ.contDiff ψ.hasCompactSupport U = U := by
    apply WkpSpaceOn.ext_of_base_ae
    filter_upwards
      [compactSmoothMultiplierCLM_base_ae ψ.toFun ψ.contDiff ψ.hasCompactSupport U,
        hU] with x hx hfx
    rw [hx, hfx]
    by_cases hxSupport : x ∈ tsupport f
    · rw [heq x hxSupport, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hxSupport, smul_zero]
  rw [← hcut]
  exact compactSmoothMultiplierCLM_mem_Wkp0 hp ψ hψ U

end SobolevSpace.VectorValued.Trace.C1
