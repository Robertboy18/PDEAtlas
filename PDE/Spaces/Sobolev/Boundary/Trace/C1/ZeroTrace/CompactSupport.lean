/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Core
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Scalar
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.C1.CompactSupport
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Cutoff

/-!
# Interior localization on an operational C¹ domain

A real-valued Sobolev field on a domain with a `C1ExtensionAtlas` whose base representative has
compact support inside the domain belongs to `W^{1,p}_0`, for every `p ≠ ∞`. This is the case
`F = ℝ` of the Banach-valued
`SobolevSpace.VectorValued.Trace.C1.mem_Wkp0_of_compactSupport`: the scalar Sobolev graph is the
Banach-valued graph at codomain `ℝ` (`VectorValued.scalarEquiv`), with the same closure of the
interior test functions (`VectorValued.scalarEquiv_mem_wkp0_iff`). Multiplication by a cutoff
supported inside the domain is the case of the representative `ψ u`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set GraphSpace TopologicalSpace
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A Sobolev field on a C¹ domain whose representative has compact support inside
the domain belongs to `W^{1,p}_0`. This is the case `F = ℝ` of
`SobolevSpace.VectorValued.Trace.C1.mem_Wkp0_of_compactSupport`. -/
theorem mem_Wkp0_of_compactSupport (hp : p ≠ ∞) (u : W^{1,p}(Ω))
    (f : ℝ^(m + 1) → ℝ) (hu : baseRepresentative u =ᵐ[domainMeasure (m + 1) Ω] f)
    (hf : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    u ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p) (Ω := Ω)).toSubmodule := by
  let V : Opens ℝ^(m + 1) := ⟨Ω, hΩ.isOpen⟩
  let U := (VectorValued.scalarEquiv (Ω := V)).symm u
  exact (VectorValued.scalarEquiv_mem_wkp0_iff U).mpr
    (VectorValued.Trace.C1.mem_Wkp0_of_compactSupport hp U f hu hf hs)

/-- Multiplication by an interior cutoff takes every Sobolev field on a C¹ domain
into the closure of the interior test functions: the product has compact support inside the
domain, and `mem_Wkp0_of_compactSupport` applies. -/
theorem cutoffCLM_mem_Wkp0 (hp : p ≠ ∞)
    (ψ : TestFunction (⊤ : Opens (ℝ^(m + 1))) ℝ ⊤)
    (hψ : tsupport ψ.toFun ⊆ Ω) (u : W^{1,p}(Ω)) :
    cutoffCLM ψ u ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := p) (Ω := Ω)).toSubmodule :=
  mem_Wkp0_of_compactSupport hp _ (fun x ↦ ψ.toFun x * baseRepresentative u x)
    (cutoffCLM_base_apply_ae ψ u) ψ.hasCompactSupport.mul_right
    (tsupport_mul_subset_left.trans hψ)

end SobolevSpace.Trace.C1
