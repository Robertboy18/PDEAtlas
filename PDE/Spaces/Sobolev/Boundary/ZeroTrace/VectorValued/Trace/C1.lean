/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Space
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Operator

/-!
# Vanishing surface trace of the supported smooth closure

The physical surface trace vanishes on interior test functions, hence on their Sobolev
closure. This connects the closure definition of zero boundary values to the geometric
trace on domains admitting a finite C¹ extension atlas.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.C1

open Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  [Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
  {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Interior Banach-valued test functions have zero physical surface trace. -/
theorem traceLp_testFunction_eq_zero (hp : 1 ≤ p) (φ : 𝓓(Ω, F)) :
    traceLp p hp (testFunctionToWkp (k := 1) (p := ENNReal.ofReal p) φ) = 0 := by
  apply Lp.ext
  have hfrontier : ∀ᵐ x ∂surfaceMeasure (Ω : Set ℝ^(m + 1)),
      x ∈ frontier (Ω : Set ℝ^(m + 1)) :=
    ae_restrict_mem isClosed_frontier.measurableSet
  filter_upwards [traceLp_coeFn_ae hp _ (φ.contDiff.of_le (by simp))
    (testFunctionToWkp_base_ae φ), hfrontier,
    Lp.coeFn_zero F (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1)))]
    with x hx hΩx hz
  rw [hx, hz]
  apply φ.zero_on_compl
  change x ∉ (Ω : Set ℝ^(m + 1))
  exact fun hxΩ ↦ hΩx.2 (mem_interior_iff_mem_nhds.mpr (Ω.isOpen.mem_nhds hxΩ))

/-- The physical surface trace vanishes on the Banach-valued supported smooth closure. -/
theorem traceLp_eq_zero_of_mem_Wkp0 (hp : 1 ≤ p) (U : W^{1,ENNReal.ofReal p}(Ω; F))
    (hU : U ∈ (wkp0SubmoduleOn (k := 1) (p := ENNReal.ofReal p)
      (Ω := Ω) (F := F)).toSubmodule) :
    traceLp p hp U = 0 :=
  Wkp0SpaceOn.closed_property_of_testFunctions
    (isClosed_eq (traceLp p hp).continuous continuous_const)
    (traceLp_testFunction_eq_zero hp) ⟨U, hU⟩

end SobolevSpace.VectorValued.Trace.C1
