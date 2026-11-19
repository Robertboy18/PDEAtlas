/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Smooth extension by zero

An extension by zero is smooth when its closed support stays inside the original
open domain. The support condition supplies a zero neighbourhood at every point
outside the domain, so no boundary derivatives need to be assigned separately.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- Extending by zero preserves the differentiability order when the closed support
of the extension stays inside the open domain. The values of `f` outside the domain
play no role. -/
theorem ContDiffOn.indicator_of_tsupport_subset
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {k : WithTop ℕ∞}
    {f : E → F} {U : Set E} (hf : ContDiffOn 𝕜 k f U) (hU : IsOpen U)
    (hs : tsupport (U.indicator f) ⊆ U) :
    ContDiff 𝕜 k (U.indicator f) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · apply (hf.contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact indicator_of_mem hy f
  · exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hs h)))
