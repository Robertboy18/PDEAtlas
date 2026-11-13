/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactCurry
public import PDE.Analysis.Calculus.UniformDerivativeGraph

/-!
# Spatial derivatives at boundary parameters

A continuous family and its continuous spatial differential on a compact spatial
set retain the derivative relation at limits of the parameter. This is closure
of the existing derivative graph in the supremum norm, with no differentiable
extension in the parameter direction.
-/

@[expose] public noncomputable section

namespace BoundedContinuousFunction

open Filter Set TopologicalSpace
open scoped Topology

variable {T E F : Type*}
  [NormedAddCommGroup T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Spatial derivatives extend to closure parameters through joint continuity on
a compact spatial set. The spatial domain may have an arbitrary boundary. -/
theorem hasFDerivAt_slice_closure_parameter
    (K : Compacts E) {U : Set E} {S : Set T}
    (hU : IsOpen U) (hUK : U ⊆ K)
    (f : T → E → F) (D : T → E → E →L[ℝ] F)
    (hf : Continuous f.uncurry) (hD : Continuous D.uncurry)
    (hd : ∀ t ∈ S, ∀ x ∈ U, HasFDerivAt (f t) (D t x) x)
    {t : T} (ht : t ∈ closure S) {x : E} (hx : x ∈ U) :
    HasFDerivAt (f t) (D t x) x := by
  have heq (s : T) {y : E} (hy : y ∈ U) :
      Function.extend Subtype.val (compactCurry K f hf s) 0 =ᶠ[𝓝 y] f s := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact (extend_zero_apply _ (hUK hz)).trans rfl
  have h := hasFDerivAt_closure_parameter hU hUK
    (continuous_compactCurry K f hf) (continuous_compactCurry K D hD)
    (fun s hs y hy ↦ (hd s hs y hy).congr_of_eventuallyEq (heq s hy)) ht hx
  exact h.congr_of_eventuallyEq (heq t hx).symm

end BoundedContinuousFunction
