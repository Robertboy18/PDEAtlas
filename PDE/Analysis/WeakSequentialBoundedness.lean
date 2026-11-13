/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Norm boundedness of weakly convergent sequences

A weakly convergent sequence is bounded in norm, even when the original normed
space is incomplete. Apply uniform boundedness to its evaluations on the
continuous dual, which is complete, and use the isometric inclusion into the
double dual. The sequential hypothesis matters: a convergent net can have an
unbounded initial part.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, Appendix D.4, p. 723 (stated without proof).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis

/-- A weakly convergent sequence in a real or complex normed space has bounded
range in the norm bornology. Completeness of the original space is unnecessary. -/
theorem isBounded_range_of_tendsto_weak
    {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    {u : ℕ → X} {uLimit : X}
    (hu : Tendsto (fun j ↦ toWeakSpace 𝕜 X (u j)) atTop
      (𝓝 (toWeakSpace 𝕜 X uLimit))) :
    Bornology.IsBounded (range u) := by
  have hpoint (f : StrongDual 𝕜 X) : ∃ C : ℝ, ∀ j, ‖f (u j)‖ ≤ C := by
    have hf : Tendsto (fun j ↦ f (u j)) atTop (𝓝 (f uLimit)) :=
      (WeakBilin.eval_continuous (topDualPairing 𝕜 X).flip f).continuousAt.tendsto.comp hu
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp
      (Metric.isBounded_range_of_tendsto _ hf)
    exact ⟨C, fun j ↦ hC _ (mem_range_self j)⟩
  obtain ⟨C, hC⟩ := banach_steinhaus
    (g := fun j ↦ NormedSpace.inclusionInDoubleDual 𝕜 X (u j)) hpoint
  refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact ((NormedSpace.inclusionInDoubleDualLi 𝕜).norm_map (u j)) ▸ hC j

end PDE.Analysis
