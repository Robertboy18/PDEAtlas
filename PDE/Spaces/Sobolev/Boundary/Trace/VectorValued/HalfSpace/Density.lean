/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.WholeSpace.CompactSupport
public import PDE.Spaces.Sobolev.Extension.VectorValued.HalfSpace.Operator

/-!
# Compact smooth density on the upper half-space

Reflection extends the Banach-valued first-order graph to the whole space.
Restricting compact smooth approximants transfers norm density to the half-space,
with no vanishing condition on its physical boundary.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

namespace Trace.HalfSpace

/-- Restrictions of ambient compact smooth functions are dense in the Banach-valued
upper-half-space graph. Their supports may meet the flat boundary. -/
theorem dense_compact_smooth (hp : p ≠ ∞) :
    Dense {U : W^{1,p}(⟨ℝ^(n+1)₊, SobolevSpace.HalfSpace.isOpen_upper (n+1)⟩; F) |
      ∃ f : ℝ^(n+1) → F, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
        (U.val (baseIndex (n+1) 1) : ℝ^(n+1) → F)
          =ᵐ[domainMeasure (n+1) ℝ^(n+1)₊] f} := by
  intro U
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  let E := HigherOrderReflection.weightedReflection (n+1) 1 p U
  obtain ⟨V, ⟨f, hf, hcs, hbase⟩, hV⟩ :=
    Metric.mem_closure_iff.mp (dense_compact_smooth_univ hp E) δ hδ
  let R := restrictCLM (k := 1) (p := p) (F := F)
    (show (⟨ℝ^(n+1)₊, SobolevSpace.HalfSpace.isOpen_upper (n+1)⟩ : Opens ℝ^(n+1)) ≤ ⊤ from le_top)
  have hRE : R E = U := HigherOrderReflection.restrict_weightedReflection (n+1) 1 p U
  refine ⟨R V, ⟨f, hf, hcs, ?_⟩, ?_⟩
  · exact (restrictCLM_apply_ae le_top V (baseIndex (n+1) 1)).trans
      (hbase.filter_mono (ae_mono Measure.restrict_le_self))
  · rw [dist_eq_norm] at hV ⊢
    rw [← hRE, ← map_sub]
    exact (norm_restrictCLM_apply_le _ (E - V)).trans_lt hV

end Trace.HalfSpace

end SobolevSpace.VectorValued
