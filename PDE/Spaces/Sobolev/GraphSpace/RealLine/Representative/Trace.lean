/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.WeakConvergence
import PDE.Analysis.MeasureTheory.Lp.RealL2

/-!
# Pointwise traces of bounded real H¹ graphs

The stored weak derivative bounds the classical derivative almost everywhere.
A bounded H¹ family with a continuous L² base then has continuous pointwise
representative traces, including at the endpoints of a time interval.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis SobolevSpace.GraphSpace
open scoped Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- The classical derivative of the continuous real representative is the
stored weak derivative almost everywhere. -/
theorem ae_deriv_realLineRepresentative (U : W^{1,2}(ℝ^1)) :
    deriv (realLineRepresentative U) =ᵐ[volume]
      realLineCoordinateCLM (singleDerivIndex 1 0) U := by
  have h := SobolevSpace.Slices.ae_hasDerivAt_lineRepresentative_of_locallyIntegrable
    (f := realLineCoordinateCLM (baseIndex 1 1) U)
    (locallyIntegrableOn_univ.mp
      (hasWeakTimeDerivativeOn_realLineCoordinates U).locallyIntegrable_g)
  exact h.mono fun _ hx ↦ hx.deriv

/-- The real representative's derivative has the graph's L² coordinate bound. -/
theorem deriv_realLineRepresentative_L2_bound (U : W^{1,2}(ℝ^1)) :
    MemLp (deriv (realLineRepresentative U)) 2 volume ∧
      (∫ x, deriv (realLineRepresentative U) x ^ 2) ≤ ‖U‖ ^ 2 := by
  have hae := ae_deriv_realLineRepresentative U
  have hLp := (Lp.memLp (realLineCoordinateCLM (singleDerivIndex 1 0) U)).ae_eq hae.symm
  refine ⟨hLp, ?_⟩
  rw [integral_sq_eq_eLpNorm_toReal_sq hLp, eLpNorm_congr_ae hae, ← Lp.norm_def]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_realLineCoordinateCLM_le _ U) 2

/-- Strong L² continuity of a bounded H¹ family gives continuity of every
pointwise representative trace, including both endpoints. -/
theorem continuous_realLineRepresentative_eval_of_L2_continuous
    {X : Type*} [TopologicalSpace X] {g : X → W^{1,2}(ℝ^1)} {B : ℝ}
    (hbound : ∀ t, ‖g t‖ ≤ B)
    (hbase : Continuous (fun t ↦ realLineCoordinateCLM (baseIndex 1 1) (g t))) (x : ℝ) :
    Continuous (fun t ↦ realLineRepresentative (g t) x) :=
  continuous_iff_continuousAt.mpr fun t ↦
    tendsto_realLineRepresentative_eval_of_L2_tendsto hbound (hbase.tendsto t) x

end SobolevSpace.GraphSpace
