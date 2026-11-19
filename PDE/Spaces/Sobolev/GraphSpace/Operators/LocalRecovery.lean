/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction

/-!
# Local representatives of bounded Sobolev recovery maps

A bounded linear map into a global Sobolev space also gives local representatives
at every lower order. Restriction and order reduction are contractions, so the
same operator norm controls each local graph. This is the common step when the
linear and nonlinear PDE estimates recover their source fields from an energy space.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory

/-- A global Sobolev recovery map supplies local representatives at every lower
order, bounded by its operator norm times the norm of the input. -/
theorem exists_local_hk_representative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n k m : ℕ} (hkm : k ≤ m) (A : E →L[ℝ] W^{m,2}(ℝ^n))
    (q : E → ℝ^n → ℝ) (hrep : ∀ U, q U =ᵐ[volume] baseRepresentative (A U)) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : E, ∃ Q : W^{k,2}(Metric.ball (0 : ℝ^n) r),
      baseRepresentative Q =ᵐ[domainMeasure n (Metric.ball 0 r)] q U ∧
      ‖Q‖ ≤ C * ‖U‖ := by
  refine ⟨‖A‖, ContinuousLinearMap.opNorm_nonneg A, ?_⟩
  intro U
  let G := lowerOrderCLM hkm (A U)
  refine ⟨restrictCLM measurableSet_ball (Set.subset_univ _) G, ?_, ?_⟩
  · exact (restrictCLM_apply_ae measurableSet_ball (Set.subset_univ _) G
      (baseIndex n k)).trans (by
        change baseRepresentative G =ᵐ[domainMeasure n (Metric.ball 0 r)] q U
        simpa only [G, baseRepresentative_lowerOrderCLM] using (hrep U).symm.restrict)
  · exact (norm_restrictCLM_apply_le measurableSet_ball (Set.subset_univ _) G).trans
      ((norm_lowerOrderCLM_apply_le hkm (A U)).trans (A.le_opNorm U))

end SobolevSpace.GraphSpace
