/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.BanachReflexivity
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Topology

/-!
# The closed-graph step in Banach-valued Sobolev reflexivity

The Sobolev graph is a closed subspace of a finite `PiLp` product. Therefore the
Bochner dual-representation assumptions used in the Lp bidual argument give reflexivity
of this same graph, for every order and dimension.

The dual-representation property for a reflexive Banach target is a hypothesis of
these results, so they do not give reflexivity unconditionally.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate p q] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Once the two Bochner dual pairings are surjective, reflexivity passes to the
Banach-valued weak-derivative graph. No boundedness or boundary regularity is assumed. -/
theorem WkpSpaceOn.surjective_inclusionInDoubleDual_of_surjective_dualPairing
    (hF : Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ F))
    (hP : Function.Surjective
      ((ContinuousLinearMap.id ℝ (StrongDual ℝ F)).lpPairing (domainMeasure n Ω) q p))
    (hQ : Function.Surjective
      ((ContinuousLinearMap.id ℝ (StrongDual ℝ (StrongDual ℝ F))).lpPairing
        (𝕜 := ℝ) (E := StrongDual ℝ (StrongDual ℝ F)) (F := StrongDual ℝ F) (G := ℝ)
        (domainMeasure n Ω) p q)) :
    Function.Surjective (NormedSpace.inclusionInDoubleDual ℝ (W^{k,p}(Ω; F))) := by
  apply NormedSpace.surjective_inclusionInDoubleDual_submodule
    (wkpSubmoduleOn n k p Ω F) isClosed_wkpSubmoduleOn
  exact NormedSpace.surjective_inclusionInDoubleDual_piLp p
    (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω))
    (fun _ ↦ Lp.surjective_inclusionInDoubleDual_of_surjective_dualPairing hF hP hQ)

end SobolevSpace.VectorValued
