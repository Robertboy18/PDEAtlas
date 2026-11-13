/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.VectorValued.LpClosure
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation

/-!
# Completeness of Banach-valued Sobolev spaces

Each weak-derivative constraint is closed in a pair of `Lp` coordinates. Pulling these
closed sets back along the continuous coordinate projections proves that the Sobolev graph
is a closed submodule of the finite `PiLp` product. Completeness then follows from Mathlib.
The argument includes both exponent endpoints and unbounded open domains.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The Banach-valued Sobolev graph is closed in its finite product of `Lp` spaces. -/
theorem isClosed_wkpSubmoduleOn :
    IsClosed (wkpSubmoduleOn n k p Ω F : Set (WkpAmbientOn n k p Ω F)) := by
  change IsClosed {U : WkpAmbientOn n k p Ω F |
    ∀ a : DerivIndex n k, HasWeakDerivativeOn Ω a.toList (U (baseIndex n k)) (U a)}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro a
  exact (isClosed_hasWeakDerivativeOn (F := F) (p := p) Ω a.toList).preimage
    ((PiLp.proj (𝕜 := ℝ) p (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω))
      (baseIndex n k)).continuous.prodMk
      (PiLp.proj (𝕜 := ℝ) p (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω))
        a).continuous)

/-- Sobolev graph spaces with a Banach codomain are complete for every `1 ≤ p ≤ ∞`. -/
instance : CompleteSpace (W^{k,p}(Ω; F)) :=
  (isClosed_wkpSubmoduleOn (n := n) (k := k) (p := p) (Ω := Ω) (F := F)).completeSpace_coe

end SobolevSpace.VectorValued
