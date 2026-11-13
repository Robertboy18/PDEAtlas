/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.EuclideanCoordinates
public import PDE.Analysis.MeasureTheory.Lp.Reflexivity
import PDE.Analysis.Normed.Reflexivity

/-!
# Reflexivity of Euclidean-valued Lp

At exponents strictly between one and infinity, scalar Lp reflexivity and the finite
coordinate equivalence give reflexivity with the Euclidean-valued Lp norm.
-/

@[expose] public section

namespace MeasureTheory.Lp

open NormedSpace
open scoped ENNReal

/-- Euclidean-valued Lp over a sigma-finite measure is reflexive when `1 < p < ∞`. -/
theorem surjective_inclusionInDoubleDual_euclidean
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ ∞) :
    Function.Surjective
      (inclusionInDoubleDual ℝ (Lp (ℝ^n) p μ)) :=
  surjective_inclusionInDoubleDual_of_equiv euclideanTupleEquiv
    (surjective_inclusionInDoubleDual_pi (fun _ : Fin n ↦ Lp ℝ p μ)
      (fun _ ↦ surjective_inclusionInDoubleDual hp hp_top))

end MeasureTheory.Lp
