/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.BoundedOperator

/-!
# Chart pullback and linear maps of Banach targets

The bounded chart pullback acts by composition on almost-everywhere
representatives. Consequently it commutes with every continuous linear map of
the target, including continuous linear functionals used in weak chain rules.
Neither the construction nor these identities require a finite-dimensional target.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SobolevSpace.WeakChangeOfVariables

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E : OpenPartialHomeomorph ℝ^n ℝ^n}
  {F G : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Chart pullback composes any chosen almost-everywhere representative with the chart. -/
theorem boundedPullbackCLM_ae_eq_comp
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    (u : Lp F p (domainMeasure n E.target)) {f : ℝ^n → F}
    (hu : ⇑u =ᵐ[domainMeasure n E.target] f) :
    ⇑(boundedPullbackCLM hE hSymm hTarget u) =ᵐ[domainMeasure n E.source]
      fun x ↦ f (E x) :=
  (boundedPullbackLp_apply_ae hE hSymm hTarget u).trans
    ((quasiMeasurePreserving_partialHomeomorph hE hSymm).ae_eq_comp hu)

/-- Pulling back an `Lp` function commutes with applying a continuous linear
map to its values. -/
theorem boundedPullbackCLM_compLpL
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) (L : F →L[ℝ] G)
    (u : Lp F p (domainMeasure n E.target)) :
    boundedPullbackCLM hE hSymm hTarget (L.compLpL p (domainMeasure n E.target) u) =
      L.compLpL p (domainMeasure n E.source) (boundedPullbackCLM hE hSymm hTarget u) := by
  apply Lp.ext
  have hleft := boundedPullbackCLM_ae_eq_comp hE hSymm hTarget
    (L.compLpL p (domainMeasure n E.target) u) (L.coeFn_compLpL u)
  exact hleft.trans
    (((boundedPullbackLp_apply_ae hE hSymm hTarget u).fun_comp L).symm.trans
      (L.coeFn_compLpL (boundedPullbackCLM hE hSymm hTarget u)).symm)

/-- Naturality as an equality of continuous linear operators. -/
theorem compLpL_comp_boundedPullbackCLM
    (hE : ContDiff ℝ 1 E) (hSymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) (L : F →L[ℝ] G) :
    (L.compLpL p (domainMeasure n E.source)).comp
        (boundedPullbackCLM hE hSymm hTarget) =
      (boundedPullbackCLM hE hSymm hTarget).comp
        (L.compLpL p (domainMeasure n E.target)) := by
  apply ContinuousLinearMap.ext
  intro u
  exact (boundedPullbackCLM_compLpL hE hSymm hTarget L u).symm

end SobolevSpace.WeakChangeOfVariables
