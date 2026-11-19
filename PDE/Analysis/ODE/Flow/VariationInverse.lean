/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.HigherVariation
public import PDE.Analysis.ODE.Flow.IntegralEstimates
public import PDE.Analysis.Calculus.SmoothFamilyInverse

/-!
# The inverse first variation as a smooth family

The first variation `variationOn v Dv a b s t x` of a `C¹` field is invertible, with inverse the
first variation `variationOn v Dv a b t s (flowOn v a b s t x)` back to the base time
(`IsC1FieldOn.ringInverse_variationOn`). For a field that is a smooth family of order `m + 1`,
the inverse first variations along the flow,
`(s, x) ↦ variationOn v Dv a b t s (flowOn v a b s t x)`, form a smooth family of order `m`
(`IsC1FieldOn.isSmoothFamilyOn_variationOn_flowOn`): they are the inverses in the ring
`E →L[ℝ] E` of the derivatives of the flow maps.

## Main definitions

* `IsC1FieldOn.variationUnit`: the first variation as a unit of the ring `E →L[ℝ] E`.

## Main results

* `IsC1FieldOn.isUnit_variationOn`: the first variation is invertible.
* `IsC1FieldOn.ringInverse_variationOn`: its inverse is the first variation back to the base time.
* `IsC1FieldOn.isSmoothFamilyOn_variationOn_flowOn`: the inverse first variations along the flow
  form a smooth family of order `m` when the field is a smooth family of order `m + 1`.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis.ODE

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {a b s t : ℝ} {K : NNReal}

namespace IsC1FieldOn

/-- The first variation as a unit of the ring `E →L[ℝ] E`. -/
def variationUnit (hv : IsC1FieldOn v Dv a b K) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    (E →L[ℝ] E)ˣ where
  val := variationOn v Dv a b s t x
  inv := variationOn v Dv a b t s (flowOn v a b s t x)
  val_inv := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
    exact hv.variationOn_comp_variationOn_flowOn hs ht x
  inv_val := by
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
    exact hv.variationOn_flowOn_comp_variationOn hs ht x

/-- The first variation is invertible. -/
theorem isUnit_variationOn (hv : IsC1FieldOn v Dv a b K) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (x : E) : IsUnit (variationOn v Dv a b s t x) :=
  ⟨hv.variationUnit hs ht x, rfl⟩

/-- The inverse of the first variation is the first variation back to the base time. -/
theorem ringInverse_variationOn (hv : IsC1FieldOn v Dv a b K) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) (x : E) :
    Ring.inverse (variationOn v Dv a b s t x) =
      variationOn v Dv a b t s (flowOn v a b s t x) :=
  Ring.inverse_unit (hv.variationUnit hs ht x)

/-- **The inverse first variations along the flow form a smooth family** of order `m` when the
field is a smooth family of order `m + 1`. -/
theorem isSmoothFamilyOn_variationOn_flowOn (hv : IsC1FieldOn v Dv a b K) {m : ℕ}
    (hsm : IsSmoothFamilyOn (m + 1) v (Icc a b)) (ht : t ∈ Icc a b) :
    IsSmoothFamilyOn m (fun s x ↦ variationOn v Dv a b t s (flowOn v a b s t x)) (Icc a b) := by
  have hX := hv.isSmoothFamilyOn_flowOn hsm ht
  have hD : IsSmoothFamilyOn m (fun s x ↦ fderiv ℝ (flowOn v a b s t) x) (Icc a b) :=
    (isSmoothFamilyOn_succ_iff.mp hX).2.2
  have hU := hD.ringInverse fun s hs x ↦ by
    rw [(hv.hasFDerivAt_flowOn hs ht x).fderiv]
    exact hv.isUnit_variationOn hs ht x
  refine hU.congr fun s hs ↦ funext fun x ↦ ?_
  rw [(hv.hasFDerivAt_flowOn hs ht x).fderiv, hv.ringInverse_variationOn hs ht x]

end IsC1FieldOn

end PDE.Analysis.ODE
