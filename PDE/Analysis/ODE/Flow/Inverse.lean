/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.Variation

/-!
# Differences of inverse flow maps and inverse variations

For two flows, the difference of the inverse maps at a point is controlled by the difference of
the forward maps at its preimage (`IsLipschitzFieldOn.norm_flowOn_sub_flowOn_le_of_inverse`): if
`a' = Φ'(t, s) x` then `Φ(t, s) x - a' = Φ(t, s)(Φ'(s, t) a') - Φ(t, s)(Φ(s, t) a')`. For the
first variations, the inverse `W = D Φ(t, s)(Φ(s, t) x)` of `J = D Φ(s, t) x` satisfies
`W - W' = W (J' - J) W'` (`norm_sub_le_of_comp_eq_id`), so
`‖W - W'‖ ≤ ‖W‖ ‖J - J'‖ ‖W'‖` (`IsC1FieldOn.norm_variationOn_inverse_sub_le`).

## Main results

* `norm_sub_le_of_comp_eq_id`: if `W ∘ J = id` and `J' ∘ W' = id`, then
  `‖W - W'‖ ≤ ‖W‖ ‖J - J'‖ ‖W'‖`.
* `IsLipschitzFieldOn.norm_flowOn_sub_flowOn_le_of_inverse`: with `a' = Φ'(t, s) x`,
  `‖Φ(t, s) x - Φ'(t, s) x‖ ≤ exp (K |t - s|) ‖Φ(s, t) a' - Φ'(s, t) a'‖`.
* `IsC1FieldOn.norm_variationOn_inverse_sub_le`: the inverse first variations of two fields
  satisfy `‖W - W'‖ ≤ ‖W‖ ‖J - J'‖ ‖W'‖`.
-/

@[expose] public section

noncomputable section

open Set
open scoped NNReal

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Difference of left and right inverses.** If `W ∘ J = id` and `J' ∘ W' = id`, then
`W - W' = W ∘ (J' - J) ∘ W'`, so `‖W - W'‖ ≤ ‖W‖ ‖J - J'‖ ‖W'‖`. -/
theorem norm_sub_le_of_comp_eq_id {W W' J J' : E →L[ℝ] E}
    (hW : W.comp J = ContinuousLinearMap.id ℝ E) (hW' : J'.comp W' = ContinuousLinearMap.id ℝ E) :
    ‖W - W'‖ ≤ ‖W‖ * ‖J - J'‖ * ‖W'‖ := by
  have heq : W - W' = (W.comp (J' - J)).comp W' := by
    ext y
    have h1 := congrArg (fun L : E →L[ℝ] E ↦ L (W' y)) hW
    have h2 := congrArg (fun L : E →L[ℝ] E ↦ W (L y)) hW'
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
    simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub, h1, h2]
  rw [heq, norm_sub_rev J J']
  calc ‖(W.comp (J' - J)).comp W'‖ ≤ ‖W.comp (J' - J)‖ * ‖W'‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖W‖ * ‖J' - J‖ * ‖W'‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)

variable [FiniteDimensional ℝ E] {v v' : ℝ → E → E} {a b : ℝ} {K K' : ℝ≥0}

/-- **Difference of inverse flow maps.** With `a' = Φ'(t, s) x`,
`‖Φ(t, s) x - Φ'(t, s) x‖ ≤ exp (K |t - s|) ‖Φ(s, t) a' - Φ'(s, t) a'‖`. -/
theorem IsLipschitzFieldOn.norm_flowOn_sub_flowOn_le_of_inverse
    (hv : IsLipschitzFieldOn v a b K) (hv' : IsLipschitzFieldOn v' a b K') {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    ‖flowOn v a b t s x - flowOn v' a b t s x‖ ≤
      Real.exp (K * |t - s|) *
        ‖flowOn v a b s t (flowOn v' a b t s x) - flowOn v' a b s t (flowOn v' a b t s x)‖ := by
  set a' := flowOn v' a b t s x
  have hx : flowOn v' a b s t a' = x := hv'.flowOn_flowOn_self ht hs x
  have ha' : flowOn v a b t s (flowOn v a b s t a') = a' := hv.flowOn_flowOn_self hs ht a'
  have h := hv.norm_flowOn_sub_le ht hs (flowOn v' a b s t a') (flowOn v a b s t a')
  rw [hx] at h
  calc ‖flowOn v a b t s x - a'‖ =
        ‖flowOn v a b t s x - flowOn v a b t s (flowOn v a b s t a')‖ := by rw [ha']
    _ ≤ Real.exp (K * |t - s|) * ‖x - flowOn v a b s t a'‖ := h
    _ = _ := by rw [← hx, norm_sub_rev]

/-- **Difference of inverse variations.** The inverse `W = D Φ(t, s)(Φ(s, t) x)` of the first
variation `J = D Φ(s, t) x`, and likewise for a second field, satisfy
`‖W - W'‖ ≤ ‖W‖ ‖J - J'‖ ‖W'‖`. -/
theorem IsC1FieldOn.norm_variationOn_inverse_sub_le {Dv Dv' : ℝ → E → E →L[ℝ] E}
    (hv : IsC1FieldOn v Dv a b K) (hv' : IsC1FieldOn v' Dv' a b K') {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : E) :
    ‖variationOn v Dv a b t s (flowOn v a b s t x) -
        variationOn v' Dv' a b t s (flowOn v' a b s t x)‖ ≤
      ‖variationOn v Dv a b t s (flowOn v a b s t x)‖ *
        ‖variationOn v Dv a b s t x - variationOn v' Dv' a b s t x‖ *
        ‖variationOn v' Dv' a b t s (flowOn v' a b s t x)‖ := by
  refine norm_sub_le_of_comp_eq_id (hv.variationOn_flowOn_comp_variationOn hs ht x) ?_
  have h := hv'.variationOn_flowOn_comp_variationOn ht hs (flowOn v' a b s t x)
  rwa [hv'.isLipschitzFieldOn.flowOn_flowOn_self hs ht x] at h

end PDE.Analysis.ODE
