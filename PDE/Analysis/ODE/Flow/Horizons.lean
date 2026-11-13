/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Flow.Variation

/-!
# Flows on nested intervals of times and extension to negative times

The flow `flowOn v a b` of a Lipschitz field does not depend on the horizon `b`: on a smaller
interval `[a, b']` it is the same flow (`IsLipschitzFieldOn.flowOn_eq_of_le`), so flows of
different horizons define one flow on a life span. A Lipschitz (or `C¹`) field on `[0, b]` extends
to `[c, b]` by its value at time `0` for negative times (`IsLipschitzFieldOn.comp_max`,
`IsC1FieldOn.comp_max`), which gives flows on time intervals containing `0` in their interior.

## Main results

* `PDE.Analysis.ODE.IsLipschitzFieldOn.mono`, `PDE.Analysis.ODE.IsLipschitzFieldOn.flowOn_eq_of_le`.
* `PDE.Analysis.ODE.IsLipschitzFieldOn.comp_max`, `PDE.Analysis.ODE.IsC1FieldOn.comp_max`.
-/

@[expose] public noncomputable section

open Set Filter Function
open scoped Topology NNReal

set_option linter.missingDocs true

/-! ### Flows on nested intervals and extension to negative times -/

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {v : ℝ → E → E} {Dv : ℝ → E → E →L[ℝ] E} {a b : ℝ} {K : ℝ≥0}

omit [NormedSpace ℝ E] in
/-- A Lipschitz field restricts to a smaller interval of times. -/
theorem IsLipschitzFieldOn.mono (hv : IsLipschitzFieldOn v a b K) {a' b' : ℝ} (ha : a ≤ a')
    (hb : b' ≤ b) : IsLipschitzFieldOn v a' b' K :=
  ⟨hv.continuousOn.mono (prod_mono (Icc_subset_Icc ha hb) subset_rfl),
    fun t ht ↦ hv.lipschitzWith t ⟨ha.trans ht.1, ht.2.trans hb⟩⟩

/-- **Flows on nested intervals of times agree** on the smaller interval. -/
theorem IsLipschitzFieldOn.flowOn_eq_of_le [FiniteDimensional ℝ E]
    (hv : IsLipschitzFieldOn v a b K) {b' : ℝ} (hb : b' ≤ b) {s t : ℝ} (hs : s ∈ Icc a b')
    (ht : t ∈ Icc a b') (x : E) : flowOn v a b' s t x = flowOn v a b s t x := by
  have hv' := hv.mono le_rfl hb
  exact hv.eq_flowOn_of_hasDerivWithinAt (Icc_subset_Icc le_rfl hb) ht (hv'.flowOn_self ht x)
    (fun r hr ↦ hv'.hasDerivWithinAt_flowOn hr ht x) s hs

omit [NormedSpace ℝ E] in
/-- A Lipschitz field on `[0, b]` extended to earlier times by its value at `0` is a Lipschitz
field on `[c, b]`. -/
theorem IsLipschitzFieldOn.comp_max (hv : IsLipschitzFieldOn v 0 b K) (hb : 0 ≤ b) (c : ℝ) :
    IsLipschitzFieldOn (fun r ↦ v (max r 0)) c b K where
  continuousOn := hv.continuousOn.comp
    ((continuous_fst.max continuous_const).prodMk continuous_snd).continuousOn
    fun _ hp ↦ ⟨⟨le_max_right _ _, max_le hp.1.2 hb⟩, mem_univ _⟩
  lipschitzWith _ ht := hv.lipschitzWith _ ⟨le_max_right _ _, max_le ht.2 hb⟩

omit [NormedSpace ℝ E] in
/-- A Lipschitz field on `[0, t₀ + b]` translated in time by `t₀ ≥ 0` is a Lipschitz field on
`[0, b]`. -/
theorem IsLipschitzFieldOn.shift {t₀ : ℝ} (hv : IsLipschitzFieldOn v 0 (t₀ + b) K)
    (ht₀ : 0 ≤ t₀) : IsLipschitzFieldOn (fun t ↦ v (t₀ + t)) 0 b K where
  continuousOn := hv.continuousOn.comp
    ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
    fun p hp ↦ ⟨⟨show 0 ≤ t₀ + p.1 by linarith [hp.1.1],
      show t₀ + p.1 ≤ t₀ + b by linarith [hp.1.2]⟩, mem_univ _⟩
  lipschitzWith t ht := hv.lipschitzWith _ ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- A `C¹` field on `[0, b]` extended to earlier times by its value at `0` is a `C¹` field on
`[c, b]`. -/
theorem IsC1FieldOn.comp_max (hv : IsC1FieldOn v Dv 0 b K) (hb : 0 ≤ b) (c : ℝ) :
    IsC1FieldOn (fun r ↦ v (max r 0)) (fun r ↦ Dv (max r 0)) c b K where
  continuousOn := hv.continuousOn.comp
    ((continuous_fst.max continuous_const).prodMk continuous_snd).continuousOn
    fun _ hp ↦ ⟨⟨le_max_right _ _, max_le hp.1.2 hb⟩, mem_univ _⟩
  continuousOn_deriv := hv.continuousOn_deriv.comp
    ((continuous_fst.max continuous_const).prodMk continuous_snd).continuousOn
    fun _ hp ↦ ⟨⟨le_max_right _ _, max_le hp.1.2 hb⟩, mem_univ _⟩
  hasFDerivAt _ ht x := hv.hasFDerivAt _ ⟨le_max_right _ _, max_le ht.2 hb⟩ x
  norm_le _ ht x := hv.norm_le _ ⟨le_max_right _ _, max_le ht.2 hb⟩ x

end PDE.Analysis.ODE
