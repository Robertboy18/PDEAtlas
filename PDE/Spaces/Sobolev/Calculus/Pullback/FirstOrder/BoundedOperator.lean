/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.EssentialBound

/-!
# Pullback on the full source of a bounded chart

A globally C¹ partial homeomorphism with globally C¹ inverse and bounded target
induces a continuous linear pullback on every `Lᵖ` space with `1 ≤ p ≤ ∞`
and an arbitrary real normed target. The scalar case is its specialization to `ℝ`.
The bound follows from change of variables at finite exponents and preservation
of null sets at infinity.
-/

@[expose] public section

namespace SobolevSpace.WeakChangeOfVariables

open MeasureTheory
open scoped ENNReal

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {E : OpenPartialHomeomorph ℝ^n ℝ^n}
  {F : Type*} [NormedAddCommGroup F]

/-- Pullback on `Lᵖ` through a bounded chart. -/
noncomputable def boundedPullbackLp
    (hE : ContDiff ℝ 1 E) (hEsymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    (u : Lp F p (domainMeasure n E.target)) : Lp F p (domainMeasure n E.source) :=
  (memLp_comp_partialHomeomorph_on_bounded_chart hE hEsymm hTarget
    (Lp.memLp u)).toLp (fun x ↦ u (E x))

/-- The pullback represents composition with the chart almost everywhere. -/
theorem boundedPullbackLp_apply_ae
    (hE : ContDiff ℝ 1 E) (hEsymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    (u : Lp F p (domainMeasure n E.target)) :
    ⇑(boundedPullbackLp hE hEsymm hTarget u) =ᵐ[domainMeasure n E.source]
      fun x ↦ u (E x) :=
  MemLp.coeFn_toLp _

variable [NormedSpace ℝ F]

/-- The change-of-variables bound bundles full-chart pullback as a continuous linear map. -/
noncomputable def boundedPullbackCLM
    (hE : ContDiff ℝ 1 E) (hEsymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) :
    Lp F p (domainMeasure n E.target) →L[ℝ] Lp F p (domainMeasure n E.source) := by
  let P := boundedPullbackLp (F := F) (p := p) hE hEsymm hTarget
  have hP := boundedPullbackLp_apply_ae (F := F) (p := p) hE hEsymm hTarget
  have hq := quasiMeasurePreserving_partialHomeomorph hE hEsymm
  let L : Lp F p (domainMeasure n E.target) →ₗ[ℝ]
      Lp F p (domainMeasure n E.source) :=
    { toFun := P
      map_add' := fun u v ↦ by
        apply Lp.ext
        filter_upwards [hP (u + v), hP u, hP v, Lp.coeFn_add (P u) (P v),
          hq.ae_eq_comp (Lp.coeFn_add u v)] with x huv hu hv hout hin
        exact huv.trans (hin.trans (by
          change u (E x) + v (E x) = (P u + P v) x
          rw [hout]
          exact congrArg₂ (· + ·) hu.symm hv.symm))
      map_smul' := fun c u ↦ by
        apply Lp.ext
        filter_upwards [hP (c • u), hP u, Lp.coeFn_smul c (P u),
          hq.ae_eq_comp (Lp.coeFn_smul c u)] with x hcu hu hout hin
        exact hcu.trans (hin.trans (by
          change c • u (E x) = (c • P u) x
          rw [hout]
          exact congrArg (c • ·) hu.symm)) }
  let C := boundedPullbackBound (p := p) hE hEsymm hTarget
  refine L.mkContinuous C.toReal fun u ↦ ?_
  change ‖boundedPullbackLp hE hEsymm hTarget u‖ ≤ C.toReal * ‖u‖
  rw [boundedPullbackLp, Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (boundedPullbackBound_ne_top hE hEsymm hTarget)
      (Lp.eLpNorm_ne_top u))
    (eLpNorm_comp_partialHomeomorph_le hE hEsymm hTarget (Lp.aestronglyMeasurable u))

/-- The bounded operator is the full-chart pullback. -/
@[simp]
theorem boundedPullbackCLM_apply
    (hE : ContDiff ℝ 1 E) (hEsymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target)
    (u : Lp F p (domainMeasure n E.target)) :
    boundedPullbackCLM hE hEsymm hTarget u =
      boundedPullbackLp hE hEsymm hTarget u := rfl

/-- The operator norm is controlled by the scalar inverse-Jacobian bound,
uniformly over all real normed targets. -/
theorem norm_boundedPullbackCLM_le
    (hE : ContDiff ℝ 1 E) (hEsymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) :
    ‖boundedPullbackCLM (F := F) (p := p) hE hEsymm hTarget‖ ≤
      (boundedPullbackBound (p := p) hE hEsymm hTarget).toReal := by
  apply ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg
  intro u
  rw [boundedPullbackCLM_apply, boundedPullbackLp, Lp.norm_toLp, Lp.norm_def,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (boundedPullbackBound_ne_top hE hEsymm hTarget)
      (Lp.eLpNorm_ne_top u))
    (eLpNorm_comp_partialHomeomorph_le hE hEsymm hTarget (Lp.aestronglyMeasurable u))

/-- At infinity the full-chart pullback is a contraction, independently of the Jacobian. -/
theorem norm_boundedPullbackCLM_top_le
    (hE : ContDiff ℝ 1 E) (hEsymm : ContDiff ℝ 1 E.symm)
    (hTarget : Bornology.IsBounded E.target) :
    ‖boundedPullbackCLM (F := F) (p := ∞) hE hEsymm hTarget‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul, boundedPullbackCLM_apply, boundedPullbackLp, Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u)
    (eLpNorm_comp_partialHomeomorph_top_le hE hEsymm (Lp.aestronglyMeasurable u))

end SobolevSpace.WeakChangeOfVariables
