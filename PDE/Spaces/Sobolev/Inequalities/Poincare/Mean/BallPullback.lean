/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.Scaling
import PDE.Spaces.Sobolev.Calculus.Pullback.FirstOrder.LocalizedPullback

/-!
# Sobolev pullback from a ball to the unit ball

The affine map `y ↦ x + r y` pulls arbitrary `W¹ᵖ` data back to the unit ball.
The weak chain rule constructs the pulled-back Sobolev element and identifies
its weak gradient as `r Du(x + r y)`. This applies to every `1 ≤ p ≤ ∞`.
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace.MeanScaling

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weak derivative of an affine pullback is the corresponding pulled-back derivative
multiplied by the radius. The input is an arbitrary Sobolev element. -/
theorem hasWeakDerivativeOn_comp_ballHomeomorph (x : ℝ^n) {r : ℝ} (hr : 0 < r)
    (U : W^{1,p}(ball x r)) (i : Fin n) :
    HasWeakDerivativeOn (ball (0 : ℝ^n) 1) [i]
      (fun y ↦ wkpBaseCoordinateCLM U (ballHomeomorph x hr y))
      (fun y ↦ r * (U : WkpAmbientOn n 1 p (ball x r))
        (singleDerivIndex n i) (ballHomeomorph x hr y)) := by
  let E := (ballHomeomorph x hr).toOpenPartialHomeomorphOfImageEq
    (ball 0 1) isOpen_ball (ball x r) (image_ball x hr)
  have hE : ContDiff ℝ 1 (fun y ↦ E y) := by
    change ContDiff ℝ 1 (fun y : ℝ^n ↦ x + r • y)
    fun_prop
  have hEsymm : ContDiff ℝ 1 (fun y ↦ E.symm y) := by
    change ContDiff ℝ 1 (fun y ↦ (ballHomeomorph x hr).symm y)
    simp only [ballHomeomorph_symm_apply]
    fun_prop
  have hweak (j : Fin n) :
      HasWeakDerivativeOn E.target [j] (wkpBaseCoordinateCLM U : ℝ^n → ℝ)
        ((U : WkpAmbientOn n 1 p (ball x r)) (singleDerivIndex n j)) := by
    simpa only [firstDerivIndex_one, wkpBaseCoordinateCLM_apply, E,
      Homeomorph.toOpenPartialHomeomorphOfImageEq_target] using
      U.property.hasWeakDerivativeOn_first (by decide) j
  have h := WeakChangeOfVariables.hasWeakDerivativeOn_comp_partialHomeomorph_W1_of_memLp
    (Approximation.standardMollifier n) hE hEsymm
    (measure_ball_lt_top.ne) (Lp.memLp (wkpBaseCoordinateCLM U))
    (fun j ↦ Lp.memLp ((U : WkpAmbientOn n 1 p (ball x r))
      (singleDerivIndex n j))) hweak i
  have hderiv (y : ℝ^n) :
      fderiv ℝ (fun z ↦ E z) y = r • ContinuousLinearMap.id ℝ (ℝ^n) :=
    (((hasFDerivAt_id y).const_smul r).const_add x).fderiv
  simp only [partialDeriv, hderiv, smul_apply, ContinuousLinearMap.id_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  simpa only [mul_comm,
    E, Homeomorph.toOpenPartialHomeomorphOfImageEq_source,
    Homeomorph.toOpenPartialHomeomorphOfImageEq_apply] using h

/-- An arbitrary Sobolev function on a ball has the affine pullback to the unit
ball, with its base function and vector-valued weak gradient identified almost everywhere. -/
theorem exists_ballPullback (x : ℝ^n) {r : ℝ} (hr : 0 < r)
    (U : W^{1,p}(ball x r)) :
    ∃ V : W^{1,p}(ball (0 : ℝ^n) 1),
      (wkpBaseCoordinateCLM V : ℝ^n → ℝ) =ᵐ[domainMeasure n (ball 0 1)]
        (fun y ↦ wkpBaseCoordinateCLM U (ballHomeomorph x hr y)) ∧
      (∇ V : ℝ^n → ℝ^n) =ᵐ[domainMeasure n (ball 0 1)]
        (fun y ↦ r • ∇ U (ballHomeomorph x hr y)) := by
  let f : ℝ^n → ℝ := fun y ↦ wkpBaseCoordinateCLM U (ballHomeomorph x hr y)
  let d : DerivIndex n 1 → ℝ^n → ℝ :=
    firstOrderRows f fun i y ↦
      r * (U : WkpAmbientOn n 1 p (ball x r))
        (singleDerivIndex n i) (ballHomeomorph x hr y)
  have hbase : d (baseIndex n 1) = f := by simp [d]
  have hmem : ∀ a, MemLp (d a) p (domainMeasure n (ball (0 : ℝ^n) 1)) := by
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · simpa only [d, firstOrderRows_baseIndex] using
        memLp_comp_ballHomeomorph x hr (Lp.memLp (wkpBaseCoordinateCLM U))
    · simpa only [d, firstOrderRows_singleDerivIndex] using
        (memLp_comp_ballHomeomorph x hr (Lp.memLp
          ((U : WkpAmbientOn n 1 p (ball x r)) (singleDerivIndex n i)))).const_mul r
  have hweak : ∀ a, HasWeakDerivativeOn (ball (0 : ℝ^n) 1) a.toList f (d a) := by
    intro a
    rcases a.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨i, rfl⟩
    · have hf : MemLp f p (domainMeasure n (ball (0 : ℝ^n) 1)) := hbase ▸ hmem _
      simpa only [d, firstOrderRows_baseIndex, baseIndex_toList] using
        hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain hf (Fact.out : 1 ≤ p))
    · simpa only [d, f, firstOrderRows_singleDerivIndex, singleDerivIndex_toList]
        using hasWeakDerivativeOn_comp_ballHomeomorph x hr U i
  let V := mkWkpSpaceOnOfWeakDerivatives f d hbase hmem hweak
  have hrow (a : DerivIndex n 1) :
      ((V : WkpAmbientOn n 1 p (ball (0 : ℝ^n) 1)) a : ℝ^n → ℝ)
        =ᵐ[domainMeasure n (ball 0 1)] d a :=
    mkWkpSpaceOnOfWeakDerivatives_apply_ae f d hbase hmem hweak a
  refine ⟨V, ?_, ?_⟩
  · simpa only [hbase, f, wkpBaseCoordinateCLM_apply] using hrow (baseIndex n 1)
  · have hrows := ae_all_iff.2 fun i ↦ hrow (singleDerivIndex n i)
    have hU := (quasiMeasurePreserving_ballHomeomorph x hr).ae
      (wkpGradientCLM_apply_ae U)
    filter_upwards [wkpGradientCLM_apply_ae V, hrows, hU] with y hy hd hu
    apply PiLp.ext
    intro i
    simp only [hy i, hd i, d, firstOrderRows_singleDerivIndex, PiLp.smul_apply,
      smul_eq_mul, hu i]

/-- The affine Sobolev pullback has the exact scaling of both its centered function norm
and its weak gradient norm. The same strictly positive volume factor occurs in both. -/
theorem exists_ballPullback_scaling (x : ℝ^n) {r : ℝ} (hr : 0 < r)
    (U : W^{1,p}(ball x r)) :
    ∃ V : W^{1,p}(ball (0 : ℝ^n) 1),
      (eLpNorm (fun y ↦ wkpBaseCoordinateCLM V y -
        ⨍ z, wkpBaseCoordinateCLM V z ∂domainMeasure n (ball 0 1))
          p (domainMeasure n (ball 0 1))).toReal =
        normFactor n r p * (eLpNorm (fun y ↦ wkpBaseCoordinateCLM U y -
          ⨍ z, wkpBaseCoordinateCLM U z ∂domainMeasure n (ball x r))
            p (domainMeasure n (ball x r))).toReal ∧
      ‖∇ V‖ = normFactor n r p * (r * ‖∇ U‖) := by
  obtain ⟨V, hbase, hgrad⟩ := exists_ballPullback x hr U
  refine ⟨V, ?_, ?_⟩
  · have havg :
        (⨍ z, wkpBaseCoordinateCLM V z ∂domainMeasure n (ball 0 1)) =
          ⨍ z, wkpBaseCoordinateCLM U z ∂domainMeasure n (ball x r) :=
      (average_congr hbase).trans (average_comp_ballHomeomorph x hr _)
    have hcenter :
        (fun y ↦ wkpBaseCoordinateCLM V y -
          ⨍ z, wkpBaseCoordinateCLM V z ∂domainMeasure n (ball 0 1))
            =ᵐ[domainMeasure n (ball 0 1)]
        (fun y ↦ wkpBaseCoordinateCLM U (ballHomeomorph x hr y) -
          ⨍ z, wkpBaseCoordinateCLM U z ∂domainMeasure n (ball x r)) := by
      filter_upwards [hbase] with y hy
      rw [hy, havg]
    rw [eLpNorm_congr_ae hcenter]
    exact eLpNorm_comp_ballHomeomorph x hr p (fun y ↦ wkpBaseCoordinateCLM U y -
      ⨍ z, wkpBaseCoordinateCLM U z ∂domainMeasure n (ball x r))
  · rw [Lp.norm_def, eLpNorm_congr_ae hgrad]
    change (eLpNorm (r • (fun y ↦ ∇ U (ballHomeomorph x hr y)))
      p (domainMeasure n (ball 0 1))).toReal = _
    rw [eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_of_nonneg hr.le,
      eLpNorm_comp_ballHomeomorph x hr p, ← Lp.norm_def]
    ring

end SobolevSpace.GraphSpace.MeanScaling
