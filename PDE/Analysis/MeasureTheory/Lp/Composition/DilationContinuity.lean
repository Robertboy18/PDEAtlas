/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation
public import PDE.Analysis.MeasureTheory.LpNorm
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import PDE.Analysis.MeasureTheory.Lp.Composition.DilationOrbit

/-!
# Strong continuity of scalar dilation on L²

Dilation orbits are continuous in `Lᵖ` for finite `p` (`tendsto_eLpNorm_comp_smul_sub`). On
factors bounded away from zero the change-of-variables bound is uniform, which gives joint
continuity in the input and the positive dilation factor.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Lp

variable {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))}
  [μ.IsAddHaarMeasure]

/-- Dilation on L² is jointly strongly continuous when factors stay above a positive bound. -/
theorem continuous_compSMul_Ici {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun ua : Lp ℝ 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) × Ici δ ↦
      compSMul μ 2 ua.2.val (hδ.trans_le ua.2.property).ne' ua.1) := by
  let C : ℝ≥0 := ⟨|(δ ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal, by positivity⟩
  refine continuous_prod_of_dense_continuous_lipschitzWith _ C dense_univ ?_ ?_
  · intro u _
    refine continuous_iff_continuousAt.2 fun a₀ ↦ ?_
    rw [ContinuousAt, tendsto_Lp_iff_tendsto_eLpNorm']
    have h := (tendsto_eLpNorm_comp_smul_sub (Lp.memLp u) (by norm_num) (by norm_num)
      (hδ.trans_le a₀.property).ne').comp (continuous_subtype_val.tendsto a₀)
    refine h.congr fun a ↦ ?_
    exact (eLpNorm_congr_ae ((coeFn_compSMul μ 2 _ _ u).sub (coeFn_compSMul μ 2 _ _ u))).symm
  · intro a
    let A : Lp ℝ 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →L[ℝ]
        Lp ℝ 2 μ := compSMul μ 2 a.val (hδ.trans_le a.property).ne'
    change LipschitzWith C A
    refine ContinuousLinearMap.lipschitzWith_of_opNorm_le
      (f := A) ?_
    refine ContinuousLinearMap.opNorm_le_bound A C.coe_nonneg ?_
    intro u
    change ‖compSMul μ 2 a.val (hδ.trans_le a.property).ne' u‖ ≤ C * ‖u‖
    rw [norm_compSMul]
    simp only [finrank_euclideanSpace_fin]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    change |(a.val ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal ≤
      |(δ ^ n)⁻¹| ^ (1 / (2 : ℝ≥0∞)).toReal
    have ha : 0 < a.val := hδ.trans_le a.property
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    gcongr
    exact a.property

end MeasureTheory.Lp
