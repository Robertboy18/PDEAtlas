/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Operator

/-!
# Characteristic segments in the compact cone

The one-dimensional retarded operator averages over characteristic segments.
We use the compact cone and its restriction maps, embedding the
segments along the first coordinate. Integration over the segment gains the
spatial derivative that is unavailable for arbitrary three-dimensional sources.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- A point of the segment joining the two one-dimensional characteristics. -/
def segmentRim (s a : I) : Cone :=
  ⟨((s : ℝ), EuclideanSpace.single (0 : Fin 3) ((1 - (s : ℝ)) * (2 * (a : ℝ) - 1))),
    s.2, by
      rw [PiLp.norm_single, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr s.2.2)]
      have ha : |2 * (a : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [a.2.1],
        by linarith [a.2.2]⟩
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr s.2.2)⟩

/-- Segment parametrization is continuous up to both characteristics. -/
theorem continuous_segmentRim : Continuous (fun p : I × I ↦ segmentRim p.1 p.2) := by
  apply Continuous.subtype_mk
  apply (continuous_subtype_val.comp continuous_fst).prodMk
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp
  refine continuous_pi fun i ↦ ?_
  by_cases hi : i = 0
  · subst i
    simp only [Pi.single_eq_same]
    fun_prop
  · simpa [Pi.single_apply, hi] using (continuous_const : Continuous (fun _ : I × I ↦ (0 : ℝ)))

/-- Evaluation on the characteristic segment of every subcone. -/
def segmentBoundary : (Cone →ᵇ ℝ) →L[ℝ] (((Cone × I) × I) →ᵇ ℝ) :=
  compContinuousCLM ℝ ℝ
    ⟨fun p ↦ descend p.1.1 (segmentRim p.1.2 p.2),
      continuous_descend.comp
        (continuous_fst.fst.prodMk
          (continuous_segmentRim.comp (continuous_fst.snd.prodMk continuous_snd)))⟩

/-- The normalized one-dimensional retarded integral on the cone space. -/
def segmentOperator : (Cone →ᵇ ℝ) →L[ℝ] (Cone →ᵇ ℝ) :=
  ((ContinuousLinearMap.mul ℝ (Cone →ᵇ ℝ)) timeSquare).comp
    ((partialIntegralCLM (volume : Measure I)).comp
      (((ContinuousLinearMap.mul ℝ ((Cone × I) →ᵇ ℝ)) radiusWeight).comp
        ((partialIntegralCLM (volume : Measure I)).comp segmentBoundary)))

/-- The retarded segment operator is the normalized characteristic double integral. -/
theorem segmentOperator_apply (w : Cone →ᵇ ℝ) (q : Cone) :
    segmentOperator w q = coneTime q ^ 2 *
      ∫ s : I, (1 - (s : ℝ)) * ∫ a : I, w (descend q (segmentRim s a)) := by
  simp only [segmentOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', BoundedContinuousFunction.mul_apply,
    partialIntegralCLM_apply, timeSquare, radiusWeight, mkOfCompact_apply,
    ContinuousMap.coe_mk, segmentBoundary, compContinuousCLM_apply, compContinuous_apply]
  rfl

/-- Restricting the retarded segment operator contributes the square of the time scale. -/
theorem segmentOperator_descend (q r : Cone) (w : Cone →ᵇ ℝ) :
    segmentOperator w (descend q r) = coneTime q ^ 2 * segmentOperator (restrictCone q w) r := by
  simp only [segmentOperator_apply, coneTime_descend, descend_assoc, restrictCone_apply,
    mul_pow, mul_assoc]

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
