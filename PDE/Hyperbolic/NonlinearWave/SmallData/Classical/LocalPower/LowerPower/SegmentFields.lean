/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.FreeField
public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.SegmentOperator
import CAS.ExactTactic

/-!
# Free waves and variable coefficients on characteristic segments

Both the free field and the coefficient parameter contain a time factor.
Their uniform bounds allow one existence interval for all spatial centers.
The coefficient has a different restriction weight from the free field;
the explicit scalar factor in the weighted implicit equation supplies the other
time factor of the retarded integral.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- The scalar spatial coordinate used in the radial one-dimensional equation. -/
def lineSpace : Cone →ᵇ ℝ :=
  mkOfCompact ⟨fun q ↦ coneSpace q 0,
    (EuclideanSpace.proj (0 : Fin 3)).continuous.comp continuous_subtype_val.snd⟩

/-- Evaluation of the scalar spatial coordinate. -/
theorem lineSpace_apply (q : Cone) : lineSpace q = coneSpace q 0 := rfl

/-- The initial point reached along a characteristic segment. -/
def segmentInitialDirection : (Cone × I) →ᵇ ℝ :=
  mkOfCompact ⟨fun p ↦ lineSpace p.1 + coneTime p.1 * (2 * (p.2 : ℝ) - 1),
    (lineSpace.continuous.comp continuous_fst).add
      ((continuous_subtype_val.fst.comp continuous_fst).mul
        ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub continuous_const))⟩

/-- The free zero-displacement one-dimensional wave on every subcone. -/
def segmentFreeField (h : C(ℝ, ℝ)) (p : ℝ × ℝ) : Cone →ᵇ ℝ :=
  p.1 • (timeWeight * partialIntegralCLM (volume : Measure I)
    (composeCompact h (constCLM (Cone × I) ℝ ℝ p.2 + p.1 • segmentInitialDirection)))

/-- The spatial reaction coefficient, with one time factor. -/
def segmentCoefficient (a : C(ℝ, ℝ)) (p : ℝ × ℝ) : Cone →ᵇ ℝ :=
  p.1 • composeCompact a (constCLM Cone ℝ ℝ p.2 + p.1 • lineSpace)

/-- Evaluation of the segment free field. -/
theorem segmentFreeField_apply (h : C(ℝ, ℝ)) (p : ℝ × ℝ) (q : Cone) :
    segmentFreeField h p q = (p.1 * coneTime q) *
      ∫ a : I, h (p.2 + p.1 * (lineSpace q + coneTime q * (2 * (a : ℝ) - 1))) := by
  simp only [segmentFreeField, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.mul_apply, partialIntegralCLM_apply, composeCompact_apply,
    BoundedContinuousFunction.add_apply, constCLM_apply, const_apply, timeWeight,
    segmentInitialDirection, mkOfCompact_apply, ContinuousMap.coe_mk, smul_eq_mul, mul_assoc]
  rfl

/-- Evaluation of the coefficient field. -/
theorem segmentCoefficient_apply (a : C(ℝ, ℝ)) (p : ℝ × ℝ) (q : Cone) :
    segmentCoefficient a p q = p.1 * a (p.2 + p.1 * lineSpace q) := by
  rfl

/-- Scalar restriction acts affinely on the spatial coordinate. -/
theorem lineSpace_descend (q r : Cone) :
    lineSpace (descend q r) = lineSpace q + coneTime q * lineSpace r := rfl

/-- C¹ velocity gives a C¹ free field with values in the uniform cone space. -/
theorem contDiff_segmentFreeField {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 1 (segmentFreeField ⟨h, hh.continuous⟩) := by
  have ha : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦
      constCLM (Cone × I) ℝ ℝ p.2 + p.1 • segmentInitialDirection) :=
    ((constCLM (Cone × I) ℝ ℝ).contDiff.comp contDiff_snd).add (contDiff_fst.smul contDiff_const)
  exact contDiff_fst.smul (contDiff_const.mul
    ((partialIntegralCLM (volume : Measure I)).contDiff.comp
      ((contDiff_composeCompact hh).comp ha)))

/-- C¹ coefficients give C¹ cone parameters. -/
theorem contDiff_segmentCoefficient {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) :
    ContDiff ℝ 1 (segmentCoefficient ⟨a, ha.continuous⟩) :=
  contDiff_fst.smul ((contDiff_composeCompact ha).comp
    (((constCLM Cone ℝ ℝ).contDiff.comp contDiff_snd).add (contDiff_fst.smul contDiff_const)))

/-- The free wave has the usual uniform bound by time times velocity. -/
theorem norm_segmentFreeField_le (h : ℝ →ᵇ ℝ) (p : ℝ × ℝ) :
    ‖segmentFreeField h.toContinuousMap p‖ ≤ |p.1| * ‖h‖ := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun q ↦ ?_
  rw [segmentFreeField_apply, norm_mul, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (coneTime_mem q).1]
  have havg : ‖∫ a : I, h (p.2 + p.1 *
      (lineSpace q + coneTime q * (2 * (a : ℝ) - 1)))‖ ≤ ‖h‖ := by
    simpa using (norm_integral_le_of_norm_le_const (μ := (volume : Measure I))
        (Filter.Eventually.of_forall fun a ↦ h.norm_coe_le_norm
          (p.2 + p.1 * (lineSpace q + coneTime q * (2 * (a : ℝ) - 1)))))
  calc
    _ ≤ (|p.1| * coneTime q) * ‖h‖ :=
      mul_le_mul_of_nonneg_left havg (mul_nonneg (abs_nonneg _) (coneTime_mem q).1)
    _ ≤ |p.1| * ‖h‖ := by
      calc
        _ ≤ (|p.1| * 1) * ‖h‖ := by
          gcongr
          exact (coneTime_mem q).2
        _ = _ := by rw [mul_one]

/-- The coefficient parameter is uniformly small on a short time interval. -/
theorem norm_segmentCoefficient_le (a : ℝ →ᵇ ℝ) (p : ℝ × ℝ) :
    ‖segmentCoefficient a.toContinuousMap p‖ ≤ |p.1| * ‖a‖ := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun q ↦ ?_
  rw [segmentCoefficient_apply, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (a.norm_coe_le_norm _) (abs_nonneg _)

/-- The free field agrees on nested characteristic cones. -/
theorem restrictCone_segmentFreeField (h : C(ℝ, ℝ)) (p : ℝ × ℝ) (q : Cone) :
    restrictCone q (segmentFreeField h p) =
      segmentFreeField h (p.1 * coneTime q, p.2 + p.1 * lineSpace q) := by
  ext r
  simp only [restrictCone_apply, segmentFreeField_apply, coneTime_descend, lineSpace_descend]
  congr 1
  · cas
  · congr 1
    funext a
    congr 1
    cas

/-- The coefficient parameter picks up one additional restriction factor. -/
theorem restrictCone_segmentCoefficient (a : C(ℝ, ℝ)) (p : ℝ × ℝ) (q : Cone) :
    coneTime q • restrictCone q (segmentCoefficient a p) =
      segmentCoefficient a (p.1 * coneTime q, p.2 + p.1 * lineSpace q) := by
  ext r
  simp only [BoundedContinuousFunction.smul_apply, restrictCone_apply,
    segmentCoefficient_apply, lineSpace_descend, smul_eq_mul]
  have he : p.2 + p.1 * (lineSpace q + coneTime q * lineSpace r) =
      p.2 + p.1 * lineSpace q + (p.1 * coneTime q) * lineSpace r := by cas
  rw [he]
  cas

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
