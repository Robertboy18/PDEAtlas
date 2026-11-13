/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Cone
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Integration

/-!
# The normalized three-dimensional Duhamel operator

Angular averaging and integration over normalized time give a bounded
linear operator on continuous cone fields. Its covariance under cone
restriction is the identity needed to obtain one spacetime solution from
the parameterized implicit solutions.
-/

@[expose] public noncomputable section

open Set MeasureTheory BoundedContinuousFunction PDE.Analysis
open scoped unitInterval

namespace WaveEquation.SmallData.Classical.LocalPower

/-- The angular domain used by the Kirchhoff formula. -/
abbrev Direction := Metric.sphere (0 : ℝ^3) 1

/-- Restriction of a continuous field to a smaller backward cone. -/
def restrictCone (q : Cone) : (Cone →ᵇ ℝ) →L[ℝ] (Cone →ᵇ ℝ) :=
  compContinuousCLM ℝ ℝ
    ⟨descend q, continuous_descend.comp (continuous_const.prodMk continuous_id)⟩

/-- Cone restriction is literal composition with the affine restriction map. -/
@[simp] theorem restrictCone_apply (q : Cone) (w : Cone →ᵇ ℝ) (r : Cone) :
    restrictCone q w r = w (descend q r) := rfl

/-- Restriction cannot increase the uniform norm. -/
theorem norm_restrictCone_le (q : Cone) (w : Cone →ᵇ ℝ) :
    ‖restrictCone q w‖ ≤ ‖w‖ :=
  norm_compContinuous_le _ _

/-- Evaluate a cone field on every retarded spherical boundary. -/
def retardedBoundary : (Cone →ᵇ ℝ) →L[ℝ] (((Cone × I) × Direction) →ᵇ ℝ) :=
  compContinuousCLM ℝ ℝ
    ⟨fun p ↦ descend p.1.1 (rim p.1.2 p.2),
      continuous_descend.comp
        ((continuous_fst.fst).prodMk
          (continuous_rim.comp (continuous_fst.snd.prodMk continuous_snd)))⟩

/-- The normalized angular average of the retarded cone field. -/
def retardedAverage : (Cone →ᵇ ℝ) →L[ℝ] ((Cone × I) →ᵇ ℝ) :=
  (unitSphereArea 3)⁻¹ •
    (partialIntegralCLM ((volume : Measure (ℝ^3)).toSphere)).comp retardedBoundary

/-- The radius factor inside the normalized time integral. -/
def radiusWeight : (Cone × I) →ᵇ ℝ :=
  mkOfCompact ⟨fun p ↦ 1 - (p.2 : ℝ),
    continuous_const.sub (continuous_subtype_val.comp continuous_snd)⟩

/-- The square of the terminal time of each normalized subcone. -/
def timeSquare : Cone →ᵇ ℝ :=
  mkOfCompact ⟨fun q ↦ coneTime q ^ 2, continuous_subtype_val.fst.pow 2⟩

/-- The normalized Duhamel operator, with Kirchhoff's angular measure
and the retarded radius weight. -/
def duhamelOperator : (Cone →ᵇ ℝ) →L[ℝ] (Cone →ᵇ ℝ) :=
  ((ContinuousLinearMap.mul ℝ (Cone →ᵇ ℝ)) timeSquare).comp
    ((partialIntegralCLM (volume : Measure I)).comp
      (((ContinuousLinearMap.mul ℝ ((Cone × I) →ᵇ ℝ)) radiusWeight).comp
        retardedAverage))

/-- Evaluation of the cone operator as two ordinary integrals. -/
theorem duhamelOperator_apply (w : Cone →ᵇ ℝ) (q : Cone) :
    duhamelOperator w q = coneTime q ^ 2 * ∫ s : I, (1 - (s : ℝ)) * ((∫ ω : Direction,
      w (descend q (rim s ω)) ∂((volume : Measure (ℝ^3)).toSphere)) / unitSphereArea 3) := by
  simp only [duhamelOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply', BoundedContinuousFunction.mul_apply,
    partialIntegralCLM_apply, retardedAverage, _root_.smul_apply,
    BoundedContinuousFunction.smul_apply, smul_eq_mul]
  simp only [timeSquare, radiusWeight, mkOfCompact_apply, ContinuousMap.coe_mk,
    retardedBoundary, compContinuousCLM_apply, compContinuous_apply,
    ContinuousMap.coe_mk, div_eq_mul_inv, mul_comm]
  rfl

/-- Rescaling a backward cone contributes exactly the square of its time
scale to Duhamel's operator. -/
theorem duhamelOperator_descend (q r : Cone) (w : Cone →ᵇ ℝ) :
    duhamelOperator w (descend q r) = coneTime q ^ 2 * duhamelOperator (restrictCone q w) r := by
  simp only [duhamelOperator_apply, coneTime_descend, descend_assoc, restrictCone_apply,
    mul_pow, mul_assoc]

end WaveEquation.SmallData.Classical.LocalPower
