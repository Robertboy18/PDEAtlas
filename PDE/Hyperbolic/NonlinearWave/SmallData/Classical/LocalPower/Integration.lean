/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integration in the compact cone parameter spaces

Integration over the angular and normalized time variables is a bounded
linear map in the uniform norm. Partial integration retains continuity in
the remaining compact parameters.
-/

@[expose] public noncomputable section

open MeasureTheory Set BoundedContinuousFunction

namespace WaveEquation.SmallData.Classical.LocalPower

variable {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [OpensMeasurableSpace α] [TopologicalSpace β]

/-- Integration of real bounded continuous functions against a finite measure,
as a continuous linear map. -/
def integralCLM (μ : Measure α) [IsFiniteMeasure μ] : (α →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ∫ a, f a ∂μ
      map_add' := fun f g ↦ integral_add (f.integrable μ) (g.integrable μ)
      map_smul' := fun c f ↦ integral_smul c f }
    (μ.real univ) fun f ↦ f.norm_integral_le_mul_norm μ

/-- Evaluation of the integration map. -/
@[simp] theorem integralCLM_apply (μ : Measure α) [IsFiniteMeasure μ] (f : α →ᵇ ℝ) :
    integralCLM μ f = ∫ a, f a ∂μ := rfl

variable [CompactSpace α] [CompactSpace β]

/-- Integrate out the second variable of a continuous function on a compact
product. -/
def partialIntegral (μ : Measure α) [IsFiniteMeasure μ]
    (f : (β × α) →ᵇ ℝ) : β →ᵇ ℝ :=
  mkOfCompact
    ⟨fun b ↦ integralCLM μ (mkOfCompact (f.toContinuousMap.curry b)),
      (integralCLM μ).continuous.comp
        ((ContinuousMap.isometryEquivBoundedOfCompact α ℝ).continuous.comp
          f.toContinuousMap.curry.continuous)⟩

/-- Partial integration agrees with the usual scalar integral. -/
@[simp] theorem partialIntegral_apply (μ : Measure α) [IsFiniteMeasure μ]
    (f : (β × α) →ᵇ ℝ) (b : β) :
    partialIntegral μ f b = ∫ a, f (b, a) ∂μ := rfl

/-- Partial integration is bounded by the mass of the measure. -/
theorem norm_partialIntegral_le (μ : Measure α) [IsFiniteMeasure μ] (f : (β × α) →ᵇ ℝ) :
    ‖partialIntegral μ f‖ ≤ μ.real univ * ‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (measureReal_nonneg) (norm_nonneg f))).mpr
  intro b
  simpa only [partialIntegral_apply, mul_comm] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := fun a ↦ f (b, a))
      (Filter.Eventually.of_forall fun a ↦ f.norm_coe_le_norm (b, a)))

/-- Partial integration is a continuous linear map between the uniform
function spaces. -/
def partialIntegralCLM (μ : Measure α) [IsFiniteMeasure μ] :
    ((β × α) →ᵇ ℝ) →L[ℝ] (β →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := partialIntegral μ
      map_add' := fun f g ↦ by
        ext b
        exact integral_add
          ((mkOfCompact (f.toContinuousMap.curry b)).integrable μ)
          ((mkOfCompact (g.toContinuousMap.curry b)).integrable μ)
      map_smul' := fun c f ↦ by
        ext b
        exact integral_smul c (fun a ↦ f (b, a)) }
    (μ.real univ) (norm_partialIntegral_le μ)

/-- Evaluation of partial integration as a linear map. -/
@[simp] theorem partialIntegralCLM_apply (μ : Measure α) [IsFiniteMeasure μ]
    (f : (β × α) →ᵇ ℝ) (b : β) :
    partialIntegralCLM μ f b = ∫ a, f (b, a) ∂μ := rfl

end WaveEquation.SmallData.Classical.LocalPower
