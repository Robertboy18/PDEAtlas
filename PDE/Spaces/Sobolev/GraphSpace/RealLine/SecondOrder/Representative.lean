/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder
public import PDE.Spaces.Sobolev.GraphSpace.Topology.SupportedBall

/-!
# Classical first derivatives of weak H² representatives

The lower-order graph and its first derivative graph give a continuous
classical derivative. Both pointwise bounds follow from the H¹ evaluation
estimate, without requiring a classical second derivative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Sobolev

namespace SobolevSpace.GraphSpace

/-- A continuous representative of a weak H² graph is C¹, with the function
and its first derivative bounded by twice the graph norm. -/
theorem contDiff_and_bounds_of_h2_representative
    (W : W^{2,2}(ℝ^1)) {w : ℝ → ℝ} (hw : Continuous w)
    (hW : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ)
      =ᵐ[volume] w) :
    ContDiff ℝ 1 w ∧ ∀ x, ‖w x‖ ≤ 2 * ‖W‖ ∧ ‖deriv w x‖ ≤ 2 * ‖W‖ := by
  let U := lowerOrderCLM (by decide : 1 ≤ 2) W
  let V := ∂[0] W
  have hUV : realLineCoordinateCLM (baseIndex 1 1) V =
      realLineCoordinateCLM (singleDerivIndex 1 0) U := by
    apply congrArg oneDimensionalPushforwardL2
    change (V : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
      (U : WkpAmbientOn 1 1 2 univ) (singleDerivIndex 1 0)
    simp only [V, U, partialDerivCLM, derivativeWordCLM_apply,
      derivativeWordIndex_singleton_baseIndex, lowerOrderCLM_apply,
      DerivIndex.castOrder_singleDerivIndex]
  have hUbase : realLineCoordinateCLM (baseIndex 1 1) U =
      oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) := by
    apply congrArg oneDimensionalPushforwardL2
    change (U : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
      (W : WkpAmbientOn 1 2 2 univ) (baseIndex 1 2)
    simp only [U, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex]
  have hUrep : realLineRepresentative U = w := by
    apply (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative U) hw).mp
    have ha := realLineCoordinate_ae_representative U
    rw [hUbase] at ha
    exact ha.symm.trans hW
  have hd (x : ℝ) : HasDerivAt w (realLineRepresentative V x) x := by
    rw [← hUrep]
    exact hasDerivAt_realLineRepresentative_of_h1_derivative U V hUV x
  have hdEq : deriv w = realLineRepresentative V := funext fun x ↦ (hd x).deriv
  refine ⟨contDiff_one_iff_deriv.mpr ⟨fun x ↦ (hd x).differentiableAt,
    hdEq ▸ continuous_realLineRepresentative V⟩, ?_⟩
  intro x
  constructor
  · rw [← hUrep]
    exact (norm_realLineRepresentative_le U x).trans
      (mul_le_mul_of_nonneg_left (norm_lowerOrderCLM_apply_le _ W) (by norm_num))
  · rw [hdEq]
    exact (norm_realLineRepresentative_le V x).trans
      (mul_le_mul_of_nonneg_left (norm_derivativeWordCLM_apply_le _ _ W) (by norm_num))

/-- The complete H² base ball bounds every continuous real-line representative
and its classical first derivative, although its metric is only the L² metric. -/
theorem contDiff_and_bounds_of_hkBaseBall
    {B : NNReal} {f : DerivLp 1 2 univ} (hf : f ∈ hkBaseBall 1 2 univ B)
    {w : ℝ → ℝ} (hw : Continuous w)
    (hrep : (oneDimensionalPushforwardL2 f : ℝ → ℝ) =ᵐ[volume] w) :
    ContDiff ℝ 1 w ∧ ∀ x, ‖w x‖ ≤ 2 * (B : ℝ) ∧ ‖deriv w x‖ ≤ 2 * (B : ℝ) := by
  obtain ⟨W, hW, rfl⟩ := hf
  obtain ⟨hreg, hbound⟩ := contDiff_and_bounds_of_h2_representative W hw hrep
  refine ⟨hreg, fun x ↦ ⟨(hbound x).1.trans ?_, (hbound x).2.trans ?_⟩⟩ <;>
    exact mul_le_mul_of_nonneg_left hW (by norm_num)

end SobolevSpace.GraphSpace
