/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder
import CAS.ExactTactic

/-!
# H² multiplication from an H¹ graph for the multiplier derivative

The multiplier itself need not belong to L². A bounded C¹ multiplier whose
first derivative has an H¹ graph preserves H². The proof constructs the
two H¹ graphs in the Leibniz formula and assembles the second Sobolev order.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Sobolev

namespace SobolevSpace.GraphSpace

private theorem multiplier_coordinate_bound
    (V : W^{1,2}(ℝ^1)) {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    (M + N) * ‖realLineCoordinateCLM (baseIndex 1 1) V‖ +
      M * ‖realLineCoordinateCLM (singleDerivIndex 1 0) V‖ ≤ (2 * M + N) * ‖V‖ := by
  apply (add_le_add
    (mul_le_mul_of_nonneg_left (norm_realLineCoordinateCLM_le _ V) (add_nonneg hM hN))
    (mul_le_mul_of_nonneg_left (norm_realLineCoordinateCLM_le _ V) hM)).trans
  apply le_of_eq
  cas

/-- A bounded C¹ multiplier with H¹ first derivative maps compatible H¹
graphs into an H² graph. The supplied first derivative graph is used
to construct the highest weak derivative. -/
theorem exists_h2_mul_of_h1_multiplier_derivative
    (U V R : W^{1,2}(ℝ^1))
    (hV : realLineCoordinateCLM (baseIndex 1 1) V =
      realLineCoordinateCLM (singleDerivIndex 1 0) U)
    {m : ℝ → ℝ} {M N : ℝ} (hm : Continuous m)
    (hmderiv : ∀ x, HasDerivAt m (realLineRepresentative R x) x)
    (hbound : ∀ x, ‖m x‖ ≤ M)
    (hbound' : ∀ x, ‖realLineRepresentative R x‖ ≤ N) :
    ∃ W : W^{2,2}(ℝ^1),
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ realLineRepresentative U x * m x) ∧
      ‖W‖ ≤ succOrderAssemblyNormBound 1 1 *
        ((2 * M + N) * (‖U‖ + ‖V‖) + (4 * ‖U‖ + 2 * ‖V‖) * ‖R‖) := by
  have hM : 0 ≤ M := (norm_nonneg (m 0)).trans (hbound 0)
  have hN : 0 ≤ N := (norm_nonneg (realLineRepresentative R 0)).trans (hbound' 0)
  obtain ⟨S, hSnorm, hSrep, hSrow⟩ := exists_h1_mul_of_bounded_c1 U hm
    (continuous_realLineRepresentative R) hmderiv hbound hbound'
  obtain ⟨P, hPnorm, hPrep, _hProw⟩ := exists_h1_mul_of_bounded_c1 V hm
    (continuous_realLineRepresentative R) hmderiv hbound hbound'
  obtain ⟨Q, hQnorm, hQrep, _hQrow⟩ := exists_h1_mul_of_bounded_c1 R
    (continuous_realLineRepresentative U) (continuous_realLineRepresentative V)
    (hasDerivAt_realLineRepresentative_of_h1_derivative U V hV)
    (norm_realLineRepresentative_le U) (norm_realLineRepresentative_le V)
  have hcompat : realLineCoordinateCLM (baseIndex 1 1) (P + Q) =
      realLineCoordinateCLM (singleDerivIndex 1 0) S := by
    apply Lp.ext
    have hVrep := realLineCoordinate_ae_representative V
    rw [hV] at hVrep
    filter_upwards [realLineCoordinate_ae_representative (P + Q), hSrow, hVrep]
      with x hp hs hv
    rw [hp, hs, realLineRepresentative_add, Pi.add_apply, hPrep, hQrep, hv]
    cas
  obtain ⟨W, hWbase, hWnorm⟩ := exists_h2_of_realLine_h1_derivative S (P + Q) hcompat
  refine ⟨W, ?_, ?_⟩
  · rw [hWbase]
    exact (realLineCoordinate_ae_representative S).trans (Filter.EventuallyEq.of_eq hSrep)
  · apply hWnorm.trans
    apply mul_le_mul_of_nonneg_left _ succOrderAssemblyNormBound_nonneg
    have hS := hSnorm.trans (multiplier_coordinate_bound U hM hN)
    have hP := hPnorm.trans (multiplier_coordinate_bound V hM hN)
    have hQ := hQnorm.trans (multiplier_coordinate_bound R
      (mul_nonneg (by norm_num) (norm_nonneg U))
      (mul_nonneg (by norm_num) (norm_nonneg V)))
    apply (add_le_add hS ((norm_add_le P Q).trans (add_le_add hP hQ))).trans
    apply le_of_eq
    cas

end SobolevSpace.GraphSpace
