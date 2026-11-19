/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.Continuation.WeakSource
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Multiplier.SecondOrder

/-!
# The higher Sobolev source in the first derivative equation

For a fixed H² vorticity `W`, the source `W H Q` preserves H² in the
unknown first derivative `Q`. Its bound uses only the existing H² norm of
`W`. Hilbert commutation constructs the two H¹ rows of `H Q`, and the weak
multiplier theorem constructs their product with `W`.

These are the spatial estimates for solving the linear first derivative
equation along the already constructed local flow.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Sobolev
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The source `ω Hq` of the first derivative equation, as its canonical L² class. -/
def firstDerivativeSource (W Q : W^{2,2}(ℝ^1)) : Lp ℝ 2 (volume : Measure ℝ) :=
  realLineMultiplierCLM (lowerOrderCLM (by decide : 1 ≤ 2) W) •
    realHilbertTransformL2 (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM Q))

/-- The derivative source preserves H², with a bound depending only on the
existing H² coefficient. No classical second derivative of the coefficient
is assumed. -/
theorem exists_h2_firstDerivativeSource (W Q : W^{2,2}(ℝ^1)) :
    ∃ S : W^{2,2}(ℝ^1),
      oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM S) = firstDerivativeSource W Q ∧
      ‖S‖ ≤ (36 * succOrderAssemblyNormBound 1 1) * ‖W‖ * ‖Q‖ := by
  let U := lowerOrderCLM (by decide : 1 ≤ 2) W
  let R := partialDerivCLM 0 W
  let P := realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) Q)
  let D := realHilbertH1 (partialDerivCLM 0 Q)
  have hPD : realLineCoordinateCLM (baseIndex 1 1) D =
      realLineCoordinateCLM (singleDerivIndex 1 0) P := by
    simp only [D, P, realLineCoordinateCLM_realHilbertH1_base,
      realLineCoordinateCLM_realHilbertH1_single, realLineCoordinateCLM_partialDeriv_h2_base]
  have hU : ‖U‖ ≤ ‖W‖ := norm_lowerOrderCLM_apply_le _ W
  have hR : ‖R‖ ≤ ‖W‖ := norm_partialDeriv_le 0 W
  have hP : ‖P‖ ≤ 2 * ‖Q‖ :=
    (norm_realHilbertH1_le _).trans
      (mul_le_mul_of_nonneg_left (norm_lowerOrderCLM_apply_le _ Q) (by norm_num))
  have hD : ‖D‖ ≤ 2 * ‖Q‖ :=
    (norm_realHilbertH1_le _).trans
      (mul_le_mul_of_nonneg_left (norm_partialDeriv_le 0 Q) (by norm_num))
  obtain ⟨S, hSrep, hSnorm⟩ := exists_h2_mul_of_h1_multiplier_derivative
    P D R hPD (continuous_realLineRepresentative U)
    (hasDerivAt_realLineRepresentative_of_h1_derivative U R
      (realLineCoordinateCLM_partialDeriv_h2_base W))
    (fun x ↦ (norm_realLineRepresentative_le U x).trans
      (mul_le_mul_of_nonneg_left hU (by norm_num)))
    (fun x ↦ (norm_realLineRepresentative_le R x).trans
      (mul_le_mul_of_nonneg_left hR (by norm_num)))
  refine ⟨S, ?_, hSnorm.trans ?_⟩
  · apply Lp.ext
    have hPbase := realLineCoordinate_ae_representative P
    simp only [P, realLineCoordinateCLM_realHilbertH1_base,
      realLineCoordinateCLM_base_lowerOrder] at hPbase
    filter_upwards [hSrep, hPbase, realLineMultiplierCLM_ae U,
      Lp.coeFn_lpSMul (r := 2) (realLineMultiplierCLM U)
        (realHilbertTransformL2 (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM Q)))]
      with x hs hp hu hm
    change _ = (realLineMultiplierCLM U •
      realHilbertTransformL2 (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM Q))) x
    rw [hs, hm]
    simp only [smul_eq_mul, Pi.mul_apply, hu, hp]
    ring
  · calc
      _ ≤ succOrderAssemblyNormBound 1 1 *
          ((2 * (2 * ‖W‖) + 2 * ‖W‖) * (2 * ‖Q‖ + 2 * ‖Q‖) +
            (4 * (2 * ‖Q‖) + 2 * (2 * ‖Q‖)) * ‖W‖) := by
        gcongr
        exact succOrderAssemblyNormBound_nonneg
      _ = _ := by ring

private theorem h2_eq_of_real_base_eq {U V : W^{2,2}(ℝ^1)}
    (h : oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM U) =
      oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM V)) : U = V :=
  wkpBaseCoordinateCLM_injective isOpen_univ (oneDimensionalPushforwardL2.injective h)

private def firstDerivativeSourceH2Lift (W Q : W^{2,2}(ℝ^1)) : W^{2,2}(ℝ^1) :=
  (exists_h2_firstDerivativeSource W Q).choose

private theorem firstDerivativeSourceH2Lift_base (W Q : W^{2,2}(ℝ^1)) :
    oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM (firstDerivativeSourceH2Lift W Q)) =
      firstDerivativeSource W Q :=
  (exists_h2_firstDerivativeSource W Q).choose_spec.1

private theorem norm_firstDerivativeSourceH2Lift_le (W Q : W^{2,2}(ℝ^1)) :
    ‖firstDerivativeSourceH2Lift W Q‖ ≤
      (36 * succOrderAssemblyNormBound 1 1) * ‖W‖ * ‖Q‖ :=
  (exists_h2_firstDerivativeSource W Q).choose_spec.2

private def firstDerivativeSourceH2Linear :
    W^{2,2}(ℝ^1) →ₗ[ℝ] W^{2,2}(ℝ^1) →ₗ[ℝ] W^{2,2}(ℝ^1) where
  toFun W :=
    { toFun := firstDerivativeSourceH2Lift W
      map_add' := fun Q V ↦ by
        apply h2_eq_of_real_base_eq
        simp only [map_add, firstDerivativeSourceH2Lift_base, firstDerivativeSource, Lp.add_smul]
      map_smul' := fun a Q ↦ by
        apply h2_eq_of_real_base_eq
        simp only [map_smul, firstDerivativeSourceH2Lift_base, firstDerivativeSource,
          Lp.smul_comm, RingHom.id_apply] }
  map_add' W V := by
    apply LinearMap.ext
    intro Q
    change firstDerivativeSourceH2Lift (W + V) Q =
      firstDerivativeSourceH2Lift W Q + firstDerivativeSourceH2Lift V Q
    apply h2_eq_of_real_base_eq
    simp only [map_add, firstDerivativeSourceH2Lift_base, firstDerivativeSource, Lp.smul_add]
  map_smul' a W := by
    apply LinearMap.ext
    intro Q
    change firstDerivativeSourceH2Lift (a • W) Q = a • firstDerivativeSourceH2Lift W Q
    apply h2_eq_of_real_base_eq
    simp only [map_smul, firstDerivativeSourceH2Lift_base, firstDerivativeSource, Lp.smul_assoc]

/-- The weak product construction gives a bounded bilinear lift of the L² source. -/
theorem exists_firstDerivativeSourceH2CLM :
    ∃ M : W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1),
      (∀ W Q, oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM (M W Q)) =
        firstDerivativeSource W Q) ∧
      ∀ W Q, ‖M W Q‖ ≤ (36 * succOrderAssemblyNormBound 1 1) * ‖W‖ * ‖Q‖ := by
  exact ⟨LinearMap.mkContinuous₂ firstDerivativeSourceH2Linear
    (36 * succOrderAssemblyNormBound 1 1) norm_firstDerivativeSourceH2Lift_le,
    firstDerivativeSourceH2Lift_base, norm_firstDerivativeSourceH2Lift_le⟩

/-- The derivative source as a bounded bilinear map on the canonical H² graph.
For each fixed vorticity, this is a globally Lipschitz linear field in
the unknown first derivative. -/
def firstDerivativeSourceH2CLM :
    W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1) :=
  exists_firstDerivativeSourceH2CLM.choose

/-- The H² source has exactly the canonical L² source as its base row. -/
theorem firstDerivativeSourceH2CLM_base (W Q : W^{2,2}(ℝ^1)) :
    oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM (firstDerivativeSourceH2CLM W Q)) =
      firstDerivativeSource W Q :=
  exists_firstDerivativeSourceH2CLM.choose_spec.1 W Q

/-- The source bound loses no spatial derivative of the existing coefficient. -/
theorem norm_firstDerivativeSourceH2CLM_apply_le (W Q : W^{2,2}(ℝ^1)) :
    ‖firstDerivativeSourceH2CLM W Q‖ ≤
      (36 * succOrderAssemblyNormBound 1 1) * ‖W‖ * ‖Q‖ :=
  exists_firstDerivativeSourceH2CLM.choose_spec.2 W Q

/-- The H² source represents the classical product of the vorticity and
the continuous Hilbert transform of the unknown derivative. -/
theorem realLineRepresentative_firstDerivativeSourceH2CLM (W Q : W^{2,2}(ℝ^1)) :
    realLineRepresentative
        (lowerOrderCLM (by decide : 1 ≤ 2) (firstDerivativeSourceH2CLM W Q)) =
      fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) x *
        realLineRepresentative (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) Q)) x := by
  apply (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative _)
    ((continuous_realLineRepresentative _).mul (continuous_realLineRepresentative _))).mp
  have hbase := realLineRepresentative_lowerOrder_ae (firstDerivativeSourceH2CLM W Q)
  rw [firstDerivativeSourceH2CLM_base] at hbase
  apply hbase.symm.trans
  have hH := realLineCoordinate_ae_representative
    (realHilbertH1 (lowerOrderCLM (by decide : 1 ≤ 2) Q))
  rw [realLineCoordinateCLM_realHilbertH1_base, realLineCoordinateCLM_base_lowerOrder] at hH
  filter_upwards [realLineMultiplierCLM_ae (lowerOrderCLM (by decide : 1 ≤ 2) W), hH,
    Lp.coeFn_lpSMul (r := 2) (realLineMultiplierCLM (lowerOrderCLM (by decide : 1 ≤ 2) W))
      (realHilbertTransformL2 (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM Q)))]
    with x hw hq hm
  change (realLineMultiplierCLM (lowerOrderCLM (by decide : 1 ≤ 2) W) •
    realHilbertTransformL2 (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM Q))) x = _
  rw [hm]
  simp only [smul_eq_mul, Pi.mul_apply, hw, hq]

end DeGregorio.Iteration
