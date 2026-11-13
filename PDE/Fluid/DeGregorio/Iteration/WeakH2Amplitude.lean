/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.LogJacobianIntegral
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Multiplier.SecondOrder

/-!
# Weak H² regularity of the characteristic amplitude

The integrated characteristic integrand gives an H¹ graph for the
logarithmic derivative of the Jacobian. Multiplication by the bounded C¹
Jacobian constructs an H¹ graph for its first derivative. The real-line
H² multiplier theorem then constructs the weak H² graph of `w₀ J`.

The initial datum is a weak H² graph with a continuous representative.
Constructing the output graph through weak products avoids requiring a
highest classical derivative. The resulting bound is uniform on a finite
time interval.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The characteristic amplitude `w₀(x) exp (∫₀ᵗ c(X(x, s), s) ds)` of weak H² initial
data has a weak H² graph at every time `t ∈ [0, T]`, with an explicit bound linear
in `‖W₀‖`. -/
theorem exists_h2_hkCurve_amplitude
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X Y : ℝ → ℝ → ℝ} (hchar : HkCharacteristics hT f c X Y)
    (W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))) {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀)
    (hW₀ : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) : ℝ → ℝ)
      =ᵐ[volume] w₀)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    let M := Real.exp (2 * (B : ℝ) * T)
    let N := 2 * (B : ℝ) * T * Real.exp (4 * (B : ℝ) * T)
    let C := Real.sqrt M *
      ((M + (2 * (B : ℝ) * T + 1) * Real.exp (4 * (B : ℝ) * T)) * B)
    ∃ W : W^{2,2}((Set.univ : Set (ℝ^1))),
      (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W) : ℝ → ℝ) =ᵐ[volume]
        (fun x ↦ w₀ x * Real.exp (∫ s in 0..t, c (X x s) s)) ∧
      ‖W‖ ≤ succOrderAssemblyNormBound 1 1 *
        ((2 * M + N) * (2 + 6 * t * C) * ‖W₀‖) := by
  intro M N C
  let J : ℝ → ℝ := fun x ↦ Real.exp (∫ s in 0..t, c (X x s) s)
  have hM : 0 ≤ M := Real.exp_nonneg _
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hJcont : Continuous J :=
    (contDiff_one_hkCurve_jacobian_slice hT f hchar.toHkForwardCharacteristics ht).continuous
  have hJbound (x : ℝ) : ‖J x‖ ≤ M :=
    norm_exp_integral_flow_le hchar.coefficient_bound x t ht
  obtain ⟨_F, _hF, _hFrep, L, hLnorm, _hLbase, hLrep, _hLderiv⟩ :=
    exists_h1_hkCurve_logJacobian_derivative hT f hchar ht
  have hJderiv (x : ℝ) : HasDerivAt J (J x * realLineRepresentative L x) x := by
    rw [hLrep]; exact hasDerivAt_hkCurve_jacobian hT f hchar.toHkForwardCharacteristics x t ht
  have hJ'bound (x : ℝ) : ‖J x * realLineRepresentative L x‖ ≤ N :=
    (hJderiv x).deriv ▸ norm_deriv_hkCurve_jacobian_le hT f hchar.toHkForwardCharacteristics x t ht
  obtain ⟨R, hRnorm, hRrep, _hRrow⟩ := exists_h1_mul_of_bounded_c1 L hJcont
    (hJcont.mul (continuous_realLineRepresentative L)) hJderiv hJbound hJ'bound
  have hRderiv (x : ℝ) : HasDerivAt J (realLineRepresentative R x) x := by
    simpa only [hRrep, mul_comm] using hJderiv x
  have hRbound (x : ℝ) : ‖realLineRepresentative R x‖ ≤ N := by
    simpa only [hRrep, mul_comm] using hJ'bound x
  have hL i := (norm_realLineCoordinateCLM_le i L).trans hLnorm
  have hR : ‖R‖ ≤ (2 * M + N) * (t * C) := hRnorm.trans <| (add_le_add
    (mul_le_mul_of_nonneg_left (hL _) (add_nonneg hM hN))
    (mul_le_mul_of_nonneg_left (hL _) hM)).trans_eq (by ring)
  let U := lowerOrderCLM (by decide : 1 ≤ 2) W₀
  let V := derivativeWordCLM [0] (by decide : [0].length + 1 ≤ 2) W₀
  have hUV : realLineCoordinateCLM (baseIndex 1 1) V =
      realLineCoordinateCLM (singleDerivIndex 1 0) U := by
    apply congrArg oneDimensionalPushforwardL2
    change (V : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
      (U : WkpAmbientOn 1 1 2 univ) (singleDerivIndex 1 0)
    simp only [V, U, derivativeWordCLM_apply, derivativeWordIndex_singleton_baseIndex,
      lowerOrderCLM_apply, DerivIndex.castOrder_singleDerivIndex]
  have hUbase : realLineCoordinateCLM (baseIndex 1 1) U =
      oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) := by
    apply congrArg oneDimensionalPushforwardL2
    change (U : WkpAmbientOn 1 1 2 univ) (baseIndex 1 1) =
      (W₀ : WkpAmbientOn 1 2 2 univ) (baseIndex 1 2)
    simp only [U, lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex]
  have hUrep : realLineRepresentative U = w₀ :=
    (Continuous.ae_eq_iff_eq volume (continuous_realLineRepresentative U) hw₀).mp
      ((hUbase ▸ realLineCoordinate_ae_representative U).symm.trans hW₀)
  have hU : ‖U‖ ≤ ‖W₀‖ := norm_lowerOrderCLM_apply_le _ W₀
  have hV : ‖V‖ ≤ ‖W₀‖ := norm_derivativeWordCLM_apply_le _ _ W₀
  obtain ⟨W, hWbase, hWnorm⟩ :=
    exists_h2_mul_of_h1_multiplier_derivative U V R hUV hJcont hRderiv hJbound hRbound
  refine ⟨W, by simpa only [hUrep] using hWbase,
    hWnorm.trans (mul_le_mul_of_nonneg_left ?_ succOrderAssemblyNormBound_nonneg)⟩
  refine (add_le_add (mul_le_mul_of_nonneg_left (add_le_add hU hV) (by positivity))
    (mul_le_mul (add_le_add (mul_le_mul_of_nonneg_left hU (by norm_num))
      (mul_le_mul_of_nonneg_left hV (by norm_num))) hR (norm_nonneg R) (by positivity))).trans_eq ?_
  ring

end DeGregorio.Iteration
