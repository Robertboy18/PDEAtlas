/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Pullback.ContinuousLinearMap
public import PDE.Fluid.DeGregorio.Iteration.WeakH2Transport

/-!
# H² composition operators for the characteristic coordinates

The already constructed forward and inverse flows act on H² with uniform
operator bounds on the closed local interval. The bounds use the existing
Jacobian and inverse Lipschitz estimates. These operators allow the first
derivative equation to be solved in characteristic coordinates.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev
open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The inverse characteristic slice, with the forward slice as its inverse. -/
def HkCharacteristics.inverseHomeomorph
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} {hT : 0 ≤ T}
    {f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)}
    {c X Y : ℝ → ℝ → ℝ} (hchar : HkCharacteristics hT f c X Y)
    (t : Icc (0 : ℝ) T) : ℝ ≃ₜ ℝ where
  toFun := fun y ↦ Y y t
  invFun := fun x ↦ X x t
  left_inv := fun y ↦ hchar.flow_inverse y t t.property
  right_inv := fun x ↦ hchar.inverse_flow x t t.property
  continuous_toFun :=
    hchar.inverse_continuous.comp (continuous_id.prodMk (continuous_const (y := t)))
  continuous_invFun :=
    hchar.flow_continuous.comp (continuous_id.prodMk (continuous_const (y := t)))

/-- Both characteristic coordinates act boundedly on H², uniformly
through the closed local interval. Their action is ordinary composition of
the canonical continuous representatives. -/
theorem HkCharacteristics.exists_h2_pullbacks
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} {hT : 0 ≤ T}
    {f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)}
    {c X Y : ℝ → ℝ → ℝ} (hchar : HkCharacteristics hT f c X Y) :
    ∃ P Q : Icc (0 : ℝ) T → W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1),
      (∀ t W, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (P t W)) =
        fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) (X x t)) ∧
      (∀ t W, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (Q t W)) =
        fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) (Y x t)) ∧
      ∃ C ≥ 0, ∀ t W, ‖P t W‖ ≤ C * ‖W‖ ∧ ‖Q t W‖ ≤ C * ‖W‖ := by
  let M := Real.exp (2 * (B : ℝ) * T)
  let N := 2 * (B : ℝ) * T * Real.exp (4 * (B : ℝ) * T)
  have hM : 0 ≤ M := Real.exp_nonneg _
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  let C₁ := succOrderAssemblyNormBound 1 1 *
    (Real.sqrt M * (1 + 2 * (M + N + M * M)))
  let C₂ := succOrderAssemblyNormBound 1 1 *
    (Real.sqrt M * (1 + 2 * (M + N * M ^ 3 + M * M)))
  have hC₁ : 0 ≤ C₁ := mul_nonneg succOrderAssemblyNormBound_nonneg (by positivity)
  have hC₂ : 0 ≤ C₂ := mul_nonneg succOrderAssemblyNormBound_nonneg (by positivity)
  have hex (t : Icc (0 : ℝ) T) :
      ∃ P Q : W^{2,2}(ℝ^1) →L[ℝ] W^{2,2}(ℝ^1),
        (∀ W, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (P W)) =
          fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) (X x t)) ∧
        (∀ W, realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) (Q W)) =
          fun x ↦ realLineRepresentative (lowerOrderCLM (by decide : 1 ≤ 2) W) (Y x t)) ∧
        ∀ W, ‖P W‖ ≤ C₁ * ‖W‖ ∧ ‖Q W‖ ≤ C₂ * ‖W‖ := by
    let J : ℝ → ℝ := fun x ↦ Real.exp (∫ s in 0..(t : ℝ), c (X x s) s)
    have hJ : ContDiff ℝ 1 J :=
      contDiff_one_hkCurve_jacobian_slice hT f hchar.toHkForwardCharacteristics t.property
    have hJne (x : ℝ) : J x ≠ 0 := Real.exp_ne_zero _
    have hJbound (x : ℝ) : ‖J x‖ ≤ M :=
      norm_exp_integral_flow_le hchar.coefficient_bound x t t.property
    have hJ'bound (x : ℝ) : ‖deriv J x‖ ≤ N :=
      norm_deriv_hkCurve_jacobian_le hT f hchar.toHkForwardCharacteristics x t t.property
    let e := hchar.inverseHomeomorph t
    have hXderiv (x : ℝ) : HasDerivAt e.symm (J x) x :=
      hasDerivAt_hkCurve_hilbert_flow_space hT f hchar.velocity_derivative
        hchar.flow_initial hchar.flow_derivative x t t.property
    have helip : LipschitzWith ⟨M, hM⟩ e.symm :=
      lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (hXderiv x).differentiableAt) fun x ↦
        show ‖deriv e.symm x‖ ≤ M from (hXderiv x).deriv ▸ hJbound x
    obtain ⟨P, hP, hPnorm⟩ := exists_h2PullbackCLM e.symm
      (hchar.inverse_lipschitz t t.property) hJ.continuous (hJ.continuous_deriv le_rfl)
      (fun x ↦ Real.exp_nonneg _) hXderiv
      (fun x ↦ (hJ.differentiable (by norm_num) x).hasDerivAt) hJbound hJ'bound
    let I : ℝ → ℝ := fun y ↦ (J (e y))⁻¹
    let I' : ℝ → ℝ := fun y ↦ -(deriv J (e y)) * I y ^ 3
    have hI : Continuous I :=
      (hJ.continuous.comp e.continuous).inv₀ (fun y ↦ hJne (e y))
    have hI' : Continuous I' :=
      ((hJ.continuous_deriv le_rfl).comp e.continuous).neg.mul (hI.pow 3)
    have hederiv (y : ℝ) : HasDerivAt e (I y) y :=
      hasDerivAt_hkCurve_inverse_space hT f hchar.velocity_derivative
        hchar.flow_initial hchar.flow_derivative hchar.inverse_continuous
        hchar.flow_inverse y t t.property
    have hIderiv (y : ℝ) : HasDerivAt I (I' y) y := by
      have hd : HasDerivAt I (-(deriv J (e y) * I y) / J (e y) ^ 2) y := by
        simpa only [Pi.inv_def, Function.comp_def] using
          ((((hJ.differentiable (by norm_num)) (e y)).hasDerivAt.comp y
            (hederiv y)).inv (hJne (e y)))
      convert hd using 1
      dsimp only [I', I, Function.comp_apply]
      field_simp
    have hIbound (y : ℝ) : ‖I y‖ ≤ M :=
      (hederiv y).deriv ▸ norm_deriv_le_of_lipschitz (hchar.inverse_lipschitz t t.property)
    have hI'bound (y : ℝ) : ‖I' y‖ ≤ N * M ^ 3 := by
      simp only [I', norm_mul, norm_neg, norm_pow]
      exact mul_le_mul (hJ'bound (e y)) (pow_le_pow_left₀ (norm_nonneg _) (hIbound y) 3)
        (pow_nonneg (norm_nonneg _) _) hN
    obtain ⟨Q, hQ, hQnorm⟩ := exists_h2PullbackCLM e helip hI hI'
      (fun _ ↦ inv_nonneg.mpr (Real.exp_nonneg _)) hederiv hIderiv hIbound hI'bound
    exact ⟨P, Q, hP, hQ, fun W ↦
      ⟨(hPnorm W).trans_eq (mul_assoc _ _ _).symm, (hQnorm W).trans_eq (mul_assoc _ _ _).symm⟩⟩
  choose P Q hP hQ hnorm using hex
  refine ⟨P, Q, hP, hQ, C₁ + C₂, add_nonneg hC₁ hC₂, fun t W ↦ ?_⟩
  exact ⟨(hnorm t W).1.trans (by gcongr; linarith), (hnorm t W).2.trans (by gcongr; linarith)⟩

end DeGregorio.Iteration
