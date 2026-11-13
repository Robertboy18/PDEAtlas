/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.WeakH2Amplitude
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Pullback.SecondOrder
import CAS.ExactTactic

/-!
# Weak H² spatial slices of the Eulerian transport

The weak H² characteristic amplitude is pulled back by the inverse
flow. Its reciprocal Jacobian and the derivative of that Jacobian satisfy
explicit bounds obtained from the forward Jacobian. This constructs a weak
H² graph for the Eulerian characteristic formula at each time.

The estimate holds at both endpoints of the time interval, which lets us
place the whole output curve in a closed Sobolev ball.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The Eulerian transport formula `w₀(Y(y, t)) exp (∫₀ᵗ c(X(Y(y, t), s), s) ds)` has a
weak H² graph at each time `t ∈ [0, T]`, with an explicit bound linear in `‖W₀‖`. -/
theorem exists_h2_hkCurve_eulerian_slice
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
        (fun y ↦ w₀ (Y y t) * Real.exp (∫ s in 0..t, c (X (Y y t) s) s)) ∧
      ‖W‖ ≤ (succOrderAssemblyNormBound 1 1 *
        (Real.sqrt M * (1 + 2 * (M + N * M ^ 3 + M * M)))) *
        (succOrderAssemblyNormBound 1 1 *
          ((2 * M + N) * (2 + 6 * t * C) * ‖W₀‖)) := by
  intro M N _
  have hM : 0 ≤ M := Real.exp_nonneg _
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  let J : ℝ → ℝ := fun x ↦ Real.exp (∫ s in 0..t, c (X x s) s)
  have hJ : ContDiff ℝ 1 J :=
    contDiff_one_hkCurve_jacobian_slice hT f hchar.toHkForwardCharacteristics ht
  have hJne (x : ℝ) : J x ≠ 0 := Real.exp_ne_zero _
  have hJbound (x : ℝ) : ‖J x‖ ≤ M :=
    norm_exp_integral_flow_le hchar.coefficient_bound x t ht
  have hJ'bound (x : ℝ) : ‖deriv J x‖ ≤ N :=
    norm_deriv_hkCurve_jacobian_le hT f hchar.toHkForwardCharacteristics x t ht
  let e : ℝ ≃ₜ ℝ :=
    { toFun := fun y ↦ Y y t
      invFun := fun x ↦ X x t
      left_inv := fun y ↦ hchar.flow_inverse y t ht
      right_inv := fun x ↦ hchar.inverse_flow x t ht
      continuous_toFun :=
        hchar.inverse_continuous.comp (continuous_id.prodMk (continuous_const (y := (⟨t, ht⟩ : Icc 0
          T))))
      continuous_invFun :=
        hchar.flow_continuous.comp (continuous_id.prodMk (continuous_const (y := (⟨t, ht⟩ : Icc 0
          T)))) }
  have hXderiv (x : ℝ) : HasDerivAt e.symm (J x) x :=
    hasDerivAt_hkCurve_hilbert_flow_space hT f hchar.velocity_derivative hchar.flow_initial
      hchar.flow_derivative x t ht
  have helip : LipschitzWith ⟨M, hM⟩ e.symm :=
    lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (hXderiv x).differentiableAt) fun x ↦
      show ‖deriv e.symm x‖ ≤ M from (hXderiv x).deriv ▸ hJbound x
  let I : ℝ → ℝ := fun y ↦ (J (e y))⁻¹
  let I' : ℝ → ℝ := fun y ↦ -(deriv J (e y)) * I y ^ 3
  have hI : Continuous I :=
    (hJ.continuous.comp e.continuous).inv₀ (fun y ↦ hJne (e y))
  have hI' : Continuous I' :=
    ((hJ.continuous_deriv le_rfl).comp e.continuous).neg.mul (hI.pow 3)
  have hederiv (y : ℝ) : HasDerivAt e (I y) y :=
    hasDerivAt_hkCurve_inverse_space hT f hchar.velocity_derivative hchar.flow_initial
      hchar.flow_derivative hchar.inverse_continuous hchar.flow_inverse y t ht
  have hIderiv (y : ℝ) : HasDerivAt I (I' y) y := by
    have hd : HasDerivAt I (-(deriv J (e y) * I y) / J (e y) ^ 2) y := by
      simpa only [Pi.inv_def, Function.comp_def] using
        ((((hJ.differentiable (by norm_num)) (e y)).hasDerivAt.comp y
          (hederiv y)).inv (hJne (e y)))
    convert hd using 1
    dsimp only [I', I, Function.comp_apply]
    cas using hJne (e y)
  have hIbound (y : ℝ) : ‖I y‖ ≤ M :=
    (hederiv y).deriv ▸ norm_deriv_le_of_lipschitz (hchar.inverse_lipschitz t ht)
  have hI'bound (y : ℝ) : ‖I' y‖ ≤ N * M ^ 3 := by
    simp only [I', norm_mul, norm_neg, norm_pow]
    exact mul_le_mul (hJ'bound (e y)) (pow_le_pow_left₀ (norm_nonneg _) (hIbound y) 3)
      (pow_nonneg (norm_nonneg _) _) hN
  obtain ⟨V, hVbase, hVnorm⟩ := exists_h2_hkCurve_amplitude hT f hchar W₀ hw₀ hW₀ ht
  obtain ⟨W, hWbase, hWnorm⟩ := exists_h2_comp_of_bounded_positive_jacobian e helip hI hI'
    (fun y ↦ inv_nonneg.mpr (Real.exp_nonneg _)) hederiv hIderiv hIbound hI'bound V
    (hw₀.mul hJ.continuous) hVbase
  refine ⟨W, hWbase, hWnorm.trans ?_⟩
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_left hVnorm (mul_nonneg succOrderAssemblyNormBound_nonneg
    (by positivity))

end DeGregorio.Iteration
