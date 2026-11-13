/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.JacobianDerivative
import CAS.ExactTactic

/-!
# The weak H¹ graph of the differentiated characteristic integrand

At every time in the prescribed closed interval, the function
`c_x(X(x,t),t) J(x,t)` has an H¹ graph. Its input graph comes from spectral
Hilbert derivative commutation, and its pullback uses the constructed
characteristic coordinates and their inverse Lipschitz bound.

The graph bound is uniform in time. L² continuity of this family and the
identification of its integral with the differentiated log-Jacobian are in
`LogJacobianIntegral`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PDE.Analysis
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The integrand in the spatial derivative of the log-Jacobian
has a uniformly bounded H¹ graph at every time, including both endpoints. -/
theorem exists_h1_hkCurve_jacobian_integrand
    {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {c X Y : ℝ → ℝ → ℝ} (hchar : HkCharacteristics hT f c X Y)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ W : W^{1,2}((Set.univ : Set (ℝ^1))),
      ‖W‖ ≤ Real.sqrt (Real.exp (2 * (B : ℝ) * T)) *
        ((Real.exp (2 * (B : ℝ) * T) +
          (2 * (B : ℝ) * T + 1) * Real.exp (4 * (B : ℝ) * T)) * B) ∧
      realLineRepresentative W = (fun x ↦ deriv (fun y ↦ c y t) (X x t) *
        Real.exp (∫ s in 0..t, c (X x s) s)) := by
  let e : ℝ ≃ₜ ℝ :=
    { toEquiv :=
        { toFun := fun x ↦ X x t
          invFun := fun y ↦ Y y t
          left_inv := fun x ↦ hchar.inverse_flow x t ht
          right_inv := fun y ↦ hchar.flow_inverse y t ht }
      continuous_toFun := hchar.flow_continuous.comp
        (continuous_id.prodMk (continuous_const (y := (⟨t, ht⟩ : Icc 0 T))))
      continuous_invFun := hchar.inverse_continuous.comp
        (continuous_id.prodMk (continuous_const (y := (⟨t, ht⟩ : Icc 0 T)))) }
  let J : ℝ → ℝ := fun x ↦ Real.exp (∫ s in 0..t, c (X x s) s)
  have hJ : ContDiff ℝ 1 J :=
    contDiff_one_hkCurve_jacobian_slice hT f hchar.toHkForwardCharacteristics ht
  have he' (x : ℝ) : HasDerivAt e (J x) x :=
    hasDerivAt_hkCurve_hilbert_flow_space hT f hchar.velocity_derivative hchar.flow_initial
      hchar.flow_derivative x t ht
  have hJbound (x : ℝ) : ‖J x‖ ≤ Real.exp (2 * (B : ℝ) * T) :=
    norm_exp_integral_flow_le hchar.coefficient_bound x t ht
  obtain ⟨V, _hV, hV₀, hV₁, hcV⟩ :=
    exists_hilbert_derivative_h1_of_hkBaseBall
      (f (projIcc 0 T hT t)).property.1
      (hchar.coefficient_continuous.comp (continuous_id.prodMk continuous_const))
        (hchar.hilbert_pair t)
  have hderiv (x : ℝ) : deriv (fun y ↦ c y t) x = realLineRepresentative V x :=
    (hcV x).deriv
  obtain ⟨W, hWnorm, hW, _hrow⟩ := exists_h1_jacobian_weighted_pullback e (hchar.inverse_lipschitz t
    ht)
    hJ.continuous (contDiff_one_iff_deriv.mp hJ).2
    (fun x ↦ Real.exp_nonneg _)
    he' (fun x ↦ (hJ.differentiable (by simp) x).hasDerivAt)
    hJbound (fun x ↦ norm_deriv_hkCurve_jacobian_le hT f hchar.toHkForwardCharacteristics x t ht) V
  refine ⟨W, ?_, ?_⟩
  · apply hWnorm.trans
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    have hM : 0 ≤ Real.exp (2 * (B : ℝ) * T) := Real.exp_nonneg _
    have hN : 0 ≤ 2 * (B : ℝ) * T * Real.exp (4 * (B : ℝ) * T) := by positivity
    apply (add_le_add
      (mul_le_mul_of_nonneg_left hV₀ (add_nonneg hM hN))
      (mul_le_mul_of_nonneg_left hV₁ (mul_nonneg hM hM))).trans
    have he : Real.exp (2 * (B : ℝ) * T) * Real.exp (2 * (B : ℝ) * T) =
        Real.exp (4 * (B : ℝ) * T) := by
      rw [← Real.exp_add]
      congr 1
      cas
    rw [he]
    apply le_of_eq
    cas
  · rw [hW]
    funext x
    rw [hderiv]
    rfl

end DeGregorio.Iteration
