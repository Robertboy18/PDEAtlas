/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.Superposition
import CAS.ExactTactic

/-!
# Finite increments of the lower-power reaction

The first-order remainder of the absolute power is bounded by the `p`th
power of the increment, uniformly across zeros. Applying the estimate in
the uniform cone norm permits finite differences of the nonlinear
integral equation without assuming second derivatives of its solution.
-/

@[expose] public noncomputable section

open Set BoundedContinuousFunction

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

/-- The Hölder derivative estimate gives a global first-order remainder
bound, including increments through zero. -/
theorem norm_abs_rpow_sub_linear_le {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (x y : ℝ) :
    ‖|y| ^ p - |x| ^ p - deriv (fun z : ℝ ↦ |z| ^ p) x * (y - x)‖ ≤ (2 * p) * ‖y - x‖ ^ p := by
  let f : ℝ → ℝ := fun z ↦ |z| ^ p
  have hf : ContDiff ℝ 1 f := by
    simpa only [Real.norm_eq_abs] using (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun z : ℝ ↦ ‖z‖ ^ p))
  have hd (z : ℝ) : HasDerivAt (fun w ↦ f w - f x - deriv f x * (w - x))
        (deriv f z - deriv f x) z := by
    simpa only [id_eq, one_mul, mul_one] using
      ((hf.differentiable one_ne_zero z).hasDerivAt.sub_const (f x)).fun_sub
        (((hasDerivAt_id z).sub_const x).const_mul (deriv f x))
  have hb (z : ℝ) (hz : z ∈ segment ℝ x y) :
      ‖deriv f z - deriv f x‖ ≤ (2 * p) * ‖y - x‖ ^ (p - 1) :=
    (norm_deriv_abs_rpow_sub_le hp hp₂ z x).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le_of_mem_segment hz)
          (by linarith)) (by linarith))
  have hm := (convex_segment x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ ↦ (hd z).hasDerivWithinAt) hb (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hpow : ‖y - x‖ ^ (p - 1) * ‖y - x‖ = ‖y - x‖ ^ p := by
    conv_lhs => rhs; rw [← Real.rpow_one ‖y - x‖]
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _)
      (by linarith : 0 ≤ p - 1) zero_le_one]
    congr 1
    cas
  simpa only [sub_self, mul_zero, sub_zero, mul_assoc, hpow, f] using hm

variable {α : Type} [TopologicalSpace α] [CompactSpace α]

/-- A uniform bound on a cone field bounds its absolute-power reaction. -/
theorem norm_composeCompact_abs_rpow_le {p M : ℝ} (hp : 1 < p)
    (u : α →ᵇ ℝ) (hu : ‖u‖ ≤ M) :
    let f : C(ℝ, ℝ) := ⟨fun x ↦ |x| ^ p, by
      simpa only [Real.norm_eq_abs] using
        (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p)).continuous⟩
    ‖composeCompact f u‖ ≤ M ^ p := by
  dsimp only
  have hM : 0 ≤ M := (norm_nonneg u).trans hu
  refine (BoundedContinuousFunction.norm_le (Real.rpow_nonneg hM p)).mpr fun a ↦ ?_
  simp only [composeCompact_apply, ContinuousMap.coe_mk,
    Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) ((u.norm_coe_le_norm a).trans hu)
    (by linarith)

/-- The power remainder estimate holds in the uniform norm on every compact
parameter space. -/
theorem norm_composeCompact_abs_rpow_sub_linear_le {p : ℝ}
    (hp : 1 < p) (hp₂ : p ≤ 2) (u v : α →ᵇ ℝ) :
    let f : C(ℝ, ℝ) := ⟨fun x ↦ |x| ^ p, by
      simpa only [Real.norm_eq_abs] using
        (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p)).continuous⟩
    ‖composeCompact f v - composeCompact f u -
        fderiv ℝ (composeCompact f) u (v - u)‖ ≤
      (2 * p) * ‖v - u‖ ^ p := by
  dsimp only
  have hf : ContDiff ℝ 1 (fun x : ℝ ↦ |x| ^ p) := by
    simpa only [Real.norm_eq_abs] using (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p))
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun a ↦ ?_
  simp only [BoundedContinuousFunction.sub_apply, composeCompact_apply,
    ContinuousMap.coe_mk, fderiv_composeCompact_apply hf]
  exact (norm_abs_rpow_sub_linear_le hp hp₂ (u a) (v a)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) ((v - u).norm_coe_le_norm a)
        (by linarith)) (by linarith))

/-- On a uniform ball, the power derivative is bounded by its scalar
derivative at the radius. -/
theorem norm_fderiv_composeCompact_abs_rpow_le {p M : ℝ}
    (hp : 1 < p) (u : α →ᵇ ℝ) (hu : ‖u‖ ≤ M) :
    let f : C(ℝ, ℝ) := ⟨fun x ↦ |x| ^ p, by
      simpa only [Real.norm_eq_abs] using
        (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p)).continuous⟩
    ‖fderiv ℝ (composeCompact f) u‖ ≤ p * M ^ (p - 1) := by
  dsimp only
  have hf : ContDiff ℝ 1 (fun x : ℝ ↦ |x| ^ p) := by
    simpa only [Real.norm_eq_abs] using (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p))
  have hM : 0 ≤ M := (norm_nonneg _).trans hu
  have hC : 0 ≤ p * M ^ (p - 1) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hM _)
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun w ↦ ?_
  refine (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg _))).mpr fun a ↦ ?_
  rw [fderiv_composeCompact_apply hf, norm_mul, deriv_abs_rpow_eq_signedPower hp, norm_mul,
    Real.norm_of_nonneg (by linarith : 0 ≤ p),
    Real.norm_signedPower (by linarith : 0 < p - 1)]
  exact mul_le_mul (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) ((u.norm_coe_le_norm a).trans hu)
        (by linarith)) (by linarith)) (w.norm_coe_le_norm a) (norm_nonneg _) hC

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
