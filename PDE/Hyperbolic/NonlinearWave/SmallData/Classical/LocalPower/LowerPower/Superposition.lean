/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.FunctionSpace
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.PowerHolder

/-!
# Hölder derivative estimates in the uniform cone space

The derivative of scalar postcomposition acts by pointwise multiplication.
For a power between one and two, its derivative is Hölder continuous in
operator norm on bounded continuous functions. The estimate is uniform in
the compact parameter space and includes functions with zeros.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

variable {α : Type} [TopologicalSpace α] [CompactSpace α]

/-- Evaluate the Fréchet derivative of compact scalar postcomposition. -/
theorem fderiv_composeCompact_apply {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (u w : α →ᵇ ℝ) (a : α) :
    fderiv ℝ (composeCompact ⟨f, hf.continuous⟩) u w a = deriv f (u a) * w a := by
  let N := composeCompact (α := α) ⟨f, hf.continuous⟩
  let L : (α →ᵇ ℝ) →L[ℝ] ℝ := evalCLM ℝ a
  have hN : HasFDerivAt N (fderiv ℝ N u) u :=
    ((contDiff_composeCompact hf).differentiable one_ne_zero u).hasFDerivAt
  have hleft : HasFDerivAt (fun z : α →ᵇ ℝ ↦ f (z a))
      (L.comp (fderiv ℝ N u)) u := by
    simpa only [Function.comp_def, evalCLM_apply, composeCompact_apply,
      ContinuousMap.coe_mk, L, N] using L.hasFDerivAt.comp u hN
  have hev : HasFDerivAt (fun z : α →ᵇ ℝ ↦ z a) L u := by
    have heq : (⇑L) = fun z : α →ᵇ ℝ ↦ z a := by
      funext z
      exact evalCLM_apply ℝ a z
    rw [← heq]
    exact L.hasFDerivAt
  have hright := ((hf.differentiable one_ne_zero (u a)).hasDerivAt).comp_hasFDerivAt u hev
  have heq := congrArg (fun D : (α →ᵇ ℝ) →L[ℝ] ℝ ↦ D w) (hleft.unique hright)
  simpa only [ContinuousLinearMap.comp_apply, _root_.smul_apply,
    smul_eq_mul, evalCLM_apply, L, N] using heq

/-- The derivative of absolute-power postcomposition is Hölder in operator
norm with the same exponent as the scalar derivative. -/
theorem norm_fderiv_composeCompact_abs_rpow_sub_le {p : ℝ}
    (hp : 1 < p) (hp₂ : p ≤ 2) (u v : α →ᵇ ℝ) :
    let f : C(ℝ, ℝ) := ⟨fun x ↦ |x| ^ p, by
      simpa only [Real.norm_eq_abs] using
        (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p)).continuous⟩
    ‖fderiv ℝ (composeCompact f) u - fderiv ℝ (composeCompact f) v‖ ≤
      (2 * p) * ‖u - v‖ ^ (p - 1) := by
  dsimp only
  have hf : ContDiff ℝ 1 (fun x : ℝ ↦ |x| ^ p) := by
    simpa only [Real.norm_eq_abs] using (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p))
  have hC : 0 ≤ (2 * p) * ‖u - v‖ ^ (p - 1) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun w ↦ ?_
  refine (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg w))).mpr fun a ↦ ?_
  simp only [_root_.sub_apply, BoundedContinuousFunction.sub_apply]
  rw [fderiv_composeCompact_apply hf, fderiv_composeCompact_apply hf, ← sub_mul, norm_mul]
  have hab : ‖u a - v a‖ ≤ ‖u - v‖ := (u - v).norm_coe_le_norm a
  have hder := norm_deriv_abs_rpow_sub_le hp hp₂ (u a) (v a)
  exact mul_le_mul (hder.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hab (by linarith)) (by linarith)))
    (w.norm_coe_le_norm a) (norm_nonneg _) hC

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
