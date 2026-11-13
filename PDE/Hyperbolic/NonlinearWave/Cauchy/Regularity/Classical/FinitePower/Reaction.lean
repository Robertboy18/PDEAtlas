/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SignedPower.Deriv
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.Superposition
import CAS.ExactTactic

/-!
# Finite regularity of the signed-power coefficient

The derivative has exponent `min (p - 1) 1` on bounded intervals. This is coefficient regularity.
-/

@[expose] public noncomputable section

open Set BoundedContinuousFunction
open scoped ContDiff
open WaveEquation.SmallData.Classical.LocalPower
open WaveEquation.SmallData.Classical.LocalPower.LowerPower

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

/-- Below exponent two, the derivative has its exact global Hölder bound. -/
theorem norm_deriv_signedPower_sub_le_lower {p : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2) (x y : ℝ) :
    ‖deriv (Real.signedPower p) x - deriv (Real.signedPower p) y‖ ≤ p * ‖x - y‖ ^ (p - 1) := by
  rw [(Real.hasDerivAt_signedPower hp.le x).deriv,
    (Real.hasDerivAt_signedPower hp.le y).deriv, ← mul_sub, norm_mul,
    Real.norm_of_nonneg (by linarith : 0 ≤ p)]
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  exact (norm_rpow_sub_le_rpow_norm_sub (by linarith) (by linarith)
    (abs_nonneg x) (abs_nonneg y)).trans
      (Real.rpow_le_rpow (norm_nonneg _) (by
        simpa only [Real.norm_eq_abs] using abs_abs_sub_abs_le_abs_sub x y) (by linarith))

/-- At and above exponent two, the derivative is Lipschitz on each bounded interval. -/
theorem norm_deriv_signedPower_sub_le_upper {p M : ℝ} (hp : 2 ≤ p)
    {x y : ℝ} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖deriv (Real.signedPower p) x - deriv (Real.signedPower p) y‖ ≤
      (p * (p - 1) * M ^ (p - 2)) * ‖x - y‖ := by
  rw [(Real.hasDerivAt_signedPower (by linarith) x).deriv,
    (Real.hasDerivAt_signedPower (by linarith) y).deriv, ← mul_sub, norm_mul,
    Real.norm_of_nonneg (by linarith : 0 ≤ p)]
  have he := Real.norm_rpow_sub_le_on_Icc (by linarith : 1 ≤ p - 1)
    (show |x| ∈ Icc 0 M from ⟨abs_nonneg x, hx⟩) (show |y| ∈ Icc 0 M from ⟨abs_nonneg y, hy⟩)
  have hab : ‖|x| - |y|‖ ≤ ‖x - y‖ := by
    simpa only [Real.norm_eq_abs] using abs_abs_sub_abs_le_abs_sub x y
  have hc : 0 ≤ (p - 1) * M ^ (p - 1 - 1) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg ((norm_nonneg x).trans hx) _)
  calc
    _ ≤ p * ((p - 1) * M ^ (p - 1 - 1) * ‖x - y‖) := mul_le_mul_of_nonneg_left
        (he.trans (mul_le_mul_of_nonneg_left hab hc)) (by linarith)
    _ = _ := by rw [show p - 1 - 1 = p - 2 by cas]; cas

/-- The exact scalar coefficient exponent is positive for every real `p > 1`. -/
theorem exists_deriv_signedPower_holder_bound {p M : ℝ} (hp : 1 < p) (hM : 0 ≤ M) :
    0 < min (p - 1) 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x y : ℝ, ‖x‖ ≤ M → ‖y‖ ≤ M → ‖deriv (Real.signedPower p) x - deriv (Real.signedPower p) y‖ ≤
        C * ‖x - y‖ ^ (min (p - 1) 1) := by
  refine ⟨lt_min (sub_pos.mpr hp) zero_lt_one, ?_⟩
  by_cases hp₂ : p ≤ 2
  · refine ⟨p, hp.le.trans' zero_le_one, fun x y _ _ ↦ ?_⟩
    rw [min_eq_left (by linarith : p - 1 ≤ 1)]
    exact norm_deriv_signedPower_sub_le_lower hp hp₂ x y
  · refine ⟨p * (p - 1) * M ^ (p - 2), by positivity, fun x y hx hy ↦ ?_⟩
    rw [min_eq_right (by linarith : 1 ≤ p - 1), Real.rpow_one]
    exact norm_deriv_signedPower_sub_le_upper (le_of_not_ge hp₂) hx hy

/-- Above exponent two the scalar reaction is C², without an all-orders assertion. -/
theorem contDiff_two_signedPower {p : ℝ} (hp : 2 < p) :
    ContDiff ℝ 2 (Real.signedPower p) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨(Real.contDiff_one_signedPower (by linarith)).differentiable one_ne_zero,
    by simp, ?_⟩
  have he : deriv (Real.signedPower p) = fun x ↦ p * ‖x‖ ^ (p - 1) := by
    funext x
    exact (Real.hasDerivAt_signedPower (by linarith) x).deriv
  rw [he]
  exact contDiff_const.mul (contDiff_norm_rpow (by linarith : 1 < p - 1))

variable {α : Type} [TopologicalSpace α] [CompactSpace α]

/-- Compact postcomposition inherits the lower-power Hölder estimate in operator norm. -/
theorem norm_fderiv_composeCompact_signedPower_sub_le_lower {p : ℝ}
    (hp : 1 < p) (hp₂ : p ≤ 2) (u v : α →ᵇ ℝ) :
    let f : C(ℝ, ℝ) := ⟨Real.signedPower p, (Real.contDiff_one_signedPower hp.le).continuous⟩;
      ‖fderiv ℝ (composeCompact f) u - fderiv ℝ (composeCompact f) v‖ ≤ p * ‖u - v‖ ^ (p - 1) := by
  dsimp only
  have hf := Real.contDiff_one_signedPower hp.le
  have hC : 0 ≤ p * ‖u - v‖ ^ (p - 1) := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun w ↦ ?_
  refine (BoundedContinuousFunction.norm_le (mul_nonneg hC (norm_nonneg w))).mpr fun a ↦ ?_
  simp only [_root_.sub_apply, BoundedContinuousFunction.sub_apply]
  rw [fderiv_composeCompact_apply hf, fderiv_composeCompact_apply hf, ← sub_mul, norm_mul]
  have hab : ‖u a - v a‖ ≤ ‖u - v‖ := (u - v).norm_coe_le_norm a
  exact mul_le_mul ((norm_deriv_signedPower_sub_le_lower hp hp₂ (u a) (v a)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hab (by linarith)) (by linarith)))
    (w.norm_coe_le_norm a) (norm_nonneg _) hC

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower
