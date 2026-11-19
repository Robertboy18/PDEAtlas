/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import CAS.ExactTactic

/-!
# The general-order normal-frequency integral

For `s > 1/2`, the integral `J(s) = ∫ t, (1 + t²)^(-s)` is finite and strictly
positive. Dilation gives the exact identity
`∫ t, (a² + t²)^(-s) = a^(1 - 2*s) * J(s)` for `a > 0`.
All integrals use Lebesgue measure on the real line. The normalization at order
one is `J(1) = π`; no special-function evaluation is needed at other orders.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace SobolevSpace.Fractional.Trace.GeneralOrder

/-- The unscaled normal integral for the inhomogeneous Hilbert Sobolev weight. -/
def normalMass (s : ℝ) : ℝ :=
  ∫ t : ℝ, (1 + t ^ 2) ^ (-s)

/-- The strict trace threshold gives absolute integrability on each normal line. -/
theorem integrable_unit_normalWeight {s : ℝ} (hs : 1 / 2 < s) :
    Integrable (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s)) := by
  have h := integrable_rpow_neg_one_add_norm_sq
    (E := ℝ) (μ := volume) (r := 2 * s) (by simpa using (show 1 < 2 * s by linarith))
  simpa only [Real.norm_eq_abs, sq_abs, show -(2 * s) / 2 = -s by cas] using h

/-- The finite normal integral is strictly positive above the trace threshold. -/
theorem normalMass_pos {s : ℝ} (hs : 1 / 2 < s) : 0 < normalMass s := by
  unfold normalMass
  rw [integral_pos_iff_support_of_nonneg
    (fun t : ℝ ↦ Real.rpow_nonneg (by positivity) _) (integrable_unit_normalWeight hs)]
  have hsupport : Function.support (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s)) = Set.univ := by
    ext t
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  simp [hsupport]

/-- At order one the normal mass is Mathlib's arctangent integral. -/
theorem normalMass_one : normalMass 1 = Real.pi := by
  simpa only [normalMass, Real.rpow_neg_one] using integral_univ_inv_one_add_sq

/-- Factoring out a positive scale separates the normal and tangential weights. -/
theorem normalWeight_eq_scaled (s : ℝ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (a ^ 2 + t ^ 2) ^ (-s) = a ^ (-2 * s) * (1 + (t / a) ^ 2) ^ (-s) := by
  have hbase : a ^ 2 + t ^ 2 = a ^ 2 * (1 + (t / a) ^ 2) := by cas using ha.ne'
  rw [hbase, Real.mul_rpow (sq_nonneg _) (by positivity),
    ← Real.rpow_natCast_mul ha.le]
  congr 1
  congr 1
  cas

/-- Integrability at arbitrary positive normal-frequency scale. -/
theorem integrable_normalWeight {s a : ℝ} (hs : 1 / 2 < s) (ha : 0 < a) :
    Integrable (fun t : ℝ ↦ (a ^ 2 + t ^ 2) ^ (-s)) := by
  simp_rw [normalWeight_eq_scaled s ha]
  exact ((integrable_unit_normalWeight hs).comp_div ha.ne').const_mul _

/-- The exact normal-frequency dilation formula, including its Jacobian. -/
theorem integral_normalWeight (s : ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ, (a ^ 2 + t ^ 2) ^ (-s) = a ^ (1 - 2 * s) * normalMass s := by
  simp_rw [normalWeight_eq_scaled s ha]
  rw [integral_const_mul,
    Measure.integral_comp_div (fun t : ℝ ↦ (1 + t ^ 2) ^ (-s)), abs_of_pos ha]
  change a ^ (-2 * s) * (a * normalMass s) = _
  rw [← mul_assoc, ← Real.rpow_add_one ha.ne']
  congr 2
  cas

end SobolevSpace.Fractional.Trace.GeneralOrder
