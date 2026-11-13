/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.NormalWeight
public import Mathlib.MeasureTheory.Function.L2Space
import PDE.Analysis.MeasureTheory.LpNorm
import CAS.ExactTactic

/-!
# The normalized normal-frequency kernel at general order

For `s > 1/2` and `a > 0`, the kernel
`J(s)^(-1/2) * a^(s - 1/2) * (a² + t²)^(-s/2)` has unit `L²` norm.
Its normalization follows from the dilation formula for the normal
weight. Multiplying by the ambient Bessel weight leaves the boundary weight
divided by `sqrt (J(s))`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace SobolevSpace.Fractional.Trace.GeneralOrder

/-- The positive scale factor for the physically normalized trace. -/
def traceConstant (s : ℝ) : ℝ := Real.sqrt (normalMass s)

theorem traceConstant_pos {s : ℝ} (hs : 1 / 2 < s) : 0 < traceConstant s :=
  Real.sqrt_pos.2 (normalMass_pos hs)

theorem traceConstant_sq {s : ℝ} (hs : 1 / 2 < s) :
    traceConstant s ^ 2 = normalMass s :=
  Real.sq_sqrt (normalMass_pos hs).le

theorem traceConstant_one : traceConstant 1 = Real.sqrt Real.pi := by
  rw [traceConstant, normalMass_one]

/-- The unit normal kernel in the weighted Fourier coordinates. -/
def normalKernel (s : ℝ) (a : ℝ≥0) (t : ℝ) : ℝ :=
  (traceConstant s)⁻¹ * (a : ℝ) ^ (s - 1 / 2) *
    ((a : ℝ) ^ 2 + t ^ 2) ^ (-s / 2)

theorem normalKernel_nonneg (s : ℝ) (a : ℝ≥0) (t : ℝ) :
    0 ≤ normalKernel s a t := by
  unfold normalKernel traceConstant
  positivity

theorem normalKernel_neg (s : ℝ) (a : ℝ≥0) (t : ℝ) :
    normalKernel s a (-t) = normalKernel s a t := by
  simp only [normalKernel, neg_sq]

theorem measurable_normalKernel (s : ℝ) (a : ℝ≥0) :
    Measurable (normalKernel s a) := by
  unfold normalKernel
  fun_prop

/-- The kernel's square is the normalized reciprocal Sobolev weight. -/
theorem normalKernel_sq {s : ℝ} (hs : 1 / 2 < s) (a : ℝ≥0) (t : ℝ) :
    normalKernel s a t ^ 2 =
      (normalMass s)⁻¹ * (a : ℝ) ^ (2 * s - 1) *
        ((a : ℝ) ^ 2 + t ^ 2) ^ (-s) := by
  rw [normalKernel, mul_pow, mul_pow, inv_pow, traceConstant_sq hs,
    ← Real.rpow_mul_natCast a.coe_nonneg,
    ← Real.rpow_mul_natCast (by positivity : 0 ≤ (a : ℝ) ^ 2 + t ^ 2)]
  congr 2 <;> congr 1 <;> cas

theorem memLp_normalKernel {s : ℝ} (hs : 1 / 2 < s)
    (a : ℝ≥0) (ha : a ≠ 0) : MemLp (normalKernel s a) 2 volume := by
  rw [memLp_two_iff_integrable_sq (measurable_normalKernel s a).aestronglyMeasurable]
  simp_rw [normalKernel_sq hs]
  exact (integrable_normalWeight hs (show 0 < (a : ℝ) from
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 ha))).const_mul _

/-- The dilation formula makes the normal kernel an `L²` unit vector. -/
theorem integral_normalKernel_sq {s : ℝ} (hs : 1 / 2 < s)
    (a : ℝ≥0) (ha : a ≠ 0) : ∫ t : ℝ, normalKernel s a t ^ 2 = 1 := by
  have ha' : 0 < (a : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ha)
  simp_rw [normalKernel_sq hs]
  rw [integral_const_mul, integral_normalWeight s ha']
  calc
    _ = (normalMass s)⁻¹ *
        ((a : ℝ) ^ (2 * s - 1) * (a : ℝ) ^ (1 - 2 * s)) * normalMass s := by
      ac_rfl
    _ = 1 := by
      rw [← Real.rpow_add ha', show 2 * s - 1 + (1 - 2 * s) = 0 by cas,
        Real.rpow_zero, mul_one, inv_mul_cancel₀ (normalMass_pos hs).ne']

theorem norm_normalKernel_toLp {s : ℝ} (hs : 1 / 2 < s)
    (a : ℝ≥0) (ha : a ≠ 0) :
    ‖(memLp_normalKernel hs a ha).toLp (normalKernel s a)‖ = 1 := by
  have hsq : ‖(memLp_normalKernel hs a ha).toLp (normalKernel s a)‖ ^ 2 = 1 := by
    rw [Lp.norm_sq_eq_integral_sq]
    calc
      _ = ∫ t : ℝ, normalKernel s a t ^ 2 :=
        integral_congr_ae ((memLp_normalKernel hs a ha).coeFn_toLp.fun_comp
          (fun x : ℝ ↦ x ^ 2))
      _ = 1 := integral_normalKernel_sq hs a ha
  nlinarith [norm_nonneg ((memLp_normalKernel hs a ha).toLp (normalKernel s a))]

/-- Cancellation with the ambient Bessel weight, with the exact trace constant. -/
theorem normalKernel_mul_weight {s : ℝ} (hs : 1 / 2 < s)
    (a : ℝ≥0) (ha : a ≠ 0) (t : ℝ) :
    traceConstant s * normalKernel s a t * ((a : ℝ) ^ 2 + t ^ 2) ^ (s / 2) =
      (a : ℝ) ^ (s - 1 / 2) := by
  have hbase : 0 < (a : ℝ) ^ 2 + t ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (NNReal.coe_ne_zero.2 ha)) (sq_nonneg t)
  unfold normalKernel
  calc
    _ = (traceConstant s * (traceConstant s)⁻¹) * (a : ℝ) ^ (s - 1 / 2) *
        (((a : ℝ) ^ 2 + t ^ 2) ^ (-s / 2) *
          ((a : ℝ) ^ 2 + t ^ 2) ^ (s / 2)) := by ac_rfl
    _ = _ := by
      rw [mul_inv_cancel₀ (traceConstant_pos hs).ne', one_mul, ← Real.rpow_add hbase,
        show -s / 2 + s / 2 = 0 by cas, Real.rpow_zero, mul_one]

end SobolevSpace.Fractional.Trace.GeneralOrder
