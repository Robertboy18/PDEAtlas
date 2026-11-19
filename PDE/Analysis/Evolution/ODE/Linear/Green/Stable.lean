/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Primitive.Improper
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import CAS.ExactTactic

/-!
# The stable exponential Green integral

An exponentially growing continuous forcing with rate smaller than `a` has a
convergent past integral for `u' + a • u = f`. The norm estimate retains the
forcing's exponential weight and loses precisely the factor `1 / (a - η)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The past Green integral for a scalar stable rate. The integrating-factor
form is convenient for the fundamental theorem of calculus. -/
def pastExponentialIntegral (a : ℝ) (f : ℝ → E) (t : ℝ) : E :=
  Real.exp (-(a * t)) • ∫ s in Iic t, Real.exp (a * s) • f s

private theorem norm_exp_smul_le_on_Iic {a η C : ℝ} {f : ℝ → E}
    (hη : 0 ≤ η) (hC : 0 ≤ C)
    (hbound : ∀ t, ‖f t‖ ≤ Real.exp (η * |t|) * C) {s t : ℝ} (hst : s ≤ t) :
    ‖Real.exp (a * s) • f s‖ ≤
      (Real.exp (η * (|t| + t)) * C) * Real.exp ((a - η) * s) := by
  have hab : |s| ≤ |t| + t - s := abs_le.mpr
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (a * s) * ‖f s‖ ≤
        Real.exp (a * s) * (Real.exp (η * |s|) * C) :=
      mul_le_mul_of_nonneg_left (hbound s) (Real.exp_nonneg _)
    _ = Real.exp (a * s + η * |s|) * C := by rw [Real.exp_add]; ac_rfl
    _ ≤ Real.exp (a * s + η * (|t| + t - s)) * C :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (add_le_add_right (mul_le_mul_of_nonneg_left hab hη) _)) hC
    _ = (Real.exp (η * (|t| + t)) * C) * Real.exp ((a - η) * s) := by
      have heq : a * s + η * (|t| + t - s) = η * (|t| + t) + (a - η) * s := by cas
      rw [heq, Real.exp_add]
      ac_rfl

/-- The integrating-factor integrand is integrable on every left half-line
when its decay dominates the growth of the forcing. -/
theorem integrableOn_exp_smul_Iic {a η C : ℝ} {f : ℝ → E}
    (hη : 0 ≤ η) (ha : η < a) (hC : 0 ≤ C) (hf : Continuous f)
    (hbound : ∀ t, ‖f t‖ ≤ Real.exp (η * |t|) * C) (t : ℝ) :
    IntegrableOn (fun s ↦ Real.exp (a * s) • f s) (Iic t) := by
  refine ((integrableOn_exp_mul_Iic (sub_pos.mpr ha) t).const_mul
    (Real.exp (η * (|t| + t)) * C)).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
  exact norm_exp_smul_le_on_Iic hη hC hbound hs

/-- The past Green integral preserves the forcing's exponential growth rate. -/
theorem norm_pastExponentialIntegral_le {a η C : ℝ} {f : ℝ → E}
    (hη : 0 ≤ η) (ha : η < a) (hC : 0 ≤ C)
    (hbound : ∀ t, ‖f t‖ ≤ Real.exp (η * |t|) * C) (t : ℝ) :
    ‖pastExponentialIntegral a f t‖ ≤ Real.exp (η * |t|) * (C / (a - η)) := by
  have hi := norm_integral_le_of_norm_le
    ((integrableOn_exp_mul_Iic (sub_pos.mpr ha) t).const_mul
      (Real.exp (η * (|t| + t)) * C))
    (f := fun s ↦ Real.exp (a * s) • f s)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
      exact norm_exp_smul_le_on_Iic hη hC hbound hs)
  rw [integral_const_mul, integral_exp_mul_Iic (sub_pos.mpr ha)] at hi
  rw [pastExponentialIntegral, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  refine (mul_le_mul_of_nonneg_left hi (Real.exp_nonneg _)).trans_eq ?_
  have heq : -(a * t) + η * (|t| + t) + (a - η) * t = η * |t| := by cas
  calc
    Real.exp (-(a * t)) *
        ((Real.exp (η * (|t| + t)) * C) * (Real.exp ((a - η) * t) / (a - η))) =
        (Real.exp (-(a * t)) * Real.exp (η * (|t| + t)) *
          Real.exp ((a - η) * t)) * (C / (a - η)) := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = Real.exp (η * |t|) * (C / (a - η)) := by
      rw [← Real.exp_add, ← Real.exp_add, heq]

/-- The convergent past integral is a classical solution of the
inhomogeneous stable linear equation. -/
theorem hasDerivAt_pastExponentialIntegral [CompleteSpace E]
    {a η C : ℝ} {f : ℝ → E}
    (hη : 0 ≤ η) (ha : η < a) (hC : 0 ≤ C) (hf : Continuous f)
    (hbound : ∀ t, ‖f t‖ ≤ Real.exp (η * |t|) * C) (t : ℝ) :
    HasDerivAt (pastExponentialIntegral a f)
      (f t - a • pastExponentialIntegral a f t) t := by
  have hprim := PDE.Analysis.hasDerivAt_integral_Iic
    (show Continuous (fun s ↦ Real.exp (a * s) • f s) by fun_prop)
    (integrableOn_exp_smul_Iic hη ha hC hf hbound) t
  have he : HasDerivAt (fun s ↦ Real.exp (-(a * s)))
      (-a * Real.exp (-(a * t))) t := by cas
  convert he.smul hprim using 1
  · rfl
  · rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
    simp only [pastExponentialIntegral, mul_smul, neg_smul, sub_eq_add_neg]

end PDE.Analysis.Evolution
