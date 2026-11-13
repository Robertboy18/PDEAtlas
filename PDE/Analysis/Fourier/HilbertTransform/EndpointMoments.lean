/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.Regularity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import CAS.ExactTactic

/-!
# Half-line moments of the Hilbert principal value

Reflection turns the Hilbert kernel of an odd input into a half-line kernel. At a
zero of the input a local Lipschitz bound makes the kernel absolutely integrable;
the resulting integral is the principal value, including at support endpoints.
These are the formulas for `u_x(0)`, `u_x(L)` and `c_ω` that precede (4.24) in Chen, Hou and
Huang.

## References

* J. Chen, T. Y. Hou and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), 1282-1350, numbering of arXiv:1905.06387v3,
  Section 4.2.3, the formulas before (4.24). <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped NNReal Topology

noncomputable section

/-- Split a full-line integral into its two reflected half-lines. -/
theorem integral_eq_integral_Ioi_add_reflection {g : ℝ → ℝ} (hg : Integrable g) :
    (∫ y, g y) = ∫ y in Ioi 0, g y + g (-y) := by
  rw [integral_add hg.integrableOn hg.comp_neg.integrableOn,
    integral_comp_neg_Ioi, neg_zero, add_comm]
  rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
    hg.integrableOn hg.integrableOn, Iic_union_Ioi, Measure.restrict_univ]

/-- The uncentered, absolutely convergent Hilbert integral is its principal value. -/
theorem hasHilbertPV_of_integrable_uncentered {f : ℝ → ℝ} {x : ℝ}
    (hf : Integrable (fun y ↦ f y / (x - y))) :
    HasHilbertPV f x (Real.pi⁻¹ * ∫ y, f y / (x - y)) := by
  have hcenter : Integrable (fun t ↦ f (x - t) / t) := by
    simpa only [sub_sub_cancel] using hf.comp_sub_left x
  convert hasHilbertPV_of_integrable hcenter using 1
  congr 1
  simpa only [sub_sub_cancel] using
    (integral_sub_left_eq_self (fun y ↦ f y / (x - y)) volume x).symm

/-- At a zero of a locally Lipschitz input, no singular constant remains to subtract. -/
theorem integrable_hilbertKernel_of_local_lipschitz_zero
    {f : ℝ → ℝ} (hf : Integrable f) {x R C : ℝ}
    (hx : f x = 0) (hR : 0 < R) (hC : 0 ≤ C)
    (hlocal : ∀ t : ℝ, |t| < R → |f (x - t) - f x| ≤ C * |t|) :
    Integrable (fun y ↦ f y / (x - y)) := by
  have h := (integrable_hilbertRegularizedKernel hf hR hC hlocal).comp_sub_left x
  simpa [hilbertRegularizedKernel, hx] using h

/-- Oddness and the right support bound reduce an absolutely convergent PV to `(0,L)`.
Only the positive support bound is needed: oddness determines the negative half. -/
theorem hasHilbertPV_odd_support_of_integrable {f : ℝ → ℝ} {L x : ℝ}
    (hodd : Function.Odd f) (hsupport : ∀ y, L ≤ y → f y = 0)
    (hkernel : Integrable (fun y ↦ f y / (x - y))) :
    HasHilbertPV f x
      (Real.pi⁻¹ * ∫ y in Ioo 0 L, f y / (x - y) - f y / (x + y)) := by
  have hreflect :
      (∫ y, f y / (x - y)) =
        ∫ y in Ioi 0, f y / (x - y) - f y / (x + y) := by
    rw [integral_eq_integral_Ioi_add_reflection hkernel]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    simp [hodd y, sub_eq_add_neg, neg_div]
  have htruncate :
      (∫ y in Ioi 0, f y / (x - y) - f y / (x + y)) =
        ∫ y in Ioo 0 L, f y / (x - y) - f y / (x + y) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ hy ↦ hy.1)
    intro y hy
    have hyL : L ≤ y := not_lt.mp fun hyL ↦ hy.2 ⟨hy.1, hyL⟩
    simp [hsupport y hyL]
  simpa only [hreflect, htruncate] using hasHilbertPV_of_integrable_uncentered hkernel

/-- The origin coefficient for an odd input supported in `[-L,L]`. -/
theorem hasHilbertPV_zero_odd_support {f : ℝ → ℝ} {L : ℝ}
    (hodd : Function.Odd f) (hsupport : ∀ y, L ≤ y → f y = 0)
    (hkernel : Integrable (fun y ↦ f y / y)) :
    HasHilbertPV f 0 (∫ y in Ioo 0 L, (-2 / (Real.pi * y)) * f y) := by
  have hneg : Integrable (fun y ↦ f y / (0 - y)) := by
    simpa only [zero_sub, div_neg] using hkernel.fun_neg
  convert hasHilbertPV_odd_support_of_integrable hodd hsupport hneg using 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y hy
  have hy0 := hy.1.ne'
  cas using hy0

/-- The right endpoint coefficient for an odd input supported in `[-L,L]`. -/
theorem hasHilbertPV_right_odd_support {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hodd : Function.Odd f)
    (hsupport : ∀ y, L ≤ y → f y = 0)
    (hkernel : Integrable (fun y ↦ f y / (L - y))) :
    HasHilbertPV f L (∫ y in Ioo 0 L, (2 * y / (Real.pi * (L ^ 2 - y ^ 2))) * f y) := by
  convert hasHilbertPV_odd_support_of_integrable hodd hsupport hkernel using 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y hy
  have hminus : L - y ≠ 0 := (sub_pos.mpr hy.2).ne'
  have hplus : L + y ≠ 0 := (add_pos hL hy.1).ne'
  have hsq : L ^ 2 - y ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hplus hminus
  cas using hsq

end

end PDE.Analysis
