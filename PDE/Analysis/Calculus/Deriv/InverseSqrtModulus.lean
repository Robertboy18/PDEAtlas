/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
import CAS.ExactTactic

/-!
# Continuity estimates from an inverse square root derivative bound

A derivative bounded by `A + B / √x` may become unbounded near zero, but its
primitive still has a uniform modulus of continuity. Comparing with
`A x + 2 B √x` retains the square root contribution instead of replacing the
derivative by its supremum on each interval.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrating the inverse square root bound gives the exact difference of
square roots. Only continuity is needed at the right endpoint. -/
theorem norm_sub_le_add_sqrt_sub_of_deriv_bound
    {f : ℝ → E} {A B a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hfd : ∀ t ∈ Ico a b, DifferentiableAt ℝ f t)
    (hbound : ∀ t ∈ Ico a b, ‖deriv f t‖ ≤ A + B / Real.sqrt t) :
    ‖f b - f a‖ ≤ A * (b - a) + 2 * B * (Real.sqrt b - Real.sqrt a) := by
  let g := fun t ↦ f t - f a
  let majorant := fun t ↦ A * (t - a) + 2 * B * (Real.sqrt t - Real.sqrt a)
  have hgd (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt g (deriv f t) (Ici t) t :=
    ((hfd t ht).hasDerivAt.sub_const (f a)).hasDerivWithinAt
  have hmd (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt majorant (A + B / Real.sqrt t) (Ici t) t := by
    have htpos : 0 < t := ha.trans_le ht.1
    have hd : HasDerivAt majorant (A + B / Real.sqrt t) t := by
      dsimp only [majorant]
      cas using htpos
    exact hd.hasDerivWithinAt
  exact image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (hf.sub continuousOn_const) hgd
    (by simp [majorant]) (by dsimp only [majorant]; fun_prop) hmd hbound
    (right_mem_Icc.mpr hab)

/-- A nonnegative inverse square root contribution gives a square root modulus
of continuity on a positive interval, uniformly as either point approaches zero. -/
theorem norm_sub_le_of_deriv_le_add_inv_sqrt
    {f : ℝ → E} {A B L x y : ℝ} (hB : 0 ≤ B)
    (hf : ContinuousOn f (Ioc 0 L))
    (hfd : ∀ t ∈ Ioo 0 L, DifferentiableAt ℝ f t)
    (hbound : ∀ t ∈ Ioo 0 L, ‖deriv f t‖ ≤ A + B / Real.sqrt t)
    (hx : x ∈ Ioc 0 L) (hy : y ∈ Ioc 0 L) :
    ‖f x - f y‖ ≤ A * |x - y| + 2 * B * Real.sqrt |x - y| := by
  have ordered (a b : ℝ) (ha : a ∈ Ioc 0 L) (hb : b ∈ Ioc 0 L) (hab : a ≤ b) :
      ‖f b - f a‖ ≤ A * (b - a) + 2 * B * Real.sqrt (b - a) := by
    have hsub : Icc a b ⊆ Ioc 0 L := fun t ht ↦
      ⟨ha.1.trans_le ht.1, ht.2.trans hb.2⟩
    have hsub' : Ico a b ⊆ Ioo 0 L := fun t ht ↦
      ⟨ha.1.trans_le ht.1, ht.2.trans_le hb.2⟩
    have hsqrt : Real.sqrt b - Real.sqrt a ≤ Real.sqrt (b - a) := by
      apply Real.le_sqrt_of_sq_le
      have hmul : 0 ≤ Real.sqrt a * (Real.sqrt b - Real.sqrt a) :=
        mul_nonneg (Real.sqrt_nonneg a) (sub_nonneg.mpr (Real.sqrt_le_sqrt hab))
      nlinarith [Real.sq_sqrt ha.1.le, Real.sq_sqrt hb.1.le]
    exact (norm_sub_le_add_sqrt_sub_of_deriv_bound ha.1 hab (hf.mono hsub)
      (fun t ht ↦ hfd t (hsub' ht)) (fun t ht ↦ hbound t (hsub' ht))).trans
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 2 * B by positivity)))
  rcases le_total x y with hxy | hyx
  · simpa only [norm_sub_rev (f x), abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)]
      using ordered x y hx hy hxy
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hyx)] using ordered y x hy hx hyx

end PDE.Analysis
