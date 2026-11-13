/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import CAS.ExactTactic

/-!
# Endpoint bounds for equal-rate transport

A linear remainder for each spatial derivative gives a quadratic zero at the
origin. The normalized velocity and vorticity vanish at the right endpoint.
Together these give an envelope with a quadratic zero at the origin and a
linear zero at the support endpoint. The interval length is any `L ≥ 2`;
no evolution equation or reference profile is assumed.
-/

@[expose] public section

open Set

namespace PDE.Hyperbolic.Transport

/-- Linear origin remainders and endpoint normalization give the singular-weight
envelope for the equal-rate transport expression on `[0, L]`, where `L ≥ 2`.
Only C¹ regularity is required. -/
theorem norm_equal_rate_transport_le_endpoint_envelope {g u : ℝ → ℝ} {a c M L : ℝ} (hL : 2 ≤ L)
    (hM : 0 ≤ M) (hg : ContDiff ℝ 1 g) (hu : ContDiff ℝ 1 u) (hg0 : g 0 = 0) (hu0 : u 0 = 0)
    (hgL : g L = 0) (hbL : c * L + u L = 0) (hrem : ∀ y ∈ Icc (0 : ℝ) L, ‖deriv g y - a‖ ≤ M * y)
    (hremU : ∀ y ∈ Icc (0 : ℝ) L, ‖deriv u y - deriv u 0‖ ≤ M * y)
    (hbound : ∀ y ∈ Icc (0 : ℝ) L, ‖deriv g y‖ ≤ M ∧ ‖c + deriv u y‖ ≤ M) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) L) :
    ‖(c + deriv u x) * g x - (c * x + u x) * deriv g x‖ ≤ (4 * M ^ 2) * x ^ 2 * (L - x) := by
  have hgd := hg.differentiable one_ne_zero
  have hud := hu.differentiable one_ne_zero
  have hgr : ‖g x - a * x‖ ≤ M * x ^ 2 := by
    have hd (y : ℝ) : HasDerivAt (fun z ↦ g z - a * z) (deriv g y - a) y := by
      convert (hgd y).hasDerivAt.sub ((hasDerivAt_id y).const_mul a) using 1
      · rfl
      · rw [mul_one]
    have hb := (convex_Icc (0 : ℝ) x).norm_image_sub_le_of_norm_deriv_le
      (fun y _ ↦ (hd y).differentiableAt)
      (fun y hy ↦ by
        rw [(hd y).deriv]
        exact (hrem y ⟨hy.1, hy.2.trans hx.2⟩).trans (mul_le_mul_of_nonneg_left hy.2 hM))
      (left_mem_Icc.mpr hx.1) (right_mem_Icc.mpr hx.1)
    simpa only [hg0, mul_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hx.1,
      sq, mul_assoc] using hb
  have hgr' : ‖g x - x * deriv g x‖ ≤ 2 * M * x ^ 2 := by
    calc
      _ = ‖(g x - a * x) - x * (deriv g x - a)‖ := by congr 1; cas
      _ ≤ ‖g x - a * x‖ + ‖x * (deriv g x - a)‖ := norm_sub_le _ _
      _ = ‖g x - a * x‖ + x * ‖deriv g x - a‖ := by
        rw [norm_mul, Real.norm_eq_abs x, abs_of_nonneg hx.1]
      _ ≤ M * x ^ 2 + x * (M * x) := add_le_add hgr (mul_le_mul_of_nonneg_left (hrem x hx) hx.1)
      _ = _ := by cas
  have huxdiff (y : ℝ) (hy : y ∈ Icc (0 : ℝ) x) :
      ‖deriv u y - deriv u x‖ ≤ 2 * M * x := by
    calc
      _ ≤ ‖deriv u y - deriv u 0‖ + ‖deriv u x - deriv u 0‖ := by
        simpa only [norm_sub_rev (deriv u 0)] using
          norm_sub_le_norm_sub_add_norm_sub (deriv u y) (deriv u 0) (deriv u x)
      _ ≤ M * y + M * x := add_le_add (hremU y ⟨hy.1, hy.2.trans hx.2⟩) (hremU x hx)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hy.2 hM]
  have hur : ‖u x - x * deriv u x‖ ≤ 2 * M * x ^ 2 := by
    have hd (y : ℝ) : HasDerivAt (fun z ↦ u z - deriv u x * z)
        (deriv u y - deriv u x) y := by
      convert (hud y).hasDerivAt.sub ((hasDerivAt_id y).const_mul (deriv u x)) using 1
      · rfl
      · rw [mul_one]
    have hb := (convex_Icc (0 : ℝ) x).norm_image_sub_le_of_norm_deriv_le
      (fun y _ ↦ (hd y).differentiableAt)
      (fun y hy ↦ by rw [(hd y).deriv]; exact huxdiff y hy)
      (left_mem_Icc.mpr hx.1) (right_mem_Icc.mpr hx.1)
    simpa only [hu0, mul_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hx.1,
      sq, mul_assoc, mul_comm x] using hb
  have hrightG : ‖g x‖ ≤ M * (L - x) := by
    have hb := (convex_Icc x (L : ℝ)).norm_image_sub_le_of_norm_deriv_le (fun y _ ↦ hgd y)
      (fun y hy ↦ (hbound y ⟨hx.1.trans hy.1, hy.2⟩).1)
      (left_mem_Icc.mpr hx.2) (right_mem_Icc.mpr hx.2)
    simpa only [hgL, zero_sub, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hx.2)] using hb
  have hrightB : ‖c * x + u x‖ ≤ M * (L - x) := by
    have hd (y : ℝ) : HasDerivAt (fun z ↦ c * z + u z) (c + deriv u y) y := by
      convert ((hasDerivAt_id y).const_mul c).add (hud y).hasDerivAt using 1
      · rfl
      · rw [mul_one]
    have hb := (convex_Icc x (L : ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun y _ ↦ (hd y).differentiableAt)
      (fun y hy ↦ by
        rw [(hd y).deriv]
        exact (hbound y ⟨hx.1.trans hy.1, hy.2⟩).2) (left_mem_Icc.mpr hx.2) (right_mem_Icc.mpr hx.2)
    simpa only [hbL, zero_sub, norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hx.2)] using hb
  have hleft : ‖(c + deriv u x) * g x - (c * x + u x) * deriv g x‖ ≤
      (4 * M ^ 2) * x ^ 2 := by
    calc
      _ = ‖(c + deriv u x) * (g x - x * deriv g x) -
          (u x - x * deriv u x) * deriv g x‖ := by congr 1; cas
      _ ≤ ‖(c + deriv u x) * (g x - x * deriv g x)‖ +
          ‖(u x - x * deriv u x) * deriv g x‖ := norm_sub_le _ _
      _ = ‖c + deriv u x‖ * ‖g x - x * deriv g x‖ +
          ‖u x - x * deriv u x‖ * ‖deriv g x‖ := by rw [norm_mul, norm_mul]
      _ ≤ M * (2 * M * x ^ 2) + (2 * M * x ^ 2) * M :=
        add_le_add (mul_le_mul (hbound x hx).2 hgr' (norm_nonneg _) hM)
          (mul_le_mul hur (hbound x hx).1 (norm_nonneg _) (by positivity))
      _ = _ := by cas
  have hright : ‖(c + deriv u x) * g x - (c * x + u x) * deriv g x‖ ≤
      (2 * M ^ 2) * (L - x) := by
    calc
      _ ≤ ‖(c + deriv u x) * g x‖ + ‖(c * x + u x) * deriv g x‖ := norm_sub_le _ _
      _ = ‖c + deriv u x‖ * ‖g x‖ + ‖c * x + u x‖ * ‖deriv g x‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ M * (M * (L - x)) + (M * (L - x)) * M :=
        add_le_add (mul_le_mul (hbound x hx).2 hrightG (norm_nonneg _) hM)
          (mul_le_mul hrightB (hbound x hx).1 (norm_nonneg _) (mul_nonneg hM (sub_nonneg.mpr hx.2)))
      _ = _ := by cas
  by_cases hs : x ≤ L - 1
  · exact hleft.trans (le_mul_of_one_le_right (by positivity) (by linarith))
  · have hx2 : 2 ≤ 4 * x ^ 2 := by nlinarith
    calc
      _ ≤ (2 * M ^ 2) * (L - x) := hright
      _ ≤ (4 * M ^ 2) * x ^ 2 * (L - x) := by
        apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hx.2)
        nlinarith [mul_le_mul_of_nonneg_right hx2 (sq_nonneg M)]

end PDE.Hyperbolic.Transport
