/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Bounds
public import PDE.Analysis.SpecialFunctions.SphericalBessel.Rayleigh

/-!
# Zeros of spherical Bessel functions

Away from the origin the derivatives of `j_l` and `j_{l+1}` are combinations of the same two
functions: `j_l' = (l / x) j_l - j_{l+1}` and `j_{l+1}' = j_l - ((l + 2) / x) j_{l+1}`.

Two functions of consecutive orders have no common zero away from the origin, since the
three-term recurrence would carry a common zero down to `j_0` and `j_1`, and these do not vanish
together. At a zero of one of them the derivative is therefore the other one, up to sign.

The function `j_l` is positive on `(0, √(l (l + 1))]`. The flux `x ^ 2 j_l'` has derivative
`(l (l + 1) - x ^ 2) j_l` and vanishes at the origin, so before the first positive zero of `j_l`
and below `√(l (l + 1))` the flux is positive and `j_l` increases from `j_l 0 ≥ 0`. In the same
way `(x ^ (l + 2) j_{l+1})' = x ^ (l + 2) j_l` shows that `j_{l+1}` is positive on `(0, z]`
whenever `j_l` is positive on `(0, z)`. Since `j_l = x ^ l g_l` with `g_l 0 > 0`, the function
`j_l` is positive on `(0, z)` as soon as it has no zero there.
-/

@[expose] public section

namespace PDE.Analysis.SpecialFunctions

/-- `j_l' x = (l / x) j_l x - j_{l+1} x` for `x ≠ 0`. -/
theorem hasDerivAt_sphericalBesselJ_of_ne_zero {x : ℝ} (hx : x ≠ 0) (l : ℕ) :
    HasDerivAt (sphericalBesselJ l) (l / x * sphericalBesselJ l x - sphericalBesselJ (l + 1) x)
      x := by
  rw [← deriv_sphericalBesselJ_eq hx]
  exact (differentiable_sphericalBesselJ l x).hasDerivAt

/-- `j_{l+1}' x = j_l x - ((l + 2) / x) j_{l+1} x` for `x ≠ 0`. -/
theorem hasDerivAt_sphericalBesselJ_succ_of_ne_zero {x : ℝ} (hx : x ≠ 0) (l : ℕ) :
    HasDerivAt (sphericalBesselJ (l + 1))
      (sphericalBesselJ l x - (l + 2) / x * sphericalBesselJ (l + 1) x) x := by
  refine (hasDerivAt_sphericalBesselJ_succ l x).congr_deriv ?_
  rw [sphericalBesselJ_add_two hx]
  field_simp
  ring

/-- Away from the origin, `j_l` and `j_{l+1}` have no common zero. -/
theorem sphericalBesselJ_succ_ne_zero_of_eq_zero {x : ℝ} (hx : x ≠ 0) {l : ℕ}
    (h : sphericalBesselJ l x = 0) : sphericalBesselJ (l + 1) x ≠ 0 := by
  induction l with
  | zero =>
    intro h₁
    rw [sphericalBesselJ_zero_eq hx, div_eq_zero_iff, or_iff_left hx] at h
    rw [zero_add, sphericalBesselJ_one_eq hx, h, zero_div, zero_sub, neg_eq_zero,
      div_eq_zero_iff, or_iff_left hx] at h₁
    have h₂ := Real.sin_sq_add_cos_sq x
    rw [h, h₁] at h₂
    norm_num at h₂
  | succ m ih =>
    intro h₁
    have h₂ : sphericalBesselJ (m + 2) x = 0 := h₁
    rw [sphericalBesselJ_add_two hx, h, mul_zero, zero_sub, neg_eq_zero] at h₂
    exact ih h₂ h

/-- At a zero `x ≠ 0` of `j_{l+1}`, the derivative of `j_{l+1}` is `j_l x`. -/
theorem deriv_sphericalBesselJ_succ_of_eq_zero {x : ℝ} (hx : x ≠ 0) {l : ℕ}
    (h : sphericalBesselJ (l + 1) x = 0) :
    deriv (sphericalBesselJ (l + 1)) x = sphericalBesselJ l x := by
  rw [(hasDerivAt_sphericalBesselJ_succ_of_ne_zero hx l).deriv, h, mul_zero, sub_zero]

/-- At a zero `x ≠ 0` of `j_l`, the derivative of `j_l` is `-j_{l+1} x`. -/
theorem deriv_sphericalBesselJ_of_eq_zero {x : ℝ} (hx : x ≠ 0) {l : ℕ}
    (h : sphericalBesselJ l x = 0) :
    deriv (sphericalBesselJ l) x = -sphericalBesselJ (l + 1) x := by
  rw [(hasDerivAt_sphericalBesselJ_of_ne_zero hx l).deriv, h, mul_zero, zero_sub]

/-- `j_l` is positive on `(0, √(l (l + 1))]`. In particular its first positive zero exceeds
`√(l (l + 1))`. -/
theorem sphericalBesselJ_pos_of_sq_le {l : ℕ} {x : ℝ} (hx : 0 < x)
    (hxl : x ^ 2 ≤ l * (l + 1)) : 0 < sphericalBesselJ l x := by
  obtain _ | m := l
  · norm_num at hxl
    nlinarith
  have hgc : Continuous (reducedSphericalBesselJ (m + 1)) :=
    (differentiable_reducedSphericalBesselJ _).continuous
  by_contra hneg
  push Not at hneg
  have hgx : reducedSphericalBesselJ (m + 1) x ≤ 0 := by
    by_contra hg
    push Not at hg
    rw [sphericalBesselJ_eq_pow_mul] at hneg
    exact (mul_pos (pow_pos hx _) hg).not_ge hneg
  set T := Set.Icc 0 x ∩ {t | reducedSphericalBesselJ (m + 1) t ≤ 0} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_le hgc continuous_const)
  have hxT : x ∈ T := ⟨⟨hx.le, le_rfl⟩, hgx⟩
  have hbdd : BddBelow T := ⟨0, fun t ht ↦ ht.1.1⟩
  obtain ⟨c, hcT, hpos⟩ : ∃ c ∈ T, ∀ t ∈ Set.Ico 0 c, 0 < reducedSphericalBesselJ (m + 1) t := by
    refine ⟨sInf T, hTc.csInf_mem ⟨x, hxT⟩ hbdd, fun t ht ↦ ?_⟩
    by_contra hgt
    push Not at hgt
    have htT : t ∈ T := ⟨⟨ht.1, ht.2.le.trans (csInf_le hbdd hxT)⟩, hgt⟩
    exact (not_le.mpr ht.2) (csInf_le hbdd htT)
  have hc0 : 0 < c := by
    rcases hcT.1.1.eq_or_lt with h | h
    · rw [← h] at hcT
      exact absurd hcT.2 (not_le.mpr (reducedSphericalBesselJ_zero_pos _))
    · exact h
  have hjpos : ∀ t ∈ Set.Ioo 0 c, 0 < sphericalBesselJ (m + 1) t := fun t ht ↦ by
    rw [sphericalBesselJ_eq_pow_mul]
    exact mul_pos (pow_pos ht.1 _) (hpos t ⟨ht.1.le, ht.2⟩)
  have hF := hasDerivAt_sq_mul_deriv_sphericalBesselJ (m + 1)
  have hFmono : StrictMonoOn (fun y ↦ y ^ 2 * deriv (sphericalBesselJ (m + 1)) y)
      (Set.Icc 0 c) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 c)
      (fun t _ ↦ (hF t).continuousAt.continuousWithinAt) fun t ht ↦ ?_
    rw [interior_Icc] at ht
    rw [(hF t).deriv]
    have htx : t < x := ht.2.trans_le hcT.1.2
    have ht2 : t ^ 2 < x ^ 2 := by nlinarith [ht.1]
    exact mul_pos (by linarith) (hjpos t ht)
  have hjmono : StrictMonoOn (sphericalBesselJ (m + 1)) (Set.Icc 0 c) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 c)
      (continuous_sphericalBesselJ _).continuousOn fun t ht ↦ ?_
    rw [interior_Icc] at ht
    have h0 := hFmono ⟨le_rfl, hc0.le⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at h0
    exact pos_of_mul_pos_right h0 (sq_nonneg t)
  have hjc := hjmono ⟨le_rfl, hc0.le⟩ ⟨hc0.le, le_rfl⟩ hc0
  rw [sphericalBesselJ_succ_zero, sphericalBesselJ_eq_pow_mul] at hjc
  exact (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hc0.le _) hcT.2).not_gt hjc

/-- If `j_l` is positive on `(0, z)`, then `j_{l+1}` is positive on `(0, z]`. -/
theorem sphericalBesselJ_succ_pos_of_forall_pos {l : ℕ} {z : ℝ}
    (h : ∀ x ∈ Set.Ioo 0 z, 0 < sphericalBesselJ l x) :
    ∀ x ∈ Set.Ioc 0 z, 0 < sphericalBesselJ (l + 1) x := by
  intro x hx
  have hH := hasDerivAt_pow_mul_sphericalBesselJ_succ l
  have hmono : StrictMonoOn (fun y ↦ y ^ (l + 2) * sphericalBesselJ (l + 1) y)
      (Set.Icc 0 x) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 x)
      (fun t _ ↦ (hH t).continuousAt.continuousWithinAt) fun t ht ↦ ?_
    rw [interior_Icc] at ht
    rw [(hH t).deriv]
    exact mul_pos (pow_pos ht.1 _) (h t ⟨ht.1, ht.2.trans_le hx.2⟩)
  have h0 : (0 : ℝ) ^ (l + 2) * sphericalBesselJ (l + 1) 0 <
      x ^ (l + 2) * sphericalBesselJ (l + 1) x :=
    hmono ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hx.1
  rw [zero_pow (by omega), zero_mul] at h0
  exact pos_of_mul_pos_right h0 (pow_nonneg hx.1.le _)

/-- If `j_l` is negative on `(0, z)`, then `j_{l+1}` is negative on `(0, z]`. -/
theorem sphericalBesselJ_succ_neg_of_forall_neg {l : ℕ} {z : ℝ}
    (h : ∀ x ∈ Set.Ioo 0 z, sphericalBesselJ l x < 0) :
    ∀ x ∈ Set.Ioc 0 z, sphericalBesselJ (l + 1) x < 0 := by
  intro x hx
  have hH := hasDerivAt_pow_mul_sphericalBesselJ_succ l
  have hanti : StrictAntiOn (fun y ↦ y ^ (l + 2) * sphericalBesselJ (l + 1) y)
      (Set.Icc 0 x) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 x)
      (fun t _ ↦ (hH t).continuousAt.continuousWithinAt) fun t ht ↦ ?_
    rw [interior_Icc] at ht
    rw [(hH t).deriv]
    exact mul_neg_of_pos_of_neg (pow_pos ht.1 _) (h t ⟨ht.1, ht.2.trans_le hx.2⟩)
  have h0 : x ^ (l + 2) * sphericalBesselJ (l + 1) x <
      (0 : ℝ) ^ (l + 2) * sphericalBesselJ (l + 1) 0 :=
    hanti ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hx.1
  rw [zero_pow (by omega), zero_mul] at h0
  exact neg_of_mul_neg_right h0 (pow_nonneg hx.1.le _)

/-- On an open interval free of zeros of `j_l`, the function `j_l` has constant sign. -/
theorem sphericalBesselJ_pos_or_neg_of_forall_ne_zero {l : ℕ} {a b : ℝ}
    (hne : ∀ x ∈ Set.Ioo a b, sphericalBesselJ l x ≠ 0) :
    (∀ x ∈ Set.Ioo a b, 0 < sphericalBesselJ l x) ∨
      ∀ x ∈ Set.Ioo a b, sphericalBesselJ l x < 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨x, hx, hjx⟩, y, hy, hjy⟩ := hc
  obtain ⟨t, ht, hjt⟩ := isPreconnected_Ioo.intermediate_value hx hy
    (continuous_sphericalBesselJ l).continuousOn ⟨hjx, hjy⟩
  exact hne t ht hjt

/-- If `j_l` has no zero in `(0, z)`, it is positive there. -/
theorem sphericalBesselJ_pos_of_forall_ne_zero {l : ℕ} {z : ℝ}
    (h : ∀ x ∈ Set.Ioo 0 z, sphericalBesselJ l x ≠ 0) :
    ∀ x ∈ Set.Ioo 0 z, 0 < sphericalBesselJ l x := by
  intro x hx
  have hg0 := reducedSphericalBesselJ_zero_pos l
  have hgx : 0 < reducedSphericalBesselJ l x := by
    by_contra hg
    push Not at hg
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc' hx.1.le
      (differentiable_reducedSphericalBesselJ l).continuous.continuousOn ⟨hg, hg0.le⟩
    rcases ht.1.eq_or_lt with ht0 | ht0
    · rw [← ht0] at hgt
      exact hg0.ne' hgt
    · apply h t ⟨ht0, ht.2.trans_lt hx.2⟩
      rw [sphericalBesselJ_eq_pow_mul, hgt, mul_zero]
  rw [sphericalBesselJ_eq_pow_mul]
  exact mul_pos (pow_pos hx.1 _) hgx

end PDE.Analysis.SpecialFunctions
