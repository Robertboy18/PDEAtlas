/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

import CAS.ExactTactic

/-!
# Taylor bounds along a normal segment

A linear bound on a Hessian field gives quadratic and cubic Taylor bounds by
vector-valued mean value comparison. The derivative fields may be specified only
within the closed segment, so the estimate applies at a domain boundary. A bound
on the third derivative supplies the Hessian envelope for a smooth function.
Neither space needs to be complete.

When the value, derivative and Hessian vanish at the base point, a bound `K` on the third
derivative gives `‖Q x‖ / ‖x - base‖³ ≤ K / 6`. This is the reduction of a singular weighted
estimate to a `C³` bound, `|x|⁻³ |f(x)| ≲ ‖∇³ f‖_{L∞}` for `f(x) = O(|x|³)`, in Chen and Hou,
Part I, Section 2.8.4.

## Main results

* `normal_segment_taylor_bounds_of_derivative_fields`: if `Q` and its derivative vanish at
  `base` and the Hessian is bounded by `M + K ‖y - base‖` on the segment, then
  `‖D x‖ ≤ M r + K r² / 2` and `‖Q x‖ ≤ M r² / 2 + K r³ / 6`, where `r = ‖x - base‖`.
* `normal_segment_taylor_bounds`: the same bounds for a `C³` function from `‖D²Q(base)‖ ≤ M`
  and a bound `K` on the third derivative along the segment.
* `norm_div_cube_le_of_derivative_fields`, `norm_div_cube_le_of_second_jet_eq_zero`: the cubic
  singular-weight bound `‖Q x‖ / ‖x - base‖³ ≤ K / 6`, from a Hessian bound `K ‖y - base‖`
  or from a third-derivative bound `K` when the second jet vanishes at `base`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.8.4.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A linear Hessian envelope gives quadratic and cubic Taylor bounds.
The supplied derivative fields need only be derivatives within the segment. In
particular, no derivative of the Hessian or extension across a boundary is needed. -/
theorem normal_segment_taylor_bounds_of_derivative_fields {Q : E → F}
    {D : E → E →L[ℝ] F} {H : E → E →L[ℝ] E →L[ℝ] F} {base x : E} {M K : ℝ}
    (hQ : ∀ y ∈ segment ℝ base x, HasFDerivWithinAt Q (D y) (segment ℝ base x) y)
    (hD : ∀ y ∈ segment ℝ base x, HasFDerivWithinAt D (H y) (segment ℝ base x) y)
    (hH : ∀ y ∈ segment ℝ base x, ‖H y‖ ≤ M + K * ‖y - base‖)
    (hzero : Q base = 0) (hDzero : D base = 0) :
    ‖D x‖ ≤ M * ‖x - base‖ + K * ‖x - base‖ ^ 2 / 2 ∧
      ‖Q x‖ ≤ M * ‖x - base‖ ^ 2 / 2 + K * ‖x - base‖ ^ 3 / 6 := by
  let d := x - base
  let r := ‖d‖
  let γ : ℝ → E := AffineMap.lineMap base x
  have hr : 0 ≤ r := norm_nonneg d
  have hγzero : γ 0 = base := AffineMap.lineMap_apply_zero base x
  have hγone : γ 1 = x := AffineMap.lineMap_apply_one base x
  have hγmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      γ t ∈ segment ℝ base x := lineMap_mem_segment ℝ base x ht
  have hγmaps : MapsTo γ (Icc (0 : ℝ) 1) (segment ℝ base x) := fun t ht ↦ hγmem t ht
  have hQd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s ↦ Q (γ s)) (D (γ t) d) (Icc (0 : ℝ) 1) t :=
    (hQ (γ t) (hγmem t ht)).comp_hasDerivWithinAt t
      AffineMap.hasDerivWithinAt_lineMap hγmaps
  have hDd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (fun s ↦ D (γ s)) (H (γ t) d) (Icc (0 : ℝ) 1) t :=
    (hD (γ t) (hγmem t ht)).comp_hasDerivWithinAt t
      AffineMap.hasDerivWithinAt_lineMap hγmaps
  have hHnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖H (γ t)‖ ≤ M + K * r * t := by
    have hdist : ‖γ t - base‖ = r * t := by
      simp only [γ, AffineMap.lineMap_apply_module', add_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_comm t r
    simpa only [hdist, mul_assoc] using hH (γ t) (hγmem t ht)
  -- Comparison of the operator-valued derivative retains the factor one half.
  let B₁ : ℝ → ℝ := fun t ↦ M * r * t + K * r ^ 2 * t ^ 2 / 2
  have hB₁ (t : ℝ) : HasDerivAt B₁ ((M + K * r * t) * r) t := by
    dsimp only [B₁]
    cas
  have hDnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖D (γ t)‖ ≤ B₁ t := by
    apply image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s ↦ D (γ s)) (f' := fun s ↦ H (γ s) d)
      (a := 0) (b := 1) (B := B₁) (B' := fun s ↦ (M + K * r * s) * r)
      (fun s hs ↦ (hDd s hs).continuousWithinAt)
      (fun s hs ↦ (hDd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs))
      (by simp [B₁, hγzero, hDzero]) hB₁ ?_ ht
    intro s hs
    exact ((H (γ s)).le_opNorm d).trans
      (mul_le_mul_of_nonneg_right (hHnorm s ⟨hs.1, hs.2.le⟩) hr)
  -- A second comparison gives the cubic remainder without an integral or completeness.
  let B₀ : ℝ → ℝ := fun t ↦ M * r ^ 2 * t ^ 2 / 2 + K * r ^ 3 * t ^ 3 / 6
  have hB₀ (t : ℝ) : HasDerivAt B₀ (B₁ t * r) t := by
    dsimp only [B₀, B₁]
    cas
  have hQnorm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ‖Q (γ t)‖ ≤ B₀ t := by
    apply image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun s ↦ Q (γ s)) (f' := fun s ↦ D (γ s) d)
      (a := 0) (b := 1) (B := B₀) (B' := fun s ↦ B₁ s * r)
      (fun s hs ↦ (hQd s hs).continuousWithinAt)
      (fun s hs ↦ (hQd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs))
      (by simp [B₀, hγzero, hzero]) hB₀ ?_ ht
    intro s hs
    exact ((D (γ s)).le_opNorm d).trans
      (mul_le_mul_of_nonneg_right (hDnorm s ⟨hs.1, hs.2.le⟩) hr)
  constructor
  · simpa only [B₁, hγone, one_pow, mul_one, r, d] using
      hDnorm 1 ⟨zero_le_one, le_rfl⟩
  · simpa only [B₀, hγone, one_pow, mul_one, r, d] using
      hQnorm 1 ⟨zero_le_one, le_rfl⟩

/-- A Hessian bounded by distance from the base gives a cubic singular-weight
bound. Derivatives within the segment suffice, even if the segment starts on or
lies along a domain boundary. The Hessian need not itself be differentiable. -/
theorem norm_div_cube_le_of_derivative_fields {Q : E → F}
    {D : E → E →L[ℝ] F} {H : E → E →L[ℝ] E →L[ℝ] F} {base x : E} {K : ℝ}
    (hQ : ∀ y ∈ segment ℝ base x, HasFDerivWithinAt Q (D y) (segment ℝ base x) y)
    (hD : ∀ y ∈ segment ℝ base x, HasFDerivWithinAt D (H y) (segment ℝ base x) y)
    (hH : ∀ y ∈ segment ℝ base x, ‖H y‖ ≤ K * ‖y - base‖)
    (hzero : Q base = 0) (hDzero : D base = 0) (hx : x ≠ base) :
    ‖Q x‖ / ‖x - base‖ ^ 3 ≤ K / 6 := by
  have hbound := normal_segment_taylor_bounds_of_derivative_fields
    (Q := Q) (D := D) (H := H) (base := base) (x := x) (M := 0) (K := K)
    hQ hD (fun y hy ↦ by simpa using hH y hy) hzero hDzero
  have hnorm : 0 < ‖x - base‖ ^ 3 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) 3
  apply (div_le_iff₀ hnorm).mpr
  calc
    ‖Q x‖ ≤ K * ‖x - base‖ ^ 3 / 6 := by simpa using hbound.2
    _ = K / 6 * ‖x - base‖ ^ 3 := by ring

/-- A third derivative bound on the closed segment gives Taylor bounds for the
Hessian, derivative and value. The value and derivative vanish only at
`base`; the Hessian there is bounded by `M`. The scalar `K` bounds the norm of
the third derivative as a curried continuous trilinear map. No positive distance,
finite-dimensionality, completeness or global regularity hypothesis is needed. -/
theorem normal_segment_taylor_bounds {Q : E → F} {base x : E} {M K : ℝ}
    (hQ : ∀ y ∈ segment ℝ base x, ContDiffAt ℝ 3 Q y)
    (hthird : ∀ y ∈ segment ℝ base x,
      ContinuousLinearMap.opNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
        (F := E →L[ℝ] E →L[ℝ] F) (fderiv ℝ (fderiv ℝ (fderiv ℝ Q)) y) ≤ K)
    (hzero : Q base = 0) (hderiv_zero : fderiv ℝ Q base = 0)
    (hbase : ‖fderiv ℝ (fderiv ℝ Q) base‖ ≤ M) :
    ‖fderiv ℝ (fderiv ℝ Q) x - fderiv ℝ (fderiv ℝ Q) base‖ ≤ K * ‖x - base‖ ∧
      ‖fderiv ℝ Q x‖ ≤ M * ‖x - base‖ + K * ‖x - base‖ ^ 2 / 2 ∧
      ‖Q x‖ ≤ M * ‖x - base‖ ^ 2 / 2 + K * ‖x - base‖ ^ 3 / 6 := by
  let D := fderiv ℝ Q
  let H := fderiv ℝ D
  have hD (y : E) (hy : y ∈ segment ℝ base x) : ContDiffAt ℝ 2 D y :=
    (hQ y hy).fderiv_right (by norm_num)
  have hHdiff (y : E) (hy : y ∈ segment ℝ base x) :
      ‖H y - H base‖ ≤ K * ‖y - base‖ := by
    have hHreg (z : E) (hz : z ∈ segment ℝ base x) : DifferentiableAt ℝ H z :=
      ((hD z hz).fderiv_right
        (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableAt_one
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (E := E) (G := E →L[ℝ] E →L[ℝ] F) (f := H)
      (s := segment ℝ base x) (x := base) (y := y) (C := K)
      hHreg hthird (convex_segment base x) (left_mem_segment ℝ base x) hy
  have hbound := normal_segment_taylor_bounds_of_derivative_fields
    (Q := Q) (D := D) (H := H) (base := base) (x := x) (M := M) (K := K)
    (fun y hy ↦ ((hQ y hy).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
    (fun y hy ↦ ((hD y hy).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt)
    (fun y hy ↦ (norm_le_norm_add_norm_sub' (H y) (H base)).trans
      (add_le_add hbase (hHdiff y hy))) hzero hderiv_zero
  exact ⟨hHdiff x (right_mem_segment ℝ base x), hbound⟩

/-- Vanishing of the value, gradient and Hessian removes the cubic singular weight.
Only a third derivative bound along the segment from the base point is needed;
the factor `1 / 6` is retained for numerical error budgets. -/
theorem norm_div_cube_le_of_second_jet_eq_zero {Q : E → F} {base x : E} {K : ℝ}
    (hQ : ∀ y ∈ segment ℝ base x, ContDiffAt ℝ 3 Q y)
    (hthird : ∀ y ∈ segment ℝ base x,
      ContinuousLinearMap.opNorm (𝕜 := ℝ) (𝕜₂ := ℝ) (E := E)
        (F := E →L[ℝ] E →L[ℝ] F) (fderiv ℝ (fderiv ℝ (fderiv ℝ Q)) y) ≤ K)
    (hzero : Q base = 0) (hfirst : fderiv ℝ Q base = 0)
    (hsecond : fderiv ℝ (fderiv ℝ Q) base = 0) (hx : x ≠ base) :
    ‖Q x‖ / ‖x - base‖ ^ 3 ≤ K / 6 := by
  have hbound := normal_segment_taylor_bounds hQ hthird hzero hfirst
    (M := 0) (by simp only [hsecond, ContinuousLinearMap.opNorm_zero, le_refl])
  have hnorm : 0 < ‖x - base‖ ^ 3 := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) 3
  apply (div_le_iff₀ hnorm).mpr
  calc
    ‖Q x‖ ≤ K * ‖x - base‖ ^ 3 / 6 := by simpa using hbound.2.2
    _ = K / 6 * ‖x - base‖ ^ 3 := by ring

end PDE.Analysis
