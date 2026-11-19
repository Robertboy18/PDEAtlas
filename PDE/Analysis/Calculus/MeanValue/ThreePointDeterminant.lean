/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CAS.ExactTactic

/-!
# Three-point determinants from negative relative curvature

For two real functions `R` and `Q`, positivity of `R'` and negativity of
`Q'' - (R'' / R') * Q'` make `Q' / R'` strictly decreasing. Cauchy's mean
value theorem then compares the secants on two successive intervals.
The determinant with columns `(1, R x, Q x)` at three increasing points
is strictly negative.

The functions need only be twice continuously differentiable on the open
interval containing the three points. No inverse coordinate is constructed.
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis

private theorem strictAntiOn_deriv_ratio_of_curvature_neg
    {R Q : ℝ → ℝ} {a b : ℝ}
    (hR : ContDiffOn ℝ 2 R (Ioo a b)) (hQ : ContDiffOn ℝ 2 Q (Ioo a b))
    (hRp : ∀ x ∈ Ioo a b, 0 < deriv R x)
    (hcurv : ∀ x ∈ Ioo a b,
      deriv (deriv Q) x - deriv (deriv R) x / deriv R x * deriv Q x < 0) :
    StrictAntiOn (fun x ↦ deriv Q x / deriv R x) (Ioo a b) := by
  have hR1 : ContDiffOn ℝ 1 (deriv R) (Ioo a b) :=
    hR.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hQ1 : ContDiffOn ℝ 1 (deriv Q) (Ioo a b) :=
    hQ.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hquot (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun y ↦ deriv Q y / deriv R y)
        ((deriv (deriv Q) x * deriv R x - deriv Q x * deriv (deriv R) x) /
          deriv R x ^ 2) x := by
    have hQx : DifferentiableAt ℝ (deriv Q) x :=
      hQ1.differentiableOn_one.differentiableAt (isOpen_Ioo.mem_nhds hx)
    have hRx : DifferentiableAt ℝ (deriv R) x :=
      hR1.differentiableOn_one.differentiableAt (isOpen_Ioo.mem_nhds hx)
    exact hQx.hasDerivAt.fun_div hRx.hasDerivAt (hRp x hx).ne'
  refine strictAntiOn_of_deriv_neg (convex_Ioo a b)
    (fun x hx ↦ (hquot x hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  have hx' : x ∈ Ioo a b := interior_subset hx
  rw [(hquot x hx').deriv]
  apply div_neg_of_neg_of_pos ?_ (sq_pos_of_pos (hRp x hx'))
  have hlt := sub_neg.mp (hcurv x hx')
  rw [div_mul_eq_mul_div, mul_comm (deriv (deriv R) x) (deriv Q x)] at hlt
  exact sub_neg.mpr ((lt_div_iff₀ (hRp x hx')).mp hlt)

/-- Negative relative curvature makes the second of two successive secants
strictly smaller than the first. The denominators are positive because `R'`
is positive throughout the open interval. -/
theorem successive_secants_lt_of_curvature_neg
    {R Q : ℝ → ℝ} {a b x0 x1 x2 : ℝ}
    (hR : ContDiffOn ℝ 2 R (Ioo a b)) (hQ : ContDiffOn ℝ 2 Q (Ioo a b))
    (hRp : ∀ x ∈ Ioo a b, 0 < deriv R x)
    (hcurv : ∀ x ∈ Ioo a b,
      deriv (deriv Q) x - deriv (deriv R) x / deriv R x * deriv Q x < 0)
    (ha : a < x0) (h01 : x0 < x1) (h12 : x1 < x2) (hb : x2 < b) :
    (Q x2 - Q x1) / (R x2 - R x1) <
      (Q x1 - Q x0) / (R x1 - R x0) := by
  have hanti := strictAntiOn_deriv_ratio_of_curvature_neg hR hQ hRp hcurv
  have hmono : StrictMonoOn R (Ioo a b) :=
    strictMonoOn_of_deriv_pos (convex_Ioo a b) hR.continuousOn
      (fun x hx ↦ hRp x (interior_subset hx))
  have hx0 : x0 ∈ Ioo a b := ⟨ha, h01.trans (h12.trans hb)⟩
  have hx1 : x1 ∈ Ioo a b := ⟨ha.trans h01, h12.trans hb⟩
  have hx2 : x2 ∈ Ioo a b := ⟨(ha.trans h01).trans h12, hb⟩
  have hR01 : 0 < R x1 - R x0 := sub_pos.mpr (hmono hx0 hx1 h01)
  have hR12 : 0 < R x2 - R x1 := sub_pos.mpr (hmono hx1 hx2 h12)
  have hsub01 : Icc x0 x1 ⊆ Ioo a b := by
    intro x hx
    exact ⟨ha.trans_le hx.1, hx.2.trans_lt (h12.trans hb)⟩
  have hsub12 : Icc x1 x2 ⊆ Ioo a b := by
    intro x hx
    exact ⟨(ha.trans h01).trans_le hx.1, hx.2.trans_lt hb⟩
  have hRd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt R (deriv R x) x :=
    ((hR.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hQd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt Q (deriv Q x) x :=
    ((hQ.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  obtain ⟨c0, hc0, heq0⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    Q (deriv Q) h01 (hQ.continuousOn.mono hsub01)
      (fun x hx ↦ hQd x (hsub01 ⟨hx.1.le, hx.2.le⟩))
    R (deriv R) (hR.continuousOn.mono hsub01)
      (fun x hx ↦ hRd x (hsub01 ⟨hx.1.le, hx.2.le⟩))
  obtain ⟨c1, hc1, heq1⟩ := exists_ratio_hasDerivAt_eq_ratio_slope
    Q (deriv Q) h12 (hQ.continuousOn.mono hsub12)
      (fun x hx ↦ hQd x (hsub12 ⟨hx.1.le, hx.2.le⟩))
    R (deriv R) (hR.continuousOn.mono hsub12)
      (fun x hx ↦ hRd x (hsub12 ⟨hx.1.le, hx.2.le⟩))
  have hc0' : c0 ∈ Ioo a b := hsub01 ⟨hc0.1.le, hc0.2.le⟩
  have hc1' : c1 ∈ Ioo a b := hsub12 ⟨hc1.1.le, hc1.2.le⟩
  have hsec0 : (Q x1 - Q x0) / (R x1 - R x0) = deriv Q c0 / deriv R c0 :=
    (div_eq_div_iff hR01.ne' (hRp c0 hc0').ne').mpr
      (heq0.symm.trans (mul_comm _ _))
  have hsec1 : (Q x2 - Q x1) / (R x2 - R x1) = deriv Q c1 / deriv R c1 :=
    (div_eq_div_iff hR12.ne' (hRp c1 hc1').ne').mpr
      (heq1.symm.trans (mul_comm _ _))
  calc
    (Q x2 - Q x1) / (R x2 - R x1) = deriv Q c1 / deriv R c1 := hsec1
    _ < deriv Q c0 / deriv R c0 := hanti hc0' hc1' (hc0.2.trans hc1.1)
    _ = (Q x1 - Q x0) / (R x1 - R x0) := hsec0.symm

/-- At three increasing points, the matrix with columns `(1, R x, Q x)`
has strictly negative determinant if `R'` is positive and the relative curvature
`Q'' - (R'' / R') * Q'` is negative. In particular these columns are independent. -/
theorem three_point_det_neg_of_curvature_neg
    {R Q : ℝ → ℝ} {a b x0 x1 x2 : ℝ}
    (hR : ContDiffOn ℝ 2 R (Ioo a b)) (hQ : ContDiffOn ℝ 2 Q (Ioo a b))
    (hRp : ∀ x ∈ Ioo a b, 0 < deriv R x)
    (hcurv : ∀ x ∈ Ioo a b,
      deriv (deriv Q) x - deriv (deriv R) x / deriv R x * deriv Q x < 0)
    (ha : a < x0) (h01 : x0 < x1) (h12 : x1 < x2) (hb : x2 < b) :
    Matrix.det !![1, 1, 1; R x0, R x1, R x2; Q x0, Q x1, Q x2] < 0 := by
  have hsec := successive_secants_lt_of_curvature_neg hR hQ hRp hcurv ha h01 h12 hb
  have hmono : StrictMonoOn R (Ioo a b) :=
    strictMonoOn_of_deriv_pos (convex_Ioo a b) hR.continuousOn
      (fun x hx ↦ hRp x (interior_subset hx))
  have hx0 : x0 ∈ Ioo a b := ⟨ha, h01.trans (h12.trans hb)⟩
  have hx1 : x1 ∈ Ioo a b := ⟨ha.trans h01, h12.trans hb⟩
  have hx2 : x2 ∈ Ioo a b := ⟨(ha.trans h01).trans h12, hb⟩
  have hR01 : 0 < R x1 - R x0 := sub_pos.mpr (hmono hx0 hx1 h01)
  have hR12 : 0 < R x2 - R x1 := sub_pos.mpr (hmono hx1 hx2 h12)
  have hcross := (div_lt_div_iff₀ hR12 hR01).mp hsec
  have hformula :
      Matrix.det !![1, 1, 1; R x0, R x1, R x2; Q x0, Q x1, Q x2] =
        (R x1 - R x0) * (Q x2 - Q x1) - (R x2 - R x1) * (Q x1 - Q x0) := by
    rw [Matrix.det_fin_three]
    change
      1 * R x1 * Q x2 - 1 * R x2 * Q x1 - 1 * R x0 * Q x2 +
          1 * R x2 * Q x0 + 1 * R x0 * Q x1 - 1 * R x1 * Q x0 =
        (R x1 - R x0) * (Q x2 - Q x1) - (R x2 - R x1) * (Q x1 - Q x0)
    generalize R x0 = r0
    generalize R x1 = r1
    generalize R x2 = r2
    generalize Q x0 = q0
    generalize Q x1 = q1
    generalize Q x2 = q2
    cas
  rw [hformula]
  rw [mul_comm (Q x2 - Q x1) (R x1 - R x0),
    mul_comm (Q x1 - Q x0) (R x2 - R x1)] at hcross
  exact sub_neg.mpr hcross

end PDE.Analysis
