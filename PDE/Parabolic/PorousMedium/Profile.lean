/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.PorousMedium.Parameters
public import PDE.Analysis.Calculus.PositivePartRpow
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import CAS.ExactTactic

/-!
# The compact Barenblatt profile and its global diffusion flux

The profile `F(y) = (C - k |y|²)₊^(1/(m-1))` (`profile`) is continuous, nonnegative and compactly
supported (`continuous_profile`, `profile_nonneg`, `hasCompactSupport_profile`), and for `C > 0` its
mass is positive (`profileMass_pos`). The diffusion potential `F^m` is `C¹` on all of `ℝⁿ`
(`contDiff_profile_potential`), and `∇(F^m)(y) = -β F(y) y` holds inside, on and outside the free
boundary `k |y|² = C` (`gradient_profile_potential`). The weak equation needs only this first-order
profile equation; `F^m` need not have a classical second derivative at the interface. SymLean's
`cas` tactic checks the algebra in the derivative of `F^m`.

This is the profile (34) of Evans's §4.2.2, with `γ = m` and `b = C`. Evans reduces the radial
equation (32) to `(w^γ)' = -βrw` and takes the positive part to make `w ≥ 0`;
`gradient_profile_potential` is the same first-order equation, proved across the free boundary.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.2.2, Example (A scaling invariant solution), (27)-(36),
  pp. 185-186.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PorousMedium

open MeasureTheory Set
open scoped Gradient RealInnerProductSpace

variable {n : ℕ}

/-- The compact Barenblatt profile with free positive parameter `C`. -/
def profile (n : ℕ) (m C : ℝ) (y : ℝ^n) : ℝ :=
  (C - profileCoefficient n m * ‖y‖ ^ 2)⁺ ^ profileExponent m

/-- The profile is nonnegative everywhere. -/
theorem profile_nonneg (m C : ℝ) (y : ℝ^n) : 0 ≤ profile n m C y :=
  Real.rpow_nonneg (posPart_nonneg _) _

/-- The profile is continuous even where its density derivative may be singular. -/
theorem continuous_profile {m : ℝ} (hm : 1 < m) (C : ℝ) :
    Continuous (profile n m C) := by
  unfold profile
  exact (Real.continuous_rpow_const (profileExponent_pos hm).le).comp
    ((continuous_const.sub (continuous_const.mul (continuous_norm.pow 2))).max continuous_const)

/-- The density vanishes on and outside the quadratic free boundary, and only there. -/
theorem profile_eq_zero_iff {m : ℝ} (hm : 1 < m) (C : ℝ) (y : ℝ^n) :
    profile n m C y = 0 ↔ C ≤ profileCoefficient n m * ‖y‖ ^ 2 := by
  rw [profile, Real.rpow_eq_zero (posPart_nonneg _) (ne_of_gt (profileExponent_pos hm)),
    posPart_eq_zero, sub_nonpos]

/-- The strict positivity region is the interior of the quadratic free boundary. -/
theorem profile_pos_iff {m : ℝ} (hm : 1 < m) (C : ℝ) (y : ℝ^n) :
    0 < profile n m C y ↔ profileCoefficient n m * ‖y‖ ^ 2 < C := by
  rw [lt_iff_le_and_ne, iff_true_intro (profile_nonneg m C y), true_and,
    ne_comm, ne_eq, profile_eq_zero_iff hm C y, not_le]

/-- The support as a set of nonzero points is the open profile ball. -/
theorem support_profile {m : ℝ} (hm : 1 < m) (C : ℝ) :
    Function.support (profile n m C) =
      {y : ℝ^n | profileCoefficient n m * ‖y‖ ^ 2 < C} := by
  ext y
  simp [Function.mem_support, profile_eq_zero_iff hm]

/-- The support lies in a compact ball of radius `sqrt(C/k)` (for `C ≤ 0` the profile is zero). -/
theorem hasCompactSupport_profile {m C : ℝ} (hm : 1 < m) :
    HasCompactSupport (profile n m C) := by
  have hk := profileCoefficient_pos n hm
  by_cases hC : 0 < C
  swap
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^n) 0) fun y _ ↦ ?_
    exact (profile_eq_zero_iff hm C y).2 ((not_lt.1 hC).trans (mul_nonneg hk.le (sq_nonneg _)))
  have hquot := (div_pos hC hk).le
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : ℝ^n) (Real.sqrt (C / profileCoefficient n m)))
  intro y hy
  apply (profile_eq_zero_iff hm C y).2
  have hr : Real.sqrt (C / profileCoefficient n m) < ‖y‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy
  have hs : C / profileCoefficient n m ≤ ‖y‖ ^ 2 := by
    rw [← Real.sq_sqrt hquot]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).2 hr.le
  simpa only [mul_comm] using (div_le_iff₀ hk).1 hs

/-- The compact profile is Lebesgue integrable. -/
theorem integrable_profile {m C : ℝ} (hm : 1 < m) :
    Integrable (profile n m C) :=
  (continuous_profile hm C).integrable_of_hasCompactSupport (hasCompactSupport_profile hm)

/-- The mass of the profile, the integral of the time-one density. -/
def profileMass (n : ℕ) (m C : ℝ) : ℝ := ∫ y : ℝ^n, profile n m C y

/-- Positive profile parameter gives strictly positive finite mass. -/
theorem profileMass_pos {m C : ℝ} (hm : 1 < m) (hC : 0 < C) :
    0 < profileMass n m C := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (continuous_profile hm C) (integrable_profile hm) (profile_nonneg m C)
  apply ne_of_gt ((profile_pos_iff hm C (0 : ℝ^n)).2 ?_)
  simpa using hC

/-- Taking the diffusion power multiplies the profile exponent. -/
theorem profile_potential_eq (m C : ℝ) (y : ℝ^n) :
    profile n m C y ^ m =
      (C - profileCoefficient n m * ‖y‖ ^ 2)⁺ ^ (profileExponent m * m) := by
  unfold profile
  rw [Real.rpow_mul (posPart_nonneg _)]

/-- The diffusion potential is `C¹` on the whole space, including its free boundary. -/
theorem contDiff_profile_potential {m : ℝ} (hm : 1 < m) (C : ℝ) :
    ContDiff ℝ 1 (fun y : ℝ^n ↦ profile n m C y ^ m) := by
  simp_rw [profile_potential_eq]
  exact (PDE.Analysis.contDiff_one_posPart_rpow (potential_exponent_gt_one hm)).comp
    (contDiff_const.sub (contDiff_const.mul (contDiff_id.norm_sq ℝ)))

/-- The global first derivative of the diffusion potential has no interface term. -/
theorem hasFDerivAt_profile_potential {m : ℝ} (hm : 1 < m) (C : ℝ) (y : ℝ^n) :
    HasFDerivAt (fun z : ℝ^n ↦ profile n m C z ^ m)
      ((-similarityBeta n m * profile n m C y) • innerSL ℝ y) y := by
  have hgap := ((hasFDerivAt_id y).norm_sq.const_mul (profileCoefficient n m)).const_sub C
  have hpow := (PDE.Analysis.hasDerivAt_posPart_rpow (potential_exponent_gt_one hm)
    (C - profileCoefficient n m * ‖y‖ ^ 2)).comp_hasFDerivAt y hgap
  simp_rw [profile_potential_eq]
  convert hpow using 1
  · rfl
  · ext v
    simp only [smul_apply, neg_apply, innerSL_apply_apply, smul_eq_mul,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, id_eq,
      potential_exponent_sub_one hm]
    unfold profile
    have hbalance := profile_coefficient_balance n hm
    cas using hbalance

/-- The global profile equation in flux form, valid across the free boundary. -/
theorem gradient_profile_potential {m : ℝ} (hm : 1 < m) (C : ℝ) (y : ℝ^n) :
    ∇ (fun z : ℝ^n ↦ profile n m C z ^ m) y =
      (-similarityBeta n m * profile n m C y) • y := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, (hasFDerivAt_profile_potential hm C y).fderiv]
  simp [inner_smul_left]

end PorousMedium
