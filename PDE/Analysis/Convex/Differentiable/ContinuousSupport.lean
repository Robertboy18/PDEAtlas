/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Continuous supporting functionals are derivatives

A supporting functional bounds the first-order remainder from below by zero.
The support at the neighboring point bounds it from above by the change in the
supporting functional times the displacement. Continuity therefore makes the
remainder little-o of the displacement.

The argument works in any real normed space and uses no compactness,
completeness, or prior differentiability of the function.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous field of supporting continuous linear functionals is the
Fréchet derivative. Continuity is needed only at the point in question. -/
theorem hasFDerivAt_of_continuous_support
    {f : E → ℝ} {A : E → E →L[ℝ] ℝ} {x : E}
    (hsupport : ∀ u v, A u (v - u) ≤ f v - f u)
    (hA : ContinuousAt A x) :
    HasFDerivAt f (A x) x := by
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hsmall : ∀ᶠ y in 𝓝 x, ‖A y - A x‖ < ε := by
    have hnorm : ContinuousAt (fun y ↦ ‖A y - A x‖) x :=
      (hA.sub continuousAt_const).norm
    exact hnorm.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [hsmall] with y hy
  have hlow := hsupport x y
  have hupp := hsupport y x
  have hneg : A y (x - y) = -(A y (y - x)) := by
    rw [← map_neg, neg_sub]
  rw [hneg] at hupp
  have hrem : 0 ≤ f y - f x - A x (y - x) := sub_nonneg.mpr hlow
  rw [Real.norm_of_nonneg hrem]
  calc
    f y - f x - A x (y - x) ≤ (A y - A x) (y - x) := by
      simp only [sub_apply]
      linarith only [hupp]
    _ ≤ ‖(A y - A x) (y - x)‖ := le_abs_self _
    _ ≤ ‖A y - A x‖ * ‖y - x‖ := (A y - A x).le_opNorm _
    _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hy.le (norm_nonneg _)

/-- The scalar specialization: continuous supporting slopes are
derivatives, with no prior differentiability assumption. -/
theorem hasDerivAt_of_continuous_support
    {f a : ℝ → ℝ} {x : ℝ}
    (hsupport : ∀ u v, a u * (v - u) ≤ f v - f u)
    (ha : ContinuousAt a x) :
    HasDerivAt f (a x) x := by
  have h := hasFDerivAt_of_continuous_support
    (A := fun u ↦ a u • ContinuousLinearMap.id ℝ ℝ)
    (by simpa only [smul_apply, ContinuousLinearMap.id_apply,
      smul_eq_mul] using hsupport)
    (ha.smul continuousAt_const)
  simpa using h.hasDerivAt

end PDE.Analysis
