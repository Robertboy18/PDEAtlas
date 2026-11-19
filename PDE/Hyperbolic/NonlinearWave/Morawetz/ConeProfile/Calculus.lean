/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime
public import Mathlib.Analysis.Normed.Module.Normalize
import PDE.FDeriv.Euclidean.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Pulling a field back to a backward cone

The cone profile may have a singularity at its tip. Away from the tip the
chain rule identifies its gradient with the tangential derivative.
-/

@[expose] public noncomputable section

open PDE PDE.Common NormedSpace
open scoped RealInnerProductSpace

namespace WaveEquation

variable {n : ℕ}

/-- The spatial parametrization of a backward cone, including its totalized tip value. -/
def coneProfile (T : ℝ) (c : ℝ^n) (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) : ℝ :=
  u (timeSpaceCons (T - ‖x - c‖) x)

/-- The tangential gradient along the backward cone. -/
def coneProfileGradient (T : ℝ) (c : ℝ^n) (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) : ℝ^n :=
  WithLp.toLp 2 fun i ↦
    (∂[i.succ] u) (timeSpaceCons (T - ‖x - c‖) x) -
      (∂[0] u) (timeSpaceCons (T - ‖x - c‖) x) * normalize (x - c) i

/-- Cone pullback preserves C¹ regularity away from the tip. -/
theorem contDiffAt_coneProfile {T : ℝ} {c x : ℝ^n} {u : ℝ^(n + 1) → ℝ}
    (hx : x ≠ c) (hu : ContDiffAt ℝ 1 u (timeSpaceCons (T - ‖x - c‖) x)) :
    ContDiffAt ℝ 1 (coneProfile T c u) x := by
  unfold coneProfile
  apply hu.comp x (f := fun y ↦ timeSpaceCons (T - ‖y - c‖) y)
  exact (contDiff_timeSpaceCons_uncurry n).contDiffAt.comp x
    ((contDiffAt_const.sub ((contDiffAt_id.sub contDiffAt_const).norm ℝ
      (sub_ne_zero.mpr hx))).prodMk contDiffAt_id)

private theorem fderiv_dist_apply {c x v : ℝ^n} (hx : x ≠ c) :
    fderiv ℝ (fun y ↦ ‖y - c‖) x v = ⟪normalize (x - c), v⟫ := by
  have h := (EuclideanNorm.hasFDerivAt_norm_of_ne_zero (sub_ne_zero.mpr hx)).comp x
    ((hasFDerivAt_id x).sub_const c)
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id,
    NormedSpace.normalize, innerSL_apply_apply] using congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L v) h.fderiv

/-- The derivative of the cone pullback is the spatial derivative minus the radial time term. -/
theorem fderiv_coneProfile_apply {T : ℝ} {c x : ℝ^n} {u : ℝ^(n + 1) → ℝ} (hx : x ≠ c)
    (hu : DifferentiableAt ℝ u (timeSpaceCons (T - ‖x - c‖) x)) (v : ℝ^n) :
    fderiv ℝ (coneProfile T c u) x v = fderiv ℝ (fun y ↦ u (timeSpaceCons (T - ‖x - c‖) y)) x v -
      (∂[0] u) (timeSpaceCons (T - ‖x - c‖) x) * ⟪normalize (x - c), v⟫ := by
  have hn := ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.mpr hx)).differentiableAt
    (show (1 : WithTop ℕ∞) ≠ 0 by simp)
  have hpair := (hn.hasFDerivAt.const_sub T).prodMk (hasFDerivAt_id x)
  have hj := (timeSpaceContinuousLinearEquiv n).symm.hasFDerivAt.comp x hpair
  have hc := hu.hasFDerivAt.comp x (f := fun y ↦ timeSpaceCons (T - ‖y - c‖) y)
    (by simpa only [Function.comp_def, timeSpaceContinuousLinearEquiv_symm_apply, id] using hj)
  have hs := hu.hasFDerivAt.comp x (hasFDerivAt_timeSpaceCons_spatial n (T - ‖x - c‖) x)
  have hc' := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L v) hc.fderiv
  have hs' := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L v) hs.fderiv
  change fderiv ℝ (coneProfile T c u) x v = _ at hc'
  change fderiv ℝ (fun y ↦ u (timeSpaceCons (T - ‖x - c‖) y)) x v = _ at hs'
  rw [hc', hs']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    neg_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_apply, timeSpaceContinuousLinearEquiv_symm_apply,
    fderiv_dist_apply hx]
  have he : timeSpaceCons (-⟪normalize (x - c), v⟫) v = embedWithTimeZeroCLM n v -
        ⟪normalize (x - c), v⟫ • EuclideanSpace.single (0 : Fin (n + 1)) 1 := by
    ext i
    cases i using Fin.cases <;> simp
  rw [he, map_sub, map_smul]
  simp only [smul_eq_mul, partialDeriv]
  ring

/-- Each coordinate of the classical profile gradient is the tangential spacetime derivative. -/
theorem partialDeriv_coneProfile {T : ℝ} {c x : ℝ^n} {u : ℝ^(n + 1) → ℝ} (hx : x ≠ c)
    (hu : DifferentiableAt ℝ u (timeSpaceCons (T - ‖x - c‖) x)) (i : Fin n) :
    (∂[i] (coneProfile T c u)) x = coneProfileGradient T c u x i := by
  rw [partialDeriv, fderiv_coneProfile_apply hx hu]
  change (∂[i] (fun y ↦ u (timeSpaceCons (T - ‖x - c‖) y))) x - _ = _
  rw [partialDeriv_timeSpaceCons_spatial i u _ x hu]
  simp [coneProfileGradient, EuclideanSpace.inner_single_right]

/-- The tangential gradient represents the full derivative of the cone profile. -/
theorem fderiv_coneProfile_apply_eq_inner {T : ℝ} {c x : ℝ^n} {u : ℝ^(n + 1) → ℝ} (hx : x ≠ c)
    (hu : DifferentiableAt ℝ u (timeSpaceCons (T - ‖x - c‖) x)) (v : ℝ^n) :
    fderiv ℝ (coneProfile T c u) x v = ⟪coneProfileGradient T c u x, v⟫ := by
  rw [fderiv_apply_eq_sum_partialDeriv_mul]
  simp only [partialDeriv_coneProfile hx hu, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, mul_comm]


end WaveEquation
