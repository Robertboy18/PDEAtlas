/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Equation
public import PDE.Parabolic.Heat.MeanValue.Geometry
import PDE.FDeriv.SpaceTime
import PDE.Representations.Similarity.Calculus
import CAS.ExactTactic
import PDE.FDeriv.Calculus

/-!
# Scale differentiation for the heat-ball mean-value formula

The heat-ball change of variables uses the affine parabolic map

`p ↦ (t + r² time(p), x + r spatialPart(p))`.

We differentiate this map in `r` and prove the chain rule for a scalar
spacetime field along it.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, proof of Theorem 3 (rescaling to the unit heat
  ball).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime laplacian time)

noncomputable section

namespace HeatEquation

open PDE.Common

variable {n : ℕ}

/-- The velocity of parabolic dilation with respect to its scale is
`(2 r s, y)` at a unit-coordinate point `(s,y)`. -/
theorem hasDerivAt_heatBallParabolicMap_scale
    (x : ℝ^n) (t r : ℝ) (p : SpaceTime n) :
    HasDerivAt (fun a : ℝ ↦ heatBallParabolicMap x t a p)
      (timeSpaceCons (2 * r * time p) (spatialPart p)) r := by
  let e :=
    PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (n + 1) ↦ ℝ)
  have hcoordinates :
      HasDerivAt
      (fun a : ℝ ↦ e (heatBallParabolicMap x t a p))
        (e (timeSpaceCons (2 * r * time p) (spatialPart p))) r := by
    rw [hasDerivAt_pi]
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [e, heatBallParabolicMap, timeSpaceCons_zero,
        PiLp.continuousLinearEquiv_apply]
      cas
    · simp only [e, heatBallParabolicMap, timeSpaceCons_succ,
        PiLp.continuousLinearEquiv_apply, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul]
      cas
  exact e.symm.hasFDerivAt.comp_hasDerivAt r hcoordinates

/-- Chain rule for a scalar field evaluated along parabolic dilation. -/
theorem hasDerivAt_comp_heatBallParabolicMap_scale
    {u : SpaceTime n → ℝ}
    (x : ℝ^n) (t r : ℝ) (p : SpaceTime n)
    (hu : DifferentiableAt ℝ u (heatBallParabolicMap x t r p)) :
    HasDerivAt
      (fun a : ℝ ↦ u (heatBallParabolicMap x t a p))
      ((2 * r * time p) *
          (∂[0] u) (heatBallParabolicMap x t r p) +
        ∑ j : Fin n,
          spatialPart p j *
            (∂[j.succ] u) (heatBallParabolicMap x t r p)) r := by
  have hcomp :=
    hu.hasFDerivAt.comp_hasDerivAt r
      (hasDerivAt_heatBallParabolicMap_scale x t r p)
  rw [PDE.fderiv_apply_eq_sum_partialDeriv_mul, Fin.sum_univ_succ] at hcomp
  simp only [timeSpaceCons_zero, timeSpaceCons_succ] at hcomp
  simpa only [Function.comp_def, mul_comm] using hcomp

/-- Backward parabolic pullback converts the heat residual into
`∂τv + Δv`, with the expected factor `-r²`.

For `v(τ,y) = u(t - r²τ, x + r y)`, this is the pointwise identity
`vτ + Δv = -r² (uₜ - Δu)`. -/
theorem deriv_backward_parabolic_pullback_add_laplacian
    (u : SpaceTime n → ℝ) (hu : ContDiff ℝ 1 u)
    (huSpace : ∀ s, ContDiff ℝ 2 (fun z ↦ u (timeSpaceCons s z)))
    (x : ℝ^n) (t r τ : ℝ) (y : ℝ^n) :
    deriv
          (fun s ↦
            u (timeSpaceCons (t - r ^ 2 * s) (x + r • y))) τ +
        laplacian
          (fun z ↦
            u (timeSpaceCons (t - r ^ 2 * τ) (x + r • z))) y =
      -(r ^ 2) *
        heatOperator u
          (timeSpaceCons (t - r ^ 2 * τ) (x + r • y)) := by
  let p : SpaceTime n :=
    timeSpaceCons (t - r ^ 2 * τ) (x + r • y)
  have huAt : DifferentiableAt ℝ u p :=
    (hu.differentiable (by norm_num)).differentiableAt
  have htimeArgument :
      HasDerivAt (fun s : ℝ ↦ t - r ^ 2 * s) (-(r ^ 2)) τ := by
    cas
  have htime :
      HasDerivAt
        (fun s ↦
          u (timeSpaceCons (t - r ^ 2 * s) (x + r • y)))
        (-(r ^ 2) * (∂[0] u) p) τ := by
    have hraw :=
      HasDerivAt.comp τ
        (PDE.hasDerivAt_timeSpaceCons u
          (t - r ^ 2 * τ) (x + r • y) huAt)
        htimeArgument
    with_reducible_and_instances
      simpa only [Function.comp_def, p, mul_comm] using hraw
  let profile : ℝ^n → ℝ :=
    fun z ↦ u (timeSpaceCons (t - r ^ 2 * τ) z)
  have hprofile : ContDiff ℝ 2 profile :=
    huSpace (t - r ^ 2 * τ)
  have hshift : ContDiff ℝ 2 (fun z ↦ profile (x + z)) :=
    hprofile.comp (contDiff_const.add contDiff_id)
  have hdilation :=
    PDE.Representations.Similarity.laplacian_comp_centered_dilation
      (fun z ↦ profile (x + z)) r (0 : ℝ^n) y
  have htranslation :=
    PDE.laplacian_comp_add_left profile x (r • y) hprofile.contDiffAt
  have hspace :
      laplacian
          (fun z ↦
            u (timeSpaceCons (t - r ^ 2 * τ) (x + r • z))) y =
        r ^ 2 *
          laplacian profile (x + r • y) := by
    calc
      laplacian
            (fun z ↦
              u (timeSpaceCons (t - r ^ 2 * τ) (x + r • z))) y =
          r ^ 2 *
            laplacian (fun z ↦ profile (x + z)) (r • y) := by
        simpa [profile, PDE.Representations.Similarity.centeredDilation] using
          hdilation
      _ = r ^ 2 * laplacian profile (x + r • y) := by
        rw [htranslation]
  rw [htime.deriv, hspace]
  unfold heatOperator
  simp only [p, profile, timeSpaceCons_zero,
    spatialPartCLM_eq_spatialPart, spatialPart_timeSpaceCons]
  ring

end HeatEquation
