/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.ReducedNavierStokes
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Axis-regular cylindrical diffusion

The reduced axisymmetric Navier–Stokes equations with swirl (see `ReducedNavierStokes`) carry
the viscous operator

`∂ᵣᵣ f + (3 / r) ∂ᵣ f + ∂_zz f`

acting on the nonsingular unknowns `u_θ / r`, `ω_θ / r`, `ψ / r²`. The coefficient `3 / r` is
singular on the symmetry axis, but for a radially even profile the quotient `∂ᵣ f / r` has a
removable singularity, and the operator extends continuously to the axis with value
`4 ∂ᵣᵣ f + ∂_zz f`. That extension is `axisExtendedRadialFourAxialLaplacian`.

Squared-radius pullbacks form a concrete class of profiles on which the extension is a smooth
expression. A profile `Φ(s, z)` in squared-radius coordinates pulls back to meridian coordinates
`(r, z)` by `s = r ^ 2` (`squaredRadiusPullback`), and every such pullback is automatically even
in `r`. Differentiating through the change of variables gives `∂ᵣ (Φ ∘ sq) = 2r Φ_s`, so the
division by `r` cancels algebraically and the whole operator becomes

`8 Φ_s + 4 r² Φ_ss + Φ_zz`, evaluated at `(r², z)`,

which is `squaredRadiusDiffusionPullback`. The radial-four-plus-axial Laplacian is the radial
part of the Laplacian in four space dimensions plus the axial second derivative, which is why
the axis value carries the factor `4`.

## Main results

* `contDiff_squaredRadiusPullback`: pulling back along `s = r ^ 2` preserves `C^n` for every
  `n ≤ ∞`.
* `partialDeriv_zero_squaredRadiusPullback`, `partialDeriv_zero_zero_squaredRadiusPullback`,
  `partialDeriv_one_one_squaredRadiusPullback`: the chain rule for the first and second radial
  and axial derivatives of a pullback.
* `contDiff_squaredRadiusDiffusionPullback`: the regularised formula is smooth when `Φ` is.
* `axisExtendedRadialFourAxialLaplacian_squaredRadiusPullback`: for `C²` profiles the
  axis-extended operator agrees with the regularised formula at every point of the meridian
  plane, including `r = 0`.

## Implementation notes

We use the squared-radius coordinate throughout the axisymmetric development, so that radial
evenness is automatic.

## References

* T. Y. Hou and C. Li, "Dynamic stability of the three-dimensional axisymmetric Navier-Stokes
  equations with swirl", Comm. Pure Appl. Math. 61 (2008), no. 5, 661-697, for the reduced variables
  and their diffusion operator.
  <https://doi.org/10.1002/cpa.20212>
-/

@[expose] public section

namespace AxisymmetricFlow

open EuclideanSpace

noncomputable section

/-- The coordinate map `(r, z) -> (r ^ 2, z)`. -/
def squaredRadiusMap (x : ℝ^2) : ℝ^2 :=
  EuclideanSpace.single 0 (x 0 ^ 2) + EuclideanSpace.single 1 (x 1)

/-- The radial coordinate of `squaredRadiusMap x` is `r ^ 2`. -/
@[simp]
theorem squaredRadiusMap_apply_zero (x : ℝ^2) :
    squaredRadiusMap x 0 = x 0 ^ 2 := by
  simp [squaredRadiusMap]

/-- The axial coordinate is unchanged by `squaredRadiusMap`. -/
@[simp]
theorem squaredRadiusMap_apply_one (x : ℝ^2) :
    squaredRadiusMap x 1 = x 1 := by
  simp [squaredRadiusMap]

/-- The squared-radius coordinate map is smooth. -/
theorem contDiff_squaredRadiusMap :
    ContDiff ℝ (⊤ : ℕ∞) squaredRadiusMap := by
  have hcoord (j : Fin 2) :
      ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^2 ↦ x j) :=
    (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) j).contDiff
  apply (contDiff_piLp (2 : ENNReal)).2
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [squaredRadiusMap_apply_zero] using (hcoord 0).pow 2
  · have hi' : i = 1 := Fin.eq_one_of_ne_zero i hi
    subst i
    simpa only [squaredRadiusMap_apply_one] using hcoord 1

/-- Pull a profile in `(s, z)` coordinates back by `s = r ^ 2`. -/
def squaredRadiusPullback (Φ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  Φ (squaredRadiusMap x)

/-- Squared-radius pullback preserves every finite or infinite degree of
smoothness. -/
theorem contDiff_squaredRadiusPullback {n : ℕ∞} {Φ : ℝ^2 → ℝ}
    (hΦ : ContDiff ℝ n Φ) :
    ContDiff ℝ n (squaredRadiusPullback Φ) := by
  exact hΦ.comp (contDiff_squaredRadiusMap.of_le (by simp))

private theorem partialDeriv_zero_coord_sq (x : ℝ^2) :
    (∂[0] (fun y : ℝ^2 ↦ y 0 ^ 2)) x = 2 * x 0 := by
  cas

private theorem partialDeriv_one_coord_sq (x : ℝ^2) :
    (∂[1] (fun y : ℝ^2 ↦ y 0 ^ 2)) x = 0 := by
  cas

private theorem partialDeriv_zero_two_mul_coord (x : ℝ^2) :
    (∂[0] (fun y : ℝ^2 ↦ 2 * y 0)) x = 2 := by
  cas

/-- First radial derivative of a squared-radius pullback. -/
theorem partialDeriv_zero_squaredRadiusPullback {Φ : ℝ^2 → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (x : ℝ^2) :
    (∂[0] (squaredRadiusPullback Φ)) x =
      2 * x 0 * (∂[0] Φ) (squaredRadiusMap x) := by
  calc
    _ = ∑ j : Fin 2,
        (∂[j] Φ) (squaredRadiusMap x) *
          (∂[0]
            (fun y : ℝ^2 ↦ squaredRadiusMap y j)) x :=
      PDE.partialDeriv_comp 0 Φ squaredRadiusMap x
        (hΦ.differentiable one_ne_zero).differentiableAt
        (contDiff_squaredRadiusMap.differentiable (by simp)).differentiableAt
    _ = _ := by
      simp only [Fin.sum_univ_two, squaredRadiusMap_apply_zero,
        squaredRadiusMap_apply_one]
      rw [partialDeriv_zero_coord_sq]
      simp [PDE.partialDeriv_coord]
      ring

/-- First axial derivative of a squared-radius pullback. -/
theorem partialDeriv_one_squaredRadiusPullback {Φ : ℝ^2 → ℝ}
    (hΦ : ContDiff ℝ 1 Φ) (x : ℝ^2) :
    (∂[1] (squaredRadiusPullback Φ)) x =
      (∂[1] Φ) (squaredRadiusMap x) := by
  calc
    _ = ∑ j : Fin 2,
        (∂[j] Φ) (squaredRadiusMap x) *
          (∂[1]
            (fun y : ℝ^2 ↦ squaredRadiusMap y j)) x :=
      PDE.partialDeriv_comp 1 Φ squaredRadiusMap x
        (hΦ.differentiable one_ne_zero).differentiableAt
        (contDiff_squaredRadiusMap.differentiable (by simp)).differentiableAt
    _ = _ := by
      simp only [Fin.sum_univ_two, squaredRadiusMap_apply_zero,
        squaredRadiusMap_apply_one]
      rw [partialDeriv_one_coord_sq]
      simp [PDE.partialDeriv_coord]

/-- Second radial derivative of a squared-radius pullback. -/
theorem partialDeriv_zero_zero_squaredRadiusPullback {Φ : ℝ^2 → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (x : ℝ^2) :
    (∂[0]
        (fun y ↦ (∂[0] (squaredRadiusPullback Φ)) y)) x =
      2 * (∂[0] Φ) (squaredRadiusMap x) +
        4 * x 0 ^ 2 *
          (∂[0]
            (fun y ↦ (∂[0] Φ) y))
            (squaredRadiusMap x) := by
  have hΦone : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hΦr : ContDiff ℝ 1 (fun y ↦ (∂[0] Φ) y) :=
    PDE.contDiff_partialDeriv_of_succ hΦ
  have hfirst :
      (fun y ↦ (∂[0] (squaredRadiusPullback Φ)) y) =
        fun y ↦ 2 * y 0 * (∂[0] Φ) (squaredRadiusMap y) := by
    funext y
    exact partialDeriv_zero_squaredRadiusPullback hΦone y
  rw [hfirst]
  rw [PDE.partialDeriv_mul]
  · change
      (∂[0] (fun y : ℝ^2 ↦ 2 * y 0)) x *
          (∂[0] Φ) (squaredRadiusMap x) +
        2 * x 0 *
          (∂[0]
            (squaredRadiusPullback
              (fun y ↦ (∂[0] Φ) y))) x = _
    rw [partialDeriv_zero_squaredRadiusPullback hΦr]
    rw [partialDeriv_zero_two_mul_coord]
    ring
  · fun_prop
  · exact ((contDiff_squaredRadiusPullback hΦr).differentiable
      one_ne_zero).differentiableAt

/-- Second axial derivative of a squared-radius pullback. -/
theorem partialDeriv_one_one_squaredRadiusPullback {Φ : ℝ^2 → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (x : ℝ^2) :
    (∂[1]
        (fun y ↦ (∂[1] (squaredRadiusPullback Φ)) y)) x =
      (∂[1]
        (fun y ↦ (∂[1] Φ) y))
        (squaredRadiusMap x) := by
  have hΦone : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num)
  have hΦz : ContDiff ℝ 1 (fun y ↦ (∂[1] Φ) y) :=
    PDE.contDiff_partialDeriv_of_succ hΦ
  have hfirst :
      (fun y ↦ (∂[1] (squaredRadiusPullback Φ)) y) =
        squaredRadiusPullback (fun y ↦ (∂[1] Φ) y) := by
    funext y
    exact partialDeriv_one_squaredRadiusPullback hΦone y
  rw [hfirst]
  exact partialDeriv_one_squaredRadiusPullback hΦz x

/-- Smooth formula obtained after removing the apparent singularity in the
radial-four-plus-axial Laplacian of a squared-radius pullback. -/
def squaredRadiusDiffusionPullback (Φ : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  8 * (∂[0] Φ) (squaredRadiusMap x) +
    4 * x 0 ^ 2 *
      (∂[0] (fun y ↦ (∂[0] Φ) y))
        (squaredRadiusMap x) +
    (∂[1] (fun y ↦ (∂[1] Φ) y))
      (squaredRadiusMap x)

/-- The explicit regularized diffusion formula is smooth when the profile is
smooth. -/
theorem contDiff_squaredRadiusDiffusionPullback {Φ : ℝ^2 → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (squaredRadiusDiffusionPullback Φ) := by
  have hΦr : ContDiff ℝ (⊤ : ℕ∞)
      (fun y ↦ (∂[0] Φ) y) :=
    PDE.contDiff_top_partialDeriv hΦ
  have hΦrr : ContDiff ℝ (⊤ : ℕ∞)
      (fun y ↦ (∂[0]
        (fun z ↦ (∂[0] Φ) z)) y) :=
    PDE.contDiff_top_partialDeriv hΦr
  have hΦz : ContDiff ℝ (⊤ : ℕ∞)
      (fun y ↦ (∂[1] Φ) y) :=
    PDE.contDiff_top_partialDeriv hΦ
  have hΦzz : ContDiff ℝ (⊤ : ℕ∞)
      (fun y ↦ (∂[1]
        (fun z ↦ (∂[1] Φ) z)) y) :=
    PDE.contDiff_top_partialDeriv hΦz
  have hr : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ^2 ↦ x 0) :=
    (PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ) 0).contDiff
  have hfirst : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ 8 * squaredRadiusPullback
        (fun y ↦ (∂[0] Φ) y) x) :=
    contDiff_const.mul (contDiff_squaredRadiusPullback hΦr)
  have hsecond : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ 4 * x 0 ^ 2 * squaredRadiusPullback
        (fun y ↦ (∂[0]
          (fun z ↦ (∂[0] Φ) z)) y) x) :=
    (contDiff_const.mul (hr.pow 2)).mul
      (contDiff_squaredRadiusPullback hΦrr)
  change ContDiff ℝ (⊤ : ℕ∞) (fun x ↦
    8 * squaredRadiusPullback
        (fun y ↦ (∂[0] Φ) y) x +
      4 * x 0 ^ 2 * squaredRadiusPullback
        (fun y ↦ (∂[0]
          (fun z ↦ (∂[0] Φ) z)) y) x +
      squaredRadiusPullback
        (fun y ↦ (∂[1]
          (fun z ↦ (∂[1] Φ) z)) y) x)
  exact (hfirst.add hsecond).add (contDiff_squaredRadiusPullback hΦzz)

/-- The axis-value-extended radial-four-plus-axial Laplacian equals its
smooth squared-radius formula at every point, including `r = 0`. -/
theorem axisExtendedRadialFourAxialLaplacian_squaredRadiusPullback
    {Φ : ℝ^2 → ℝ} (hΦ : ContDiff ℝ 2 Φ) (x : ℝ^2) :
    axisExtendedRadialFourAxialLaplacian (squaredRadiusPullback Φ) x =
      squaredRadiusDiffusionPullback Φ x := by
  by_cases hr : x 0 = 0
  · rw [axisExtendedRadialFourAxialLaplacian_of_eq_zero _ _ hr]
    rw [partialDeriv_zero_zero_squaredRadiusPullback hΦ x]
    rw [partialDeriv_one_one_squaredRadiusPullback hΦ x]
    simp [squaredRadiusDiffusionPullback, hr]
    ring
  · rw [axisExtendedRadialFourAxialLaplacian_of_ne _ _ hr]
    unfold radialFourAxialLaplacian
    rw [partialDeriv_zero_zero_squaredRadiusPullback hΦ x]
    rw [partialDeriv_one_one_squaredRadiusPullback hΦ x]
    rw [partialDeriv_zero_squaredRadiusPullback (hΦ.of_le (by norm_num))]
    unfold squaredRadiusDiffusionPullback
    field_simp [hr]
    ring

end

end AxisymmetricFlow
