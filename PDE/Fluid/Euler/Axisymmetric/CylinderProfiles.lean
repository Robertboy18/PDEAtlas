/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Euler.Axisymmetric.CylinderMeridian
public import PDE.Fluid.Axisymmetric.CartesianDiffusion
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# The meridian system in squared-radius profiles

An axis-regular axisymmetric flow is described by profiles `U`, `Ω`, `Ψ` of `(t, s, z)` with
`s = r²`: the swirl `u^θ = r U`, the azimuthal vorticity `ω^θ = r Ω` and the angular stream
function `φ̃ = r Ψ` (`ofProfiles`). These are the nonsingular variables of
`PDE.Fluid.Axisymmetric`; a smooth profile in `s` gives fields that are smooth up to the axis.
Then `u^r = -r Ψ_z`, `u^z = 2Ψ + 2s Ψ_s`, and on the strip `0 < r < 1` the equations (6.2)-(6.3)
of the meridian system are the reduced Euler equations in `(t, s, z)`:

```text
(6.2), first equation:   residual = r² (D_t U - 2 U Ψ_z),
(6.2), second equation:  residual = D_t Ω - 2 U U_z,
(6.3):                   residual = r (-(8 Ψ_s + 4 s Ψ_ss + Ψ_zz) - Ω),
```

with `D_t = ∂_t - 2s Ψ_z ∂_s + (2Ψ + 2s Ψ_s) ∂_z` (`squaredRadiusMaterialDerivative`), and the
wall condition (6.4) is `Ψ(t, 1, z) = 0`.

## Main definitions

* `profilePoint`: the point `(t, s, z)` of profile space.
* `meridianProfilePoint`: `(t, r², z)` for the meridian point `(r, z)`.
* `ofProfiles`: the meridian fields `(r U, r Ω, r Ψ)`.

## Main results

* `radialVelocity_ofProfiles`, `axialVelocity_ofProfiles`: the meridian velocity.
* `swirlResidual_ofProfiles`, `vorticityResidual_ofProfiles`, `streamResidual_ofProfiles`:
  the three residual identities under local regularity of the profiles.
* `satisfiesMeridianSystemOn_ofProfiles_iff`: the meridian system on a set of times is
  equivalent to the reduced Euler equations on `0 < s < 1` and `Ψ(t, 1, z) = 0`.
* `hasMeridianRegularityOn_ofProfiles`, `hasReflectionSymmetry_ofProfiles`,
  `isAxiallyPeriodic_ofProfiles`: regularity, the reflection class and periodicity from the
  corresponding properties of the profiles.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 6, (6.2)-(6.4).
  <https://arxiv.org/abs/2210.07191v4>
* T. Y. Hou and C. Li, "Dynamic stability of the three-dimensional axisymmetric Navier-Stokes
  equations with swirl", Comm. Pure Appl. Math. 61 (2008), no. 5, 661-697, for the reduced
  variables.
  <https://doi.org/10.1002/cpa.20212>
-/

@[expose] public section

open PDE (laplacian advectiveDerivative partialDeriv)

namespace Euler.Cylinder

open EuclideanSpace Filter
open PDE.Common AxisymmetricFlow
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-- The point `(t, s, z)` of profile space. -/
def profilePoint (t s z : ℝ) : ℝ^3 :=
  WithLp.toLp 2 ![t, s, z]

/-- The time coordinate of `profilePoint t s z`. -/
@[simp]
theorem profilePoint_apply_zero (t s z : ℝ) : profilePoint t s z 0 = t := by
  simp [profilePoint]

/-- The squared-radius coordinate of `profilePoint t s z`. -/
@[simp]
theorem profilePoint_apply_one (t s z : ℝ) : profilePoint t s z 1 = s := by
  simp [profilePoint]

/-- The axial coordinate of `profilePoint t s z`. -/
@[simp]
theorem profilePoint_apply_two (t s z : ℝ) : profilePoint t s z 2 = z := by
  simp [profilePoint]

/-- `profilePoint` as a combination of the coordinate vectors. -/
theorem profilePoint_eq (t s z : ℝ) :
    profilePoint t s z =
      t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) + s • EuclideanSpace.single (1 : Fin 3) 1 +
        z • EuclideanSpace.single (2 : Fin 3) 1 := by
  ext i
  fin_cases i <;> simp [profilePoint]

/-- The profile point `(t, r², z)` of the meridian point `x = (r, z)` at time `t`. -/
def meridianProfilePoint (t : ℝ) (x : ℝ^2) : ℝ^3 :=
  profilePoint t (x 0 ^ 2) (x 1)

/-- The derivative of `x ↦ (t, r², z)`: `v ↦ (0, 2 r v₀, v₁)`. -/
def meridianProfileDeriv (x : ℝ^2) : ℝ^2 →L[ℝ] ℝ^3 :=
  ((2 * x 0) • (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ)).smulRight
      (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) +
    (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single (2 : Fin 3) (1 : ℝ))

/-- The derivative of the meridian profile chart. -/
theorem hasFDerivAt_meridianProfilePoint (t : ℝ) (x : ℝ^2) :
    HasFDerivAt (meridianProfilePoint t) (meridianProfileDeriv x) x := by
  have h0 := (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have h1 := (EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hfun : meridianProfilePoint t = fun y : ℝ^2 ↦
      t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        (y 0) ^ 2 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
        y 1 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    funext y
    exact profilePoint_eq _ _ _
  have h := ((hasFDerivAt_const (t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) x).add
    ((h0.pow 2).smul_const (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)))).add
    (h1.smul_const (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)))
  rw [hfun]
  refine h.congr_fderiv ?_
  ext v i
  fin_cases i <;> simp [meridianProfileDeriv]

/-- The meridian profile chart is smooth. -/
theorem contDiff_meridianProfilePoint {n : WithTop ℕ∞} (t : ℝ) :
    ContDiff ℝ n (meridianProfilePoint t) := by
  have hfun : meridianProfilePoint t = fun y : ℝ^2 ↦
      t • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        (y 0) ^ 2 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
        y 1 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    funext y
    exact profilePoint_eq _ _ _
  rw [hfun]
  exact (contDiff_const.add ((((EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff.pow
    2).smul contDiff_const))).add
    ((EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff.smul contDiff_const)

/-- The space-time profile chart `(x, t) ↦ (t, r², z)` is smooth. -/
theorem contDiff_meridianProfilePoint_uncurry {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : ℝ^2 × ℝ ↦ meridianProfilePoint p.2 p.1) := by
  have hfun : (fun p : ℝ^2 × ℝ ↦ meridianProfilePoint p.2 p.1) = fun p ↦
      p.2 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        (p.1 0) ^ 2 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) +
        p.1 1 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    funext p
    exact profilePoint_eq _ _ _
  have hx0 : ContDiff ℝ n (fun p : ℝ^2 × ℝ ↦ p.1 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ^2) ℝ)).contDiff
  have hx1 : ContDiff ℝ n (fun p : ℝ^2 × ℝ ↦ p.1 1) :=
    ((EuclideanSpace.proj (1 : Fin 2) : ℝ^2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ^2) ℝ)).contDiff
  rw [hfun]
  exact ((contDiff_snd.smul contDiff_const).add ((hx0.pow 2).smul contDiff_const)).add
    (hx1.smul contDiff_const)

/-- `∂_r F(t, r², z) = 2 r F_s`. -/
theorem partialDeriv_zero_comp_meridianProfilePoint {F : ℝ^3 → ℝ} {t : ℝ} {x : ℝ^2}
    (hF : DifferentiableAt ℝ F (meridianProfilePoint t x)) :
    (∂[(0 : Fin 2)] (fun y ↦ F (meridianProfilePoint t y))) x =
      2 * x 0 * (∂[(1 : Fin 3)] F) (meridianProfilePoint t x) := by
  change fderiv ℝ (F ∘ meridianProfilePoint t) x _ = _
  rw [fderiv_comp x hF (hasFDerivAt_meridianProfilePoint t x).differentiableAt,
    (hasFDerivAt_meridianProfilePoint t x).fderiv]
  have : meridianProfileDeriv x (EuclideanSpace.single (0 : Fin 2) 1) =
      (2 * x 0) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [meridianProfileDeriv]
  simp only [ContinuousLinearMap.comp_apply, this, map_smul, smul_eq_mul, partialDeriv]

/-- `∂_z F(t, r², z) = F_z`. -/
theorem partialDeriv_one_comp_meridianProfilePoint {F : ℝ^3 → ℝ} {t : ℝ} {x : ℝ^2}
    (hF : DifferentiableAt ℝ F (meridianProfilePoint t x)) :
    (∂[(1 : Fin 2)] (fun y ↦ F (meridianProfilePoint t y))) x =
      (∂[(2 : Fin 3)] F) (meridianProfilePoint t x) := by
  change fderiv ℝ (F ∘ meridianProfilePoint t) x _ = _
  rw [fderiv_comp x hF (hasFDerivAt_meridianProfilePoint t x).differentiableAt,
    (hasFDerivAt_meridianProfilePoint t x).fderiv]
  have : meridianProfileDeriv x (EuclideanSpace.single (1 : Fin 2) 1) =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [meridianProfileDeriv]
  simp only [ContinuousLinearMap.comp_apply, this, partialDeriv]

/-- `profilePoint` is the space-time point with time `t` and space `(s, z)`. -/
theorem profilePoint_eq_timeSpaceCons (t s z : ℝ) :
    profilePoint t s z = timeSpaceCons t (WithLp.toLp 2 ![s, z]) := by
  ext i
  fin_cases i <;> simp [profilePoint, timeSpaceCons]

/-- `∂_t F(t, r², z) = F_t`. -/
theorem deriv_comp_meridianProfilePoint {F : ℝ^3 → ℝ} {t : ℝ} {x : ℝ^2}
    (hF : DifferentiableAt ℝ F (meridianProfilePoint t x)) :
    deriv (fun s ↦ F (meridianProfilePoint s x)) t =
      (∂[(0 : Fin 3)] F) (meridianProfilePoint t x) := by
  have hfun : (fun s ↦ F (meridianProfilePoint s x)) =
      fun s ↦ F (timeSpaceCons s (WithLp.toLp 2 ![x 0 ^ 2, x 1])) := by
    funext s
    rw [meridianProfilePoint, profilePoint_eq_timeSpaceCons]
  have hpoint : meridianProfilePoint t x = timeSpaceCons t (WithLp.toLp 2 ![x 0 ^ 2, x 1]) :=
    profilePoint_eq_timeSpaceCons _ _ _
  rw [hfun, hpoint]
  rw [hpoint] at hF
  exact (PDE.hasDerivAt_timeSpaceCons F t _ hF).deriv

/-- `∂_r (r F(t, r², z)) = F + 2 r² F_s`. -/
theorem partialDeriv_zero_mul_comp_meridianProfilePoint {F : ℝ^3 → ℝ} {t : ℝ} {x : ℝ^2}
    (hF : DifferentiableAt ℝ F (meridianProfilePoint t x)) :
    (∂[(0 : Fin 2)] (fun y ↦ y 0 * F (meridianProfilePoint t y))) x =
      F (meridianProfilePoint t x) +
        2 * x 0 ^ 2 * (∂[(1 : Fin 3)] F) (meridianProfilePoint t x) := by
  have h0 : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have hc : DifferentiableAt ℝ (fun y ↦ F (meridianProfilePoint t y)) x :=
    hF.comp x (hasFDerivAt_meridianProfilePoint t x).differentiableAt
  rw [PDE.partialDeriv_mul h0 hc, partialDeriv_zero_comp_meridianProfilePoint hF,
    PDE.partialDeriv_coord]
  simp
  ring

/-- `∂_z (r F(t, r², z)) = r F_z`. -/
theorem partialDeriv_one_mul_comp_meridianProfilePoint {F : ℝ^3 → ℝ} {t : ℝ} {x : ℝ^2}
    (hF : DifferentiableAt ℝ F (meridianProfilePoint t x)) :
    (∂[(1 : Fin 2)] (fun y ↦ y 0 * F (meridianProfilePoint t y))) x =
      x 0 * (∂[(2 : Fin 3)] F) (meridianProfilePoint t x) := by
  have h0 : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have hc : DifferentiableAt ℝ (fun y ↦ F (meridianProfilePoint t y)) x :=
    hF.comp x (hasFDerivAt_meridianProfilePoint t x).differentiableAt
  rw [PDE.partialDeriv_mul h0 hc, partialDeriv_one_comp_meridianProfilePoint hF,
    PDE.partialDeriv_coord]
  simp

/-- `∂_r (r² F(t, r², z)) = 2 r F + 2 r³ F_s`. -/
theorem partialDeriv_zero_sq_mul_comp_meridianProfilePoint {F : ℝ^3 → ℝ} {t : ℝ} {x : ℝ^2}
    (hF : DifferentiableAt ℝ F (meridianProfilePoint t x)) :
    (∂[(0 : Fin 2)] (fun y ↦ y 0 ^ 2 * F (meridianProfilePoint t y))) x =
      2 * x 0 * F (meridianProfilePoint t x) +
        2 * x 0 ^ 3 * (∂[(1 : Fin 3)] F) (meridianProfilePoint t x) := by
  have h0 : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have hc : DifferentiableAt ℝ (fun y ↦ F (meridianProfilePoint t y)) x :=
    hF.comp x (hasFDerivAt_meridianProfilePoint t x).differentiableAt
  have h02 : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0 ^ 2) x := h0.pow 2
  rw [PDE.partialDeriv_mul h02 hc, PDE.partialDeriv_sq _ h0,
    partialDeriv_zero_comp_meridianProfilePoint hF, PDE.partialDeriv_coord]
  simp
  ring

/-- `∂_z (r² F(t, r², z)) = r² F_z`. -/
theorem partialDeriv_one_sq_mul_comp_meridianProfilePoint {F : ℝ^3 → ℝ} {t : ℝ} {x : ℝ^2}
    (hF : DifferentiableAt ℝ F (meridianProfilePoint t x)) :
    (∂[(1 : Fin 2)] (fun y ↦ y 0 ^ 2 * F (meridianProfilePoint t y))) x =
      x 0 ^ 2 * (∂[(2 : Fin 3)] F) (meridianProfilePoint t x) := by
  have h0 : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have hc : DifferentiableAt ℝ (fun y ↦ F (meridianProfilePoint t y)) x :=
    hF.comp x (hasFDerivAt_meridianProfilePoint t x).differentiableAt
  have h02 : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0 ^ 2) x := h0.pow 2
  rw [PDE.partialDeriv_mul h02 hc, PDE.partialDeriv_sq _ h0,
    partialDeriv_one_comp_meridianProfilePoint hF, PDE.partialDeriv_coord]
  simp

/-- The Laplacian of `r F(t, r², z)` in the meridian plane is
`6 r F_s + 4 r³ F_ss + r F_zz`, for `F` that is `C²` at the profile point. -/
theorem laplacian_mul_comp_meridianProfilePoint {F : ℝ^3 → ℝ} {t : ℝ} {x : ℝ^2}
    (hF : ContDiffAt ℝ 2 F (meridianProfilePoint t x)) :
    laplacian (fun y ↦ y 0 * F (meridianProfilePoint t y)) x =
      6 * x 0 * (∂[(1 : Fin 3)] F) (meridianProfilePoint t x) +
        4 * x 0 ^ 3 * (∂[(1 : Fin 3)] (∂[(1 : Fin 3)] F)) (meridianProfilePoint t x) +
        x 0 * (∂[(2 : Fin 3)] (∂[(2 : Fin 3)] F)) (meridianProfilePoint t x) := by
  have hnear : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ F (meridianProfilePoint t y) :=
    ((contDiff_meridianProfilePoint (n := 0) t).continuous.continuousAt.eventually
      (hF.eventually (by norm_num))).mono fun y hy ↦ hy.differentiableAt (by norm_num)
  have h0 : (fun y ↦ (∂[(0 : Fin 2)] (fun u ↦ u 0 * F (meridianProfilePoint t u))) y) =ᶠ[𝓝 x]
      fun y ↦ F (meridianProfilePoint t y) +
        2 * (y 0 ^ 2 * (∂[(1 : Fin 3)] F) (meridianProfilePoint t y)) :=
    hnear.mono fun y hy ↦ by
      dsimp only
      rw [partialDeriv_zero_mul_comp_meridianProfilePoint hy]
      ring
  have h1 : (fun y ↦ (∂[(1 : Fin 2)] (fun u ↦ u 0 * F (meridianProfilePoint t u))) y) =ᶠ[𝓝 x]
      fun y ↦ y 0 * (∂[(2 : Fin 3)] F) (meridianProfilePoint t y) :=
    hnear.mono fun y hy ↦ partialDeriv_one_mul_comp_meridianProfilePoint hy
  have hd := hF.differentiableAt (by norm_num)
  have hd1 : DifferentiableAt ℝ (∂[(1 : Fin 3)] F) (meridianProfilePoint t x) :=
    (PDE.contDiffAt_partialDeriv 1 hF 1).differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (∂[(2 : Fin 3)] F) (meridianProfilePoint t x) :=
    (PDE.contDiffAt_partialDeriv 1 hF 2).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun y ↦ F (meridianProfilePoint t y)) x :=
    hd.comp x (hasFDerivAt_meridianProfilePoint t x).differentiableAt
  have h0' : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have hc1 : DifferentiableAt ℝ
      (fun y ↦ y 0 ^ 2 * (∂[(1 : Fin 3)] F) (meridianProfilePoint t y)) x :=
    (h0'.pow 2).mul (hd1.comp x (hasFDerivAt_meridianProfilePoint t x).differentiableAt)
  unfold laplacian
  rw [Fin.sum_univ_two, PDE.partialDeriv_congr_nhds 0 h0, PDE.partialDeriv_congr_nhds 1 h1,
    PDE.partialDeriv_add hc (hc1.const_mul 2), partialDeriv_zero_comp_meridianProfilePoint hd,
    show (fun y ↦ 2 * (y 0 ^ 2 * (∂[(1 : Fin 3)] F) (meridianProfilePoint t y))) =
      fun y ↦ (2 : ℝ) • (y 0 ^ 2 * (∂[(1 : Fin 3)] F) (meridianProfilePoint t y)) from rfl,
    PDE.partialDeriv_const_smul, partialDeriv_zero_sq_mul_comp_meridianProfilePoint hd1,
    partialDeriv_one_mul_comp_meridianProfilePoint hd2]
  simp only [smul_eq_mul]
  ring

/-- The meridian fields `u^θ = r U`, `ω^θ = r Ω`, `φ̃ = r Ψ` of profiles `U`, `Ω`, `Ψ` of
`(t, s, z)`, `s = r²`. -/
def ofProfiles (U Ω Ψ : ℝ^3 → ℝ) : MeridianFields where
  swirl := fun x t ↦ x 0 * U (meridianProfilePoint t x)
  vorticity := fun x t ↦ x 0 * Ω (meridianProfilePoint t x)
  streamFunction := fun x t ↦ x 0 * Ψ (meridianProfilePoint t x)

/-- The radial velocity of profile fields is `u^r = -r Ψ_z`. -/
theorem radialVelocity_ofProfiles {U Ω Ψ : ℝ^3 → ℝ} {x : ℝ^2} {t : ℝ}
    (hΨ : DifferentiableAt ℝ Ψ (meridianProfilePoint t x)) :
    radialVelocity (ofProfiles U Ω Ψ) x t =
      -x 0 * (∂[(2 : Fin 3)] Ψ) (meridianProfilePoint t x) := by
  simp only [radialVelocity, ofProfiles]
  rw [partialDeriv_one_mul_comp_meridianProfilePoint hΨ]
  ring

/-- Off the axis the axial velocity of profile fields is `u^z = 2Ψ + 2s Ψ_s`. -/
theorem axialVelocity_ofProfiles {U Ω Ψ : ℝ^3 → ℝ} {x : ℝ^2} {t : ℝ} (hx : x 0 ≠ 0)
    (hΨ : DifferentiableAt ℝ Ψ (meridianProfilePoint t x)) :
    axialVelocity (ofProfiles U Ω Ψ) x t =
      2 * Ψ (meridianProfilePoint t x) +
        2 * x 0 ^ 2 * (∂[(1 : Fin 3)] Ψ) (meridianProfilePoint t x) := by
  simp only [axialVelocity, ofProfiles]
  rw [partialDeriv_zero_mul_comp_meridianProfilePoint hΨ]
  field_simp
  ring

/-- The squared radius of the profile point of `x` is `x₀²`. -/
@[simp]
theorem meridianProfilePoint_apply_one (t : ℝ) (x : ℝ^2) :
    meridianProfilePoint t x 1 = x 0 ^ 2 := by
  simp [meridianProfilePoint]

/-- The circulation of profile fields is `r² U`. -/
theorem circulation_ofProfiles (U Ω Ψ : ℝ^3 → ℝ) (x : ℝ^2) (t : ℝ) :
    circulation (ofProfiles U Ω Ψ) x t = x 0 ^ 2 * U (meridianProfilePoint t x) := by
  simp only [circulation, ofProfiles]
  ring

/-- `∂_t F(t, r², z)` as a derivative statement. -/
theorem hasDerivAt_comp_meridianProfilePoint {F : ℝ^3 → ℝ} {t : ℝ} {x : ℝ^2}
    (hF : DifferentiableAt ℝ F (meridianProfilePoint t x)) :
    HasDerivAt (fun s ↦ F (meridianProfilePoint s x))
      ((∂[(0 : Fin 3)] F) (meridianProfilePoint t x)) t := by
  have hfun : (fun s ↦ F (meridianProfilePoint s x)) =
      fun s ↦ F (timeSpaceCons s (WithLp.toLp 2 ![x 0 ^ 2, x 1])) := by
    funext s
    rw [meridianProfilePoint, profilePoint_eq_timeSpaceCons]
  have hpoint : meridianProfilePoint t x = timeSpaceCons t (WithLp.toLp 2 ![x 0 ^ 2, x 1]) :=
    profilePoint_eq_timeSpaceCons _ _ _
  rw [hfun, hpoint]
  rw [hpoint] at hF
  exact PDE.hasDerivAt_timeSpaceCons F t _ hF

/-- The circulation equation (the first equation of (6.2)) for profile fields: its left side is
`r²` times the reduced swirl residual `D_t U - 2 U Ψ_z` (on the axis both sides vanish). -/
theorem swirlResidual_ofProfiles {U Ω Ψ : ℝ^3 → ℝ} {x : ℝ^2} {t : ℝ}
    (hU : DifferentiableAt ℝ U (meridianProfilePoint t x))
    (hΨ : DifferentiableAt ℝ Ψ (meridianProfilePoint t x)) :
    deriv (fun s ↦ circulation (ofProfiles U Ω Ψ) x s) t +
        advectiveDerivative (fun y ↦ meridianVelocity (ofProfiles U Ω Ψ) y t)
          (fun y ↦ circulation (ofProfiles U Ω Ψ) y t) x =
      x 0 ^ 2 * squaredRadiusEulerSwirlResidual U Ψ (meridianProfilePoint t x) := by
  have htime : (fun s ↦ circulation (ofProfiles U Ω Ψ) x s) =
      fun s ↦ x 0 ^ 2 * U (meridianProfilePoint s x) := by
    funext s
    exact circulation_ofProfiles U Ω Ψ x s
  have hspace : (fun y ↦ circulation (ofProfiles U Ω Ψ) y t) =
      fun y ↦ y 0 ^ 2 * U (meridianProfilePoint t y) := by
    funext y
    exact circulation_ofProfiles U Ω Ψ y t
  rw [htime, hspace, ((hasDerivAt_comp_meridianProfilePoint hU).const_mul (x 0 ^ 2)).deriv,
    PDE.advectiveDerivative_eq_sum_mul_partialDeriv, Fin.sum_univ_two, meridianVelocity_apply_zero,
    meridianVelocity_apply_one, radialVelocity_ofProfiles hΨ,
    partialDeriv_zero_sq_mul_comp_meridianProfilePoint hU,
    partialDeriv_one_sq_mul_comp_meridianProfilePoint hU]
  by_cases hx : x 0 = 0
  · simp [hx]
  rw [axialVelocity_ofProfiles hx hΨ]
  simp only [squaredRadiusEulerSwirlResidual, squaredRadiusMaterialDerivative,
    meridianProfilePoint_apply_one]
  ring

/-- Off the axis the reduced vorticity of profile fields is `Ω` near the point. -/
theorem reducedVorticity_ofProfiles_eventuallyEq {U Ω Ψ : ℝ^3 → ℝ} {x : ℝ^2} (t : ℝ)
    (hx : x 0 ≠ 0) :
    (fun y ↦ reducedVorticity (ofProfiles U Ω Ψ) y t) =ᶠ[𝓝 x]
      fun y ↦ Ω (meridianProfilePoint t y) := by
  have hopen : ∀ᶠ y in 𝓝 x, y 0 ≠ 0 :=
    ((EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).continuous.continuousAt).eventually_ne hx
  filter_upwards [hopen] with y hy
  simp only [reducedVorticity, ofProfiles]
  field_simp

/-- The reduced vorticity equation (the second equation of (6.2)) for profile fields: off the
axis its left side minus its right side is the reduced vorticity residual `D_t Ω - 2 U U_z`. -/
theorem vorticityResidual_ofProfiles {U Ω Ψ : ℝ^3 → ℝ} {x : ℝ^2} {t : ℝ} (hx : x 0 ≠ 0)
    (hU : DifferentiableAt ℝ U (meridianProfilePoint t x))
    (hΩ : DifferentiableAt ℝ Ω (meridianProfilePoint t x))
    (hΨ : DifferentiableAt ℝ Ψ (meridianProfilePoint t x)) :
    deriv (fun s ↦ reducedVorticity (ofProfiles U Ω Ψ) x s) t +
        advectiveDerivative (fun y ↦ meridianVelocity (ofProfiles U Ω Ψ) y t)
          (fun y ↦ reducedVorticity (ofProfiles U Ω Ψ) y t) x -
        (∂[(1 : Fin 2)] (fun y ↦ circulation (ofProfiles U Ω Ψ) y t ^ 2)) x / x 0 ^ 4 =
      squaredRadiusEulerVorticityResidual U Ω Ψ (meridianProfilePoint t x) := by
  have htime : (fun s ↦ reducedVorticity (ofProfiles U Ω Ψ) x s) =
      fun s ↦ Ω (meridianProfilePoint s x) := by
    funext s
    simp only [reducedVorticity, ofProfiles]
    field_simp
  have hspace := reducedVorticity_ofProfiles_eventuallyEq (U := U) (Ω := Ω) (Ψ := Ψ) t hx
  have hadv : advectiveDerivative (fun y ↦ meridianVelocity (ofProfiles U Ω Ψ) y t)
      (fun y ↦ reducedVorticity (ofProfiles U Ω Ψ) y t) x =
      advectiveDerivative (fun y ↦ meridianVelocity (ofProfiles U Ω Ψ) y t)
        (fun y ↦ Ω (meridianProfilePoint t y)) x := by
    simp only [advectiveDerivative, hspace.fderiv_eq]
  have hcirc : (fun y ↦ circulation (ofProfiles U Ω Ψ) y t ^ 2) =
      fun y ↦ (y 0 ^ 2 * U (meridianProfilePoint t y)) ^ 2 := by
    funext y
    rw [circulation_ofProfiles]
  have h0 : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have hcU : DifferentiableAt ℝ (fun y ↦ y 0 ^ 2 * U (meridianProfilePoint t y)) x :=
    (h0.pow 2).mul (hU.comp x (hasFDerivAt_meridianProfilePoint t x).differentiableAt)
  rw [htime, (hasDerivAt_comp_meridianProfilePoint hΩ).deriv, hadv,
    PDE.advectiveDerivative_eq_sum_mul_partialDeriv, Fin.sum_univ_two, meridianVelocity_apply_zero,
    meridianVelocity_apply_one, radialVelocity_ofProfiles hΨ, axialVelocity_ofProfiles hx hΨ,
    partialDeriv_zero_comp_meridianProfilePoint hΩ, partialDeriv_one_comp_meridianProfilePoint hΩ,
    hcirc, PDE.partialDeriv_sq _ hcU, partialDeriv_one_sq_mul_comp_meridianProfilePoint hU]
  simp only [squaredRadiusEulerVorticityResidual, squaredRadiusMaterialDerivative,
    meridianProfilePoint_apply_one]
  field_simp
  ring

/-- The stream function equation (6.3) for profile fields: off the axis its residual is `r`
times the reduced residual `-(8 Ψ_s + 4 s Ψ_ss + Ψ_zz) - Ω`. -/
theorem streamResidual_ofProfiles {U Ω Ψ : ℝ^3 → ℝ} {x : ℝ^2} {t : ℝ} (hx : x 0 ≠ 0)
    (hΨ : ContDiffAt ℝ 2 Ψ (meridianProfilePoint t x)) :
    streamOperator (fun y ↦ (ofProfiles U Ω Ψ).streamFunction y t) x -
        (ofProfiles U Ω Ψ).vorticity x t =
      x 0 * (-spacetimeSquaredRadiusDiffusion Ψ (meridianProfilePoint t x) -
        Ω (meridianProfilePoint t x)) := by
  simp only [streamOperator, ofProfiles]
  rw [laplacian_mul_comp_meridianProfilePoint hΨ,
    partialDeriv_zero_mul_comp_meridianProfilePoint (hΨ.differentiableAt (by norm_num))]
  simp only [spacetimeSquaredRadiusDiffusion, meridianProfilePoint_apply_one]
  field_simp
  ring

/-- The wall value of the angular stream function of profile fields is `Ψ(t, 1, z)`. -/
theorem streamFunction_ofProfiles_wall (U Ω Ψ : ℝ^3 → ℝ) (z t : ℝ) :
    (ofProfiles U Ω Ψ).streamFunction (meridianPoint 1 z) t = Ψ (profilePoint t 1 z) := by
  simp [ofProfiles, meridianProfilePoint]

/-- The strip `{(t, s, z) : t ∈ times, 0 < s < 1}` of profile space, the image of the open
meridian strip `0 < r < 1` under `s = r²`. -/
def profileStrip (times : Set ℝ) : Set (ℝ^3) :=
  {q | q 0 ∈ times ∧ 0 < q 1 ∧ q 1 < 1}

/-- The reduced Euler equations in `(t, s, z)` on the strip `0 < s < 1` with the wall condition
`Ψ(t, 1, z) = 0`. -/
structure SatisfiesProfileSystemOn (U Ω Ψ : ℝ^3 → ℝ) (times : Set ℝ) : Prop where
  /-- The reduced swirl equation `D_t U = 2 U Ψ_z`. -/
  swirl_equation : ∀ q ∈ profileStrip times, squaredRadiusEulerSwirlResidual U Ψ q = 0
  /-- The reduced vorticity equation `D_t Ω = 2 U U_z`. -/
  vorticity_equation :
    ∀ q ∈ profileStrip times, squaredRadiusEulerVorticityResidual U Ω Ψ q = 0
  /-- The reduced stream function equation `Ω = -(8 Ψ_s + 4 s Ψ_ss + Ψ_zz)`. -/
  streamFunction_equation :
    ∀ q ∈ profileStrip times, Ω q = -spacetimeSquaredRadiusDiffusion Ψ q
  /-- The wall condition. -/
  wall : ∀ ⦃t : ℝ⦄, t ∈ times → ∀ z, Ψ (profilePoint t 1 z) = 0

/-- Local regularity of the profiles on the strip: `U` and `Ω` are `C¹`, `Ψ` is `C²`. -/
structure HasProfileRegularityOn (U Ω Ψ : ℝ^3 → ℝ) (times : Set ℝ) : Prop where
  /-- `C¹` swirl profile. -/
  swirl_contDiffAt : ∀ q ∈ profileStrip times, ContDiffAt ℝ 1 U q
  /-- `C¹` vorticity profile. -/
  vorticity_contDiffAt : ∀ q ∈ profileStrip times, ContDiffAt ℝ 1 Ω q
  /-- `C²` stream function profile. -/
  streamFunction_contDiffAt : ∀ q ∈ profileStrip times, ContDiffAt ℝ 2 Ψ q

/-- The profile point of a point of the open meridian strip lies in the profile strip. -/
theorem meridianProfilePoint_mem_profileStrip {times : Set ℝ} {x : ℝ^2} {t : ℝ}
    (hx : x ∈ meridianDomain) (ht : t ∈ times) :
    meridianProfilePoint t x ∈ profileStrip times := by
  refine ⟨by simp [meridianProfilePoint, ht], ?_, ?_⟩
  · rw [meridianProfilePoint_apply_one]
    exact pow_pos hx.1 2
  · rw [meridianProfilePoint_apply_one]
    nlinarith [hx.1, hx.2]

/-- Every point of the profile strip is the profile point of a point of the meridian strip. -/
theorem exists_meridianProfilePoint_eq {times : Set ℝ} {q : ℝ^3} (hq : q ∈ profileStrip times) :
    meridianPoint (Real.sqrt (q 1)) (q 2) ∈ meridianDomain ∧
      meridianProfilePoint (q 0) (meridianPoint (Real.sqrt (q 1)) (q 2)) = q := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa using Real.sqrt_pos.2 hq.2.1
  · simpa using (Real.sqrt_lt' one_pos).2 (by simpa using hq.2.2)
  · ext i
    fin_cases i <;> simp [meridianProfilePoint, profilePoint, Real.sq_sqrt hq.2.1.le]

/-- Part I (6.2)-(6.4) in profile variables: for profiles with local regularity on the strip,
the meridian system of `ofProfiles U Ω Ψ` on a set of times is equivalent to the reduced Euler
equations on `0 < s < 1` with the wall condition `Ψ(t, 1, z) = 0`. -/
theorem satisfiesMeridianSystemOn_ofProfiles_iff {U Ω Ψ : ℝ^3 → ℝ} {times : Set ℝ}
    (hreg : HasProfileRegularityOn U Ω Ψ times) :
    SatisfiesMeridianSystemOn (ofProfiles U Ω Ψ) times ↔ SatisfiesProfileSystemOn U Ω Ψ times := by
  have hdiff {F : ℝ^3 → ℝ} {n : WithTop ℕ∞} (hF : ∀ q ∈ profileStrip times, ContDiffAt ℝ n F q)
      (hn : n ≠ 0) {x : ℝ^2} {t : ℝ} (hx : x ∈ meridianDomain) (ht : t ∈ times) :
      DifferentiableAt ℝ F (meridianProfilePoint t x) :=
    (hF _ (meridianProfilePoint_mem_profileStrip hx ht)).differentiableAt hn
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨hx, hqx⟩ := exists_meridianProfilePoint_eq hq
      have ht : q 0 ∈ times := hq.1
      have heq := h.swirl_equation hx ht
      rw [swirlResidual_ofProfiles (hdiff hreg.swirl_contDiffAt one_ne_zero hx ht)
        (hdiff hreg.streamFunction_contDiffAt two_ne_zero hx ht), hqx] at heq
      exact (mul_eq_zero.1 heq).resolve_left (pow_ne_zero 2 hx.1.ne')
    · intro q hq
      obtain ⟨hx, hqx⟩ := exists_meridianProfilePoint_eq hq
      have ht : q 0 ∈ times := hq.1
      have heq := h.vorticity_equation hx ht
      have hres := vorticityResidual_ofProfiles hx.1.ne'
        (hdiff hreg.swirl_contDiffAt one_ne_zero hx ht)
        (hdiff hreg.vorticity_contDiffAt one_ne_zero hx ht)
        (hdiff hreg.streamFunction_contDiffAt two_ne_zero hx ht)
      rw [heq, sub_self, hqx] at hres
      exact hres.symm
    · intro q hq
      obtain ⟨hx, hqx⟩ := exists_meridianProfilePoint_eq hq
      have ht : q 0 ∈ times := hq.1
      have heq := h.streamFunction_equation hx ht
      have hres := streamResidual_ofProfiles (U := U) (Ω := Ω) hx.1.ne'
        (hreg.streamFunction_contDiffAt _ (meridianProfilePoint_mem_profileStrip hx ht))
      rw [heq, sub_self, hqx] at hres
      have := (mul_eq_zero.1 hres.symm).resolve_left hx.1.ne'
      linarith
    · intro t ht z
      rw [← streamFunction_ofProfiles_wall U Ω Ψ z t]
      exact h.wall z ht
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x t hx ht
      rw [swirlResidual_ofProfiles (hdiff hreg.swirl_contDiffAt one_ne_zero hx ht)
        (hdiff hreg.streamFunction_contDiffAt two_ne_zero hx ht),
        h.swirl_equation _ (meridianProfilePoint_mem_profileStrip hx ht), mul_zero]
    · intro x t hx ht
      have hres := vorticityResidual_ofProfiles hx.1.ne'
        (hdiff hreg.swirl_contDiffAt one_ne_zero hx ht)
        (hdiff hreg.vorticity_contDiffAt one_ne_zero hx ht)
        (hdiff hreg.streamFunction_contDiffAt two_ne_zero hx ht)
      rw [h.vorticity_equation _ (meridianProfilePoint_mem_profileStrip hx ht)] at hres
      exact sub_eq_zero.1 hres
    · intro x t hx ht
      have hres := streamResidual_ofProfiles (U := U) (Ω := Ω) hx.1.ne'
        (hreg.streamFunction_contDiffAt _ (meridianProfilePoint_mem_profileStrip hx ht))
      rw [h.streamFunction_equation _ (meridianProfilePoint_mem_profileStrip hx ht),
        sub_self, mul_zero] at hres
      exact sub_eq_zero.1 hres
    · intro z t ht
      rw [streamFunction_ofProfiles_wall]
      exact h.wall ht z

/-- Local regularity of the profiles gives the classical regularity of the meridian fields. -/
theorem hasMeridianRegularityOn_ofProfiles {U Ω Ψ : ℝ^3 → ℝ} {times : Set ℝ}
    (hreg : HasProfileRegularityOn U Ω Ψ times) :
    HasMeridianRegularityOn (ofProfiles U Ω Ψ) times := by
  have hr : Differentiable ℝ (fun p : ℝ^2 × ℝ ↦ p.1 0) :=
    ((EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.fst ℝ (ℝ^2) ℝ)).differentiable
  have hchart : Differentiable ℝ (fun p : ℝ^2 × ℝ ↦ meridianProfilePoint p.2 p.1) :=
    (contDiff_meridianProfilePoint_uncurry (n := 1)).differentiable (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro x t hx ht
    have hU := (hreg.swirl_contDiffAt _
      (meridianProfilePoint_mem_profileStrip hx ht)).differentiableAt one_ne_zero
    exact (hr (x, t)).mul (hU.comp (x, t) (hchart (x, t)))
  · intro x t hx ht
    have hΩ := (hreg.vorticity_contDiffAt _
      (meridianProfilePoint_mem_profileStrip hx ht)).differentiableAt one_ne_zero
    exact (hr (x, t)).mul (hΩ.comp (x, t) (hchart (x, t)))
  · intro x t hx ht
    have hΨ := hreg.streamFunction_contDiffAt _ (meridianProfilePoint_mem_profileStrip hx ht)
    exact (EuclideanSpace.proj (0 : Fin 2) : ℝ^2 →L[ℝ] ℝ).contDiff.contDiffAt.mul
      (hΨ.comp x (contDiff_meridianProfilePoint t).contDiffAt)

/-- The axial reflection of the meridian plane is the reflection of the axial coordinate of
profile space. -/
theorem meridianProfilePoint_axialReflection (t : ℝ) (x : ℝ^2) :
    meridianProfilePoint t (axialReflection x) =
      coordinateReflection (2 : Fin 3) (meridianProfilePoint t x) := by
  ext i
  fin_cases i <;>
    simp [meridianProfilePoint, profilePoint, coordinateReflection_apply_same,
      coordinateReflection_apply_of_ne]

/-- Profiles with `U` even and `Ω`, `Ψ` odd in `z` give meridian fields in the reflection
class. -/
theorem hasReflectionSymmetry_ofProfiles {U Ω Ψ : ℝ^3 → ℝ}
    (hU : IsEvenUnderCoordinateReflection (2 : Fin 3) U)
    (hΩ : IsOddUnderCoordinateReflection (2 : Fin 3) Ω)
    (hΨ : IsOddUnderCoordinateReflection (2 : Fin 3) Ψ) :
    HasReflectionSymmetry (ofProfiles U Ω Ψ) := by
  refine ⟨fun t y ↦ ?_, fun t y ↦ ?_, fun t y ↦ ?_⟩
  · change (axialReflection y) 0 * U (meridianProfilePoint t (axialReflection y)) =
      y 0 * U (meridianProfilePoint t y)
    rw [meridianProfilePoint_axialReflection, hU, axialReflection_apply_zero]
  · change (axialReflection y) 0 * Ω (meridianProfilePoint t (axialReflection y)) =
      -(y 0 * Ω (meridianProfilePoint t y))
    rw [meridianProfilePoint_axialReflection, hΩ, axialReflection_apply_zero]
    ring
  · change (axialReflection y) 0 * Ψ (meridianProfilePoint t (axialReflection y)) =
      -(y 0 * Ψ (meridianProfilePoint t y))
    rw [meridianProfilePoint_axialReflection, hΨ, axialReflection_apply_zero]
    ring

/-- The meridian translation by `L` is the translation by `L` of the axial coordinate of
profile space. -/
theorem meridianProfilePoint_axialTranslate (L t : ℝ) (x : ℝ^2) :
    meridianProfilePoint t (axialTranslate L x) =
      meridianProfilePoint t x + EuclideanSpace.single (2 : Fin 3) L := by
  ext i
  fin_cases i <;> simp [meridianProfilePoint, profilePoint, axialTranslate]

/-- Profiles that are `L`-periodic in `z` give `L`-periodic meridian fields. -/
theorem isAxiallyPeriodic_ofProfiles {U Ω Ψ : ℝ^3 → ℝ} {L : ℝ}
    (hU : ∀ q, U (q + EuclideanSpace.single (2 : Fin 3) L) = U q)
    (hΩ : ∀ q, Ω (q + EuclideanSpace.single (2 : Fin 3) L) = Ω q)
    (hΨ : ∀ q, Ψ (q + EuclideanSpace.single (2 : Fin 3) L) = Ψ q) :
    IsAxiallyPeriodic L (ofProfiles U Ω Ψ) := by
  have h0 (x : ℝ^2) : (axialTranslate L x) 0 = x 0 := by simp [axialTranslate]
  refine ⟨fun x t ↦ ?_, fun x t ↦ ?_, fun x t ↦ ?_⟩
  · change (axialTranslate L x) 0 * U (meridianProfilePoint t (axialTranslate L x)) = _
    rw [meridianProfilePoint_axialTranslate, hU, h0]
    rfl
  · change (axialTranslate L x) 0 * Ω (meridianProfilePoint t (axialTranslate L x)) = _
    rw [meridianProfilePoint_axialTranslate, hΩ, h0]
    rfl
  · change (axialTranslate L x) 0 * Ψ (meridianProfilePoint t (axialTranslate L x)) = _
    rw [meridianProfilePoint_axialTranslate, hΨ, h0]
    rfl

end

end Euler.Cylinder
