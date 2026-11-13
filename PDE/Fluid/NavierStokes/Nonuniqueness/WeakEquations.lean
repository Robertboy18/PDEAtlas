/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.Representative
import PDE.Analysis.Calculus.Divergence
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Weak self-similar profile and eigenvalue equations

The self-similar Navier–Stokes profile equation of Hou, Wang and Yang ((1.6) and the first line
of (1.12)) is

`-½ U - ½ ξ·∇U + (U·∇)U - ΔU + ∇P = 0`,

which is `stationaryVelocityOperator U + ∇P = 0`. Testing with a smooth compactly supported
divergence-free field `φ` removes the pressure. Integrating every derivative of `U` by parts
and using `div U = 0` in the convection term gives the weak form

`∫ U·φ + ½ U·(Dφ ξ) - U·(Dφ U) - U·Δφ dξ = 0`,

where `(Dφ a)ᵢ = Σⱼ aⱼ ∂ⱼφᵢ`; the first coefficient is `-½ + 3/2 = 1`. This is
`WeakProfileEquation U`. The density involves `U` only through its values, so the equation
depends only on the almost-everywhere class of `U`; divergence-freeness of `U` is a separate
hypothesis wherever the equation is used.

The eigenvalue problem is `stationaryVelocityLinearization U v + ∇q = -μ v`, that is
`L_U v = μ v` for the linearized operator `L_U` of (1.9); the second line of (1.12) has
`λ̃ = -μ`, so `μ > 0` is an unstable eigenvalue. For `v` in whole-space `H¹`, the weak form
keeps the derivatives of `v`, moves the derivative of `U` in `(v·∇)U` onto `v ⊗ φ`, and
integrates `-Δv` by parts once:

`∫ (μ - ½) v·φ + Σᵢⱼ (Uⱼ - ½ ξⱼ) ∂ⱼvᵢ φᵢ - (div v) U·φ - U·(Dφ v) + ∇v : ∇φ dξ = 0`.

This is `WeakEigenEquation U μ v`. Again only the values of `U` occur. Both predicates assert
integrability of the density together with the vanishing of its integral, since Lean's
integral is totalized. `weakProfileDensity_eq_sum` and `weakEigenDensity_eq_sum` write the
densities in Cartesian coordinates, with `∂ⱼφᵢ` the coordinate partial derivatives.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 1.2, (1.6), p. 3,
  Section 1.3, (1.9), p. 3, and (1.12), p. 4.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open scoped RealInnerProductSpace Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-- A smooth compactly supported test field on `ℝ^n` with vanishing divergence. -/
def IsSolenoidalTestField {n : ℕ} (φ : ℝ^n → ℝ^n) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ ∀ x, PDE.divergence φ x = 0

/-- Solenoidal test fields are closed under addition. -/
theorem IsSolenoidalTestField.add {n : ℕ} {u v : ℝ^n → ℝ^n} (hu : IsSolenoidalTestField u)
    (hv : IsSolenoidalTestField v) : IsSolenoidalTestField (u + v) := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, fun x ↦ ?_⟩
  change PDE.divergence (fun y ↦ u y + v y) x = 0
  rw [PDE.divergence_add_of_differentiableAt (hu.1.differentiable (by simp) x)
    (hv.1.differentiable (by simp) x), hu.2.2 x, hv.2.2 x, add_zero]

/-- Solenoidal test fields are closed under scalar multiplication. -/
theorem IsSolenoidalTestField.smul {n : ℕ} {u : ℝ^n → ℝ^n} (hu : IsSolenoidalTestField u)
    (c : ℝ) : IsSolenoidalTestField (c • u) := by
  refine ⟨hu.1.const_smul c, hu.2.1.smul_left, fun x ↦ ?_⟩
  have h := PDE.Analysis.divergence_smul (a := fun _ ↦ c) (differentiableAt_const c)
    ((hu.1.differentiable (by simp)) x)
  change PDE.divergence (fun y ↦ c • u y) x = 0
  rw [h, fderiv_const_apply, zero_apply, zero_add, hu.2.2 x, mul_zero]

/-- The integrand of the weak self-similar profile equation tested with `φ`:
`U·φ + ½ U·(Dφ(ξ) ξ) - U·(Dφ(ξ) U) - U·Δφ` at the point `ξ`. -/
def weakProfileDensity (U φ : ℝ^3 → ℝ^3) (x : ℝ^3) : ℝ :=
  ⟪U x, φ x⟫ + (1 / 2 : ℝ) * ⟪U x, fderiv ℝ φ x x⟫ - ⟪U x, fderiv ℝ φ x (U x)⟫ -
    ⟪U x, PDE.laplacian φ x⟫

/-- `U` is a weak solution of the self-similar profile equation
`-½ U - ½ ξ·∇U + div(U ⊗ U) - ΔU + ∇P = 0`: for every smooth compactly supported
divergence-free `φ`, the density `weakProfileDensity U φ` is integrable with integral zero.
For divergence-free `U` this is the weak form of `stationaryVelocityOperator U + ∇P = 0`,
Hou–Wang–Yang (1.6). -/
def WeakProfileEquation (U : ℝ^3 → ℝ^3) : Prop :=
  ∀ φ : ℝ^3 → ℝ^3, IsSolenoidalTestField φ →
    Integrable (weakProfileDensity U φ) ∧ ∫ x, weakProfileDensity U φ x = 0

/-- The integrand of the weak eigenvalue equation `L_U v = μ v` tested with `φ`, written with
the chosen representatives of `v` and of its weak gradient `∂ⱼvᵢ`:
`(μ - ½) v·φ + Σᵢⱼ (Uⱼ - ½ ξⱼ) ∂ⱼvᵢ φᵢ - (div v) U·φ - U·(Dφ v) + Σᵢⱼ ∂ⱼvᵢ ∂ⱼφᵢ`. -/
def weakEigenDensity (U : ℝ^3 → ℝ^3) (μ : ℝ) (v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)))
    (φ : ℝ^3 → ℝ^3) (x : ℝ^3) : ℝ :=
  (μ - 1 / 2) * ⟪Stationary.representative v x, φ x⟫ +
    (∑ i, ∑ j, (U x j - (1 / 2 : ℝ) * x j) * Stationary.gradientRepresentative v x i j *
      φ x i) -
    (∑ j, Stationary.gradientRepresentative v x j j) * ⟪U x, φ x⟫ -
    ⟪U x, fderiv ℝ φ x (Stationary.representative v x)⟫ +
    ∑ i, ∑ j, Stationary.gradientRepresentative v x i j * (∂[j] (fun y ↦ φ y i)) x

/-- `v ∈ H¹(ℝ^3; ℝ^3)` is a weak eigenfunction of the linearization at `U` with eigenvalue
`μ`: the weak form of `stationaryVelocityLinearization U v + ∇q = -μ v`, equivalently
`L_U v = μ v` for the operator `L_U` of Hou–Wang–Yang (1.9), with `λ̃ = -μ` in (1.12). For
every smooth compactly supported divergence-free `φ`, the density `weakEigenDensity U μ v φ`
is integrable with integral zero. -/
def WeakEigenEquation (U : ℝ^3 → ℝ^3) (μ : ℝ) (v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) :
    Prop :=
  ∀ φ : ℝ^3 → ℝ^3, IsSolenoidalTestField φ →
    Integrable (weakEigenDensity U μ v φ) ∧ ∫ x, weakEigenDensity U μ v φ x = 0

/-- Coordinate form of the profile density for a twice differentiable test field:
`Σᵢ Uᵢ φᵢ + ½ Σᵢⱼ Uᵢ ξⱼ ∂ⱼφᵢ - Σᵢⱼ Uᵢ Uⱼ ∂ⱼφᵢ - Σᵢ Uᵢ Δφᵢ`. -/
theorem weakProfileDensity_eq_sum (U : ℝ^3 → ℝ^3) {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ 2 φ)
    (x : ℝ^3) :
    weakProfileDensity U φ x =
      ∑ i, U x i * φ x i + (1 / 2 : ℝ) * ∑ i, ∑ j, U x i * x j * (∂[j] (fun y ↦ φ y i)) x -
        ∑ i, ∑ j, U x i * U x j * (∂[j] (fun y ↦ φ y i)) x -
        ∑ i, U x i * PDE.laplacian (fun y ↦ φ y i) x := by
  have hd : DifferentiableAt ℝ φ x := (hφ.differentiable (by norm_num)) x
  rw [weakProfileDensity, PDE.inner_fderiv_apply_eq_sum hd, PDE.inner_fderiv_apply_eq_sum hd,
    EuclideanSpace.real_inner_eq_sum, EuclideanSpace.real_inner_eq_sum]
  simp only [PDE.laplacian_apply_of_contDiff hφ]

/-- Coordinate form of the eigenvalue density for a differentiable test field. -/
theorem weakEigenDensity_eq_sum (U : ℝ^3 → ℝ^3) (μ : ℝ)
    (v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ 1 φ)
    (x : ℝ^3) :
    weakEigenDensity U μ v φ x =
      (μ - 1 / 2) * ∑ i, Stationary.representative v x i * φ x i +
        (∑ i, ∑ j, (U x j - (1 / 2 : ℝ) * x j) * Stationary.gradientRepresentative v x i j *
          φ x i) -
        (∑ j, Stationary.gradientRepresentative v x j j) * ∑ i, U x i * φ x i -
        (∑ i, ∑ j, U x i * Stationary.representative v x j * (∂[j] (fun y ↦ φ y i)) x) +
        ∑ i, ∑ j, Stationary.gradientRepresentative v x i j * (∂[j] (fun y ↦ φ y i)) x := by
  have hd : DifferentiableAt ℝ φ x := (hφ.differentiable (by norm_num)) x
  rw [weakEigenDensity, PDE.inner_fderiv_apply_eq_sum hd, EuclideanSpace.real_inner_eq_sum,
    EuclideanSpace.real_inner_eq_sum]

/-- The profile density depends only on the almost-everywhere class of the field. -/
theorem weakProfileDensity_congr_ae {U V : ℝ^3 → ℝ^3} (h : U =ᵐ[volume] V)
    (φ : ℝ^3 → ℝ^3) : weakProfileDensity U φ =ᵐ[volume] weakProfileDensity V φ := by
  filter_upwards [h] with x hx
  simp only [weakProfileDensity, hx]

/-- The weak profile equation depends only on the almost-everywhere class of the field. -/
theorem WeakProfileEquation.congr_ae {U V : ℝ^3 → ℝ^3} (hU : WeakProfileEquation U)
    (h : U =ᵐ[volume] V) : WeakProfileEquation V := by
  intro φ hφ
  obtain ⟨hint, hzero⟩ := hU φ hφ
  have hd := weakProfileDensity_congr_ae h φ
  exact ⟨hint.congr hd, (integral_congr_ae hd).symm.trans hzero⟩

/-- The eigenvalue density depends only on the almost-everywhere class of the base field. -/
theorem weakEigenDensity_congr_ae {U V : ℝ^3 → ℝ^3} (h : U =ᵐ[volume] V) (μ : ℝ)
    (v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))) (φ : ℝ^3 → ℝ^3) :
    weakEigenDensity U μ v φ =ᵐ[volume] weakEigenDensity V μ v φ := by
  filter_upwards [h] with x hx
  simp only [weakEigenDensity, hx]

/-- The weak eigenvalue equation depends only on the almost-everywhere class of the base
field. -/
theorem WeakEigenEquation.congr_ae {U V : ℝ^3 → ℝ^3} {μ : ℝ}
    {v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))} (hU : WeakEigenEquation U μ v)
    (h : U =ᵐ[volume] V) : WeakEigenEquation V μ v := by
  intro φ hφ
  obtain ⟨hint, hzero⟩ := hU φ hφ
  have hd := weakEigenDensity_congr_ae h μ v φ
  exact ⟨hint.congr hd, (integral_congr_ae hd).symm.trans hzero⟩

end NavierStokes.Nonuniqueness
