/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.PhysicalEvolution
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Cartesian diffusion of axisymmetric reconstructions

An axisymmetric field on `ℝ^3` is described by profiles of `(t, s, z)` with `s = x² + y²` the
squared cylindrical radius. The scalar Cartesian Laplacian of such a lift `F(t, x² + y², z)` is

`Δ (F ∘ lift) = 4 F_s + 4 s F_ss + F_zz`,

which is `spacetimeSquaredRadiusLaplacian`, while the operator appearing in the reduced
axisymmetric Navier–Stokes equations for `u_θ / r` and `ω_θ / r` is

`8 F_s + 4 s F_ss + F_zz`,

which is `spacetimeSquaredRadiusDiffusion` (the radial-four-plus-axial Laplacian of
`ReducedNavierStokes`, written in `s`). The difference between the two, `4 F_s`, is exactly what
the extra factor `x` or `y` contributes when the Laplacian acts on a product `x · (F ∘ lift)`.
These identities give the Cartesian vector Laplacian of the reconstructed axisymmetric
vorticity. All formulas are polynomial in the Cartesian
coordinates and the profile derivatives; there is no division by `r`, so every statement holds
on the symmetry axis as well as off it.

## Main results

* `laplacian_squaredCylindricalLift`, `spatialLaplacian_spacetimeSquaredCylindricalLift_eq`:
  the scalar Laplacian of a squared-cylindrical lift is the squared-radius scalar Laplacian of
  the profile.
* `laplacian_coordinate_zero_mul_squaredCylindricalLift`,
  `laplacian_coordinate_one_mul_squaredCylindricalLift`: multiplying the lift by `x` or `y`
  converts the scalar Laplacian into the radial-four coefficient
  `meridionalVorticityCoefficient`.
* `spacetimeAxisymmetricVorticity_eq_vorticityFromCoefficients`: the curl of the reconstructed
  velocity is the two-coefficient reconstruction with `Ω = -(8 Ψ_s + 4 s Ψ_ss + Ψ_zz)`.
* `spacetimeSquaredRadiusLaplacian_axialReconstruction`: the scalar Laplacian of the axial
  component `2U + 2s U_s` is the same reconstruction applied to the diffusion of `U`.
* `spatialVectorLaplacian_vorticityFromCoefficients`: the Cartesian vector Laplacian of
  `spacetimeAxisymmetricVorticityFromCoefficients U Ω` is the reconstruction from the
  diffused coefficients `(8∂_s + 4s∂_ss + ∂_zz) U` and `(8∂_s + 4s∂_ss + ∂_zz) Ω`. This is the
  Cartesian form of the statement that the viscous term of the axisymmetric vorticity equation
  acts on the reduced unknowns through the radial-four-plus-axial Laplacian.

## Implementation notes

The Laplacian identities assume `C^∞` profiles so that coordinate derivatives commute. The
reconstruction takes `Ω` as an unknown independent of the streamfunction `Ψ`. The reduced stream
equation identifying them is a hypothesis of the local theorems in `LocalEvolution`.

## References

* T. Y. Hou and C. Li, "Dynamic stability of the three-dimensional axisymmetric Navier-Stokes
  equations with swirl", Comm. Pure Appl. Math. 61 (2008), no. 5, 661-697, for the reduced unknowns
  and the operator `∂ᵣᵣ + 3r⁻¹∂ᵣ + ∂_zz`.
  <https://doi.org/10.1002/cpa.20212>
-/

@[expose] public section

open PDE (SpaceTime laplacian)

namespace AxisymmetricFlow

open EuclideanSpace
open PDE.Common
open PDE.CoordinateSystems

set_option linter.missingDocs true

noncomputable section

/-- The radial-four-plus-axial Laplacian written directly in squared-radius
spacetime coordinates `(t,s,z)`. -/
def spacetimeSquaredRadiusDiffusion
    (F : SpaceTime 2 → ℝ) (q : SpaceTime 2) : ℝ :=
  8 * (∂[(1 : Fin 3)] F) q +
    4 * q 1 * (∂[(1 : Fin 3)] (∂[(1 : Fin 3)] F)) q +
    (∂[(2 : Fin 3)] (∂[(2 : Fin 3)] F)) q

/-- The ordinary scalar Laplacian in squared-radius spacetime coordinates.
Unlike `spacetimeSquaredRadiusDiffusion`, this is the radial-two operator and
has coefficient four, rather than eight, on the first radial derivative. -/
def spacetimeSquaredRadiusLaplacian
    (F : SpaceTime 2 → ℝ) (q : SpaceTime 2) : ℝ :=
  4 * (∂[(1 : Fin 3)] F) q +
    4 * q 1 * (∂[(1 : Fin 3)] (∂[(1 : Fin 3)] F)) q +
    (∂[(2 : Fin 3)] (∂[(2 : Fin 3)] F)) q

/-- Smooth profiles are preserved by the regular squared-radius diffusion
operator. -/
theorem contDiff_spacetimeSquaredRadiusDiffusion
    {F : SpaceTime 2 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (spacetimeSquaredRadiusDiffusion F) := by
  have hS : ContDiff ℝ (⊤ : ℕ∞) fun q : SpaceTime 2 ↦ q 1 := contDiff_euclidean.1 contDiff_id 1
  have hFs := PDE.contDiff_top_partialDeriv hF (i := (1 : Fin 3))
  exact ((contDiff_const.mul hFs).add ((contDiff_const.mul hS).mul
    (PDE.contDiff_top_partialDeriv hFs))).add
      (PDE.contDiff_top_partialDeriv (PDE.contDiff_top_partialDeriv hF (i := 2)))

/-- The coordinate derivative of `a f + b s g`, where `s` is the squared-radius coordinate. -/
private theorem partialDeriv_mul_add_coord_mul {f g : SpaceTime 2 → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (a b : ℝ) (i : Fin 3) (p : SpaceTime 2) :
    (∂[i] fun y ↦ a * f y + b * y 1 * g y) p =
      a * (∂[i] f) p + b * ((if i = 1 then 1 else 0) * g p + p 1 * (∂[i] g) p) := by
  have hs : Differentiable ℝ fun y : SpaceTime 2 ↦ y 1 :=
    (differentiable_piLp _).1 differentiable_id 1
  have hc (c : ℝ) (u : SpaceTime 2 → ℝ) : (∂[i] fun y ↦ c * u y) p = c * (∂[i] u) p :=
    PDE.partialDeriv_const_smul c
  rw [PDE.partialDeriv_add (by fun_prop) (by fun_prop), PDE.partialDeriv_mul (by fun_prop) (hg p),
    hc, hc, PDE.partialDeriv_coord]
  ring

/-- The coordinate derivatives of the squared-radius diffusion of a smooth profile. -/
private theorem partialDeriv_spacetimeSquaredRadiusDiffusion {F : SpaceTime 2 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin 3) (p : SpaceTime 2) :
    (∂[i] (spacetimeSquaredRadiusDiffusion F)) p =
      8 * (∂[i] (∂[1] F)) p + 4 * ((if i = 1 then 1 else 0) * (∂[1] (∂[1] F)) p +
        p 1 * (∂[i] (∂[1] (∂[1] F))) p) + (∂[i] (∂[2] (∂[2] F))) p := by
  have hd {G : SpaceTime 2 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (j : Fin 3) :
      Differentiable ℝ (∂[j] G) := (PDE.contDiff_top_partialDeriv hG).differentiable (by simp)
  have hFs := PDE.contDiff_top_partialDeriv hF (i := 1)
  have hs : Differentiable ℝ fun y : SpaceTime 2 ↦ y 1 :=
    (differentiable_piLp _).1 differentiable_id 1
  have h₁ := hd hF 1
  have h₂ := hd hFs 1
  change (∂[i] fun p ↦ (8 * (∂[1] F) p + 4 * p 1 * (∂[1] (∂[1] F)) p) +
    (∂[2] (∂[2] F)) p) p = _
  rw [PDE.partialDeriv_add (by fun_prop) (hd (PDE.contDiff_top_partialDeriv hF (i := 2)) 2 p),
    partialDeriv_mul_add_coord_mul h₁ h₂]

/-- Axial differentiation commutes with the regular squared-radius diffusion
operator. -/
theorem spacetimeSquaredRadiusDiffusion_partialDeriv_two
    {F : SpaceTime 2 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (q : SpaceTime 2) :
    spacetimeSquaredRadiusDiffusion (∂[(2 : Fin 3)] F) q =
      (∂[(2 : Fin 3)] (spacetimeSquaredRadiusDiffusion F)) q := by
  have hFs := PDE.contDiff_top_partialDeriv hF (i := (1 : Fin 3))
  have hcomm := PDE.partialDeriv_partialDeriv_comm_of_contDiff 1 2 (hF.of_le (by simp))
  have hcomm' := PDE.partialDeriv_partialDeriv_comm_of_contDiff 1 2 (hFs.of_le (by simp))
  rw [partialDeriv_spacetimeSquaredRadiusDiffusion hF]
  simp only [spacetimeSquaredRadiusDiffusion, hcomm, hcomm', Fin.reduceEq, ite_false]
  ring

/-- The Cartesian scalar Laplacian of a squared-cylindrical lift has its
regular squared-radius formula, including on the symmetry axis. -/
theorem laplacian_squaredCylindricalLift
    {F : ℝ^2 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : ℝ^3) :
    laplacian (squaredCylindricalLift F) x =
      4 * cylindricalRadiusSq x *
          (∂[(0 : Fin 2)] (∂[(0 : Fin 2)] F))
            (squaredCylindricalMap x) +
        4 * (∂[(0 : Fin 2)] F) (squaredCylindricalMap x) +
        (∂[(1 : Fin 2)] (∂[(1 : Fin 2)] F))
          (squaredCylindricalMap x) := by
  have hFs := PDE.contDiff_top_partialDeriv hF (i := (0 : Fin 2))
  -- the two horizontal second derivatives have the same form
  have hsecond (k : Fin 3) (hk : ∀ {Φ : ℝ^2 → ℝ}, ContDiff ℝ 1 Φ → ∀ y : ℝ^3,
      (∂[k] (squaredCylindricalLift Φ)) y = 2 * y k * (∂[0] Φ) (squaredCylindricalMap y)) :
      (∂[k] (∂[k] (squaredCylindricalLift F))) x =
        2 * (∂[0] F) (squaredCylindricalMap x) +
          4 * x k ^ 2 * (∂[0] (∂[0] F)) (squaredCylindricalMap x) := by
    have h2 : (∂[k] fun y : ℝ^3 ↦ 2 * y k) x = 2 := by
      simpa using PDE.partialDeriv_const_smul (2 : ℝ) (i := k) (f := fun y : ℝ^3 ↦ y k) (x := x)
    rw [show ∂[k] (squaredCylindricalLift F) =
        fun y ↦ 2 * y k * squaredCylindricalLift (∂[0] F) y from funext (hk (hF.of_le (by simp))),
      PDE.partialDeriv_mul ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x k).differentiableAt.const_mul 2)
        ((contDiff_squaredCylindricalLift hFs).differentiable (by simp)).differentiableAt,
      hk (hFs.of_le (by simp)), h2, squaredCylindricalLift]
    ring
  have hthird : (∂[2] (∂[2] (squaredCylindricalLift F))) x =
      (∂[1] (∂[1] F)) (squaredCylindricalMap x) := by
    rw [show ∂[2] (squaredCylindricalLift F) = squaredCylindricalLift (∂[1] F) from
      funext (partialDeriv_two_squaredCylindricalLift (hF.of_le (by simp)))]
    exact partialDeriv_two_squaredCylindricalLift
      ((PDE.contDiff_top_partialDeriv hF).of_le (by simp)) x
  unfold laplacian cylindricalRadiusSq
  rw [Fin.sum_univ_three, hsecond 0 partialDeriv_zero_squaredCylindricalLift,
    hsecond 1 partialDeriv_one_squaredCylindricalLift, hthird]
  ring

/-- Spacetime version of `laplacian_squaredCylindricalLift`, with the
Laplacian taken only in the three spatial coordinates. -/
theorem spatialLaplacian_spacetimeSquaredCylindricalLift
    {F : SpaceTime 2 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.spatialLaplacian 3
        (spacetimeSquaredCylindricalLift F) (timeSpaceCons t x) =
      4 * cylindricalRadiusSq x *
          (∂[(1 : Fin 3)] (∂[(1 : Fin 3)] F))
            (timeSpaceCons t (squaredCylindricalMap x)) +
        4 * (∂[(1 : Fin 3)] F)
          (timeSpaceCons t (squaredCylindricalMap x)) +
        (∂[(2 : Fin 3)] (∂[(2 : Fin 3)] F))
          (timeSpaceCons t (squaredCylindricalMap x)) := by
  rw [IncompressibleFlow.spatialLaplacian_timeSpaceCons
    ((contDiff_spacetimeSquaredCylindricalLift hF).of_le
      (WithTop.coe_le_coe.mpr le_top))]
  change laplacian (squaredCylindricalLift (profileSlice F t)) x = _
  rw [laplacian_squaredCylindricalLift
    (contDiff_profileSlice hF t)]
  have hsliceZero : (∂[(0 : Fin 2)] (profileSlice F t)) = profileSlice (∂[(1 : Fin 3)] F) t :=
    funext (partialDeriv_profileSlice (hF.differentiable (by simp)) 0 t)
  have hsliceOne : (∂[(1 : Fin 2)] (profileSlice F t)) = profileSlice (∂[(2 : Fin 3)] F) t :=
    funext (partialDeriv_profileSlice (hF.differentiable (by simp)) 1 t)
  rw [hsliceZero,
    partialDeriv_profileSlice
      ((PDE.contDiff_top_partialDeriv hF).differentiable (by simp)) 0,
    hsliceOne,
    partialDeriv_profileSlice
      ((PDE.contDiff_top_partialDeriv hF).differentiable (by simp)) 1]
  rw [show Fin.succ (0 : Fin 2) = (1 : Fin 3) by decide,
    show Fin.succ (1 : Fin 2) = (2 : Fin 3) by decide]
  simp only [profileSlice_apply]

/-- The spacetime Cartesian scalar Laplacian is the squared-radius scalar
Laplacian evaluated at `(t,s,z)`. -/
theorem spatialLaplacian_spacetimeSquaredCylindricalLift_eq
    {F : SpaceTime 2 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.spatialLaplacian 3
        (spacetimeSquaredCylindricalLift F) (timeSpaceCons t x) =
      spacetimeSquaredRadiusLaplacian F
        (timeSpaceCons t (squaredCylindricalMap x)) := by
  rw [spatialLaplacian_spacetimeSquaredCylindricalLift hF]
  unfold spacetimeSquaredRadiusLaplacian
  have hq : timeSpaceCons t (squaredCylindricalMap x) 1 =
      cylindricalRadiusSq x := by
    change squaredCylindricalMap x 0 = cylindricalRadiusSq x
    exact squaredCylindricalMap_apply_zero x
  rw [hq]
  ring

/-- The fixed-time meridional coefficient is the spacetime squared-radius
diffusion coefficient at the corresponding point. -/
theorem meridionalVorticityCoefficient_profileSlice
    {F : SpaceTime 2 → ℝ} (hF : ContDiff ℝ 2 F)
    (t : ℝ) (q : ℝ^2) :
    meridionalVorticityCoefficient (profileSlice F t) q =
      spacetimeSquaredRadiusDiffusion F (timeSpaceCons t q) := by
  have hsliceZero : (∂[(0 : Fin 2)] (profileSlice F t)) = profileSlice (∂[(1 : Fin 3)] F) t :=
    funext (partialDeriv_profileSlice (hF.differentiable (by simp)) 0 t)
  have hsliceOne : (∂[(1 : Fin 2)] (profileSlice F t)) = profileSlice (∂[(2 : Fin 3)] F) t :=
    funext (partialDeriv_profileSlice (hF.differentiable (by simp)) 1 t)
  unfold meridionalVorticityCoefficient spacetimeSquaredRadiusDiffusion
  rw [hsliceZero,
    partialDeriv_profileSlice
      ((PDE.contDiff_partialDeriv_of_succ (m := 1) hF).differentiable (by simp)) 0,
    hsliceOne,
    partialDeriv_profileSlice
      ((PDE.contDiff_partialDeriv_of_succ (m := 1) hF).differentiable (by simp)) 1]
  rw [show Fin.succ (0 : Fin 2) = (1 : Fin 3) by decide,
    show Fin.succ (1 : Fin 2) = (2 : Fin 3) by decide]
  simp only [profileSlice_apply]
  have hq : timeSpaceCons t q (1 : Fin 3) = q 0 := rfl
  rw [hq]
  ring

/-- The curl reconstruction uses the negative squared-radius diffusion of the streamfunction
as its azimuthal-vorticity coefficient. -/
theorem spacetimeAxisymmetricVorticity_eq_vorticityFromCoefficients
    {U Ψ : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ 1 U) (hΨ : ContDiff ℝ 2 Ψ) :
    spacetimeAxisymmetricVorticity U Ψ =
      spacetimeAxisymmetricVorticityFromCoefficients U
        (fun q ↦ -spacetimeSquaredRadiusDiffusion Ψ q) := by
  funext xt
  rw [← timeSpaceCons_spatialPart xt,
    spacetimeAxisymmetricVorticity_timeSpaceCons_eq_cartesianVector
      hU hΨ]
  simp only [squaredCylindricalLift, meridionalVorticityCoefficient_profileSlice hΨ,
    partialDeriv_profileSlice (hU.differentiable (by simp))]
  ext i
  fin_cases i <;>
    simp only [cartesianVector, spacetimeAxisymmetricVorticityFromCoefficients,
      spacetimeSquaredCylindricalLift, spacetimeSquaredCylindricalMap, profileSlice, Fin.isValue,
      spatialPart_apply, timeSpaceCons_spatialPart, PDE.time_apply, Nat.reduceAdd,
      Fin.succ_one_eq_two, Fin.succ_zero_eq_one, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, neg_mul, mul_neg,
      sub_neg_eq_add] <;>
    ring

/-- Multiplying a squared-cylindrical lift by the first Cartesian coordinate
turns the scalar Cartesian Laplacian into the radial-four coefficient. -/
theorem laplacian_coordinate_zero_mul_squaredCylindricalLift
    {F : ℝ^2 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : ℝ^3) :
    laplacian (fun y ↦ y 0 * squaredCylindricalLift F y) x =
      x 0 * meridionalVorticityCoefficient F (squaredCylindricalMap x) := by
  rw [PDE.laplacian_coordinate_mul 0 (squaredCylindricalLift F) x
    ((contDiff_squaredCylindricalLift hF).of_le
      (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  rw [laplacian_squaredCylindricalLift hF]
  rw [partialDeriv_zero_squaredCylindricalLift
    (hF.of_le (WithTop.coe_le_coe.mpr le_top))]
  unfold meridionalVorticityCoefficient cylindricalRadiusSq
  rw [squaredCylindricalMap_apply_zero]
  unfold cylindricalRadiusSq
  ring

/-- Multiplying a squared-cylindrical lift by the second Cartesian coordinate
turns the scalar Cartesian Laplacian into the radial-four coefficient. -/
theorem laplacian_coordinate_one_mul_squaredCylindricalLift
    {F : ℝ^2 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : ℝ^3) :
    laplacian (fun y ↦ y 1 * squaredCylindricalLift F y) x =
      x 1 * meridionalVorticityCoefficient F (squaredCylindricalMap x) := by
  rw [PDE.laplacian_coordinate_mul 1 (squaredCylindricalLift F) x
    ((contDiff_squaredCylindricalLift hF).of_le
      (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  rw [laplacian_squaredCylindricalLift hF]
  rw [partialDeriv_one_squaredCylindricalLift
    (hF.of_le (WithTop.coe_le_coe.mpr le_top))]
  unfold meridionalVorticityCoefficient cylindricalRadiusSq
  rw [squaredCylindricalMap_apply_zero]
  unfold cylindricalRadiusSq
  ring

/-! ## Vector Laplacian of the reconstructed vorticity -/

/-- First component of the Cartesian vector Laplacian of independently
reconstructed axisymmetric vorticity. -/
theorem spatialVectorLaplacian_vorticityFromCoefficients_apply_zero
    {U Ω : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.spatialVectorLaplacian 3
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
        (timeSpaceCons t x) 0 =
      -x 0 * spacetimeSquaredRadiusDiffusion (∂[(2 : Fin 3)] U)
          (timeSpaceCons t (squaredCylindricalMap x)) -
        x 1 * spacetimeSquaredRadiusDiffusion Ω
          (timeSpaceCons t (squaredCylindricalMap x)) := by
  have hUz := PDE.contDiff_top_partialDeriv hU (i := (2 : Fin 3))
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (fun y ↦ spacetimeAxisymmetricVorticityFromCoefficients U Ω y 0) := by
    simpa [Function.comp_def] using (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff.comp
      (contDiff_spacetimeAxisymmetricVorticityFromCoefficients (m := ⊤) hU hΩ)
  have hlift {Φ : ℝ^2 → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin 3) :
      ContDiffAt ℝ 2 (fun y : ℝ^3 ↦ y i * squaredCylindricalLift Φ y) x :=
    (((contDiff_euclidean.1 contDiff_id i).mul (contDiff_squaredCylindricalLift hΦ)).of_le
      (by simp)).contDiffAt
  have hneg (F : ℝ^3 → ℝ) : laplacian (fun y ↦ -F y) x = -laplacian F x := PDE.laplacian_neg F x
  rw [IncompressibleFlow.spatialVectorLaplacian_apply,
    IncompressibleFlow.spatialLaplacian_timeSpaceCons (hcomp.of_le (by simp)),
    show (fun y ↦ spacetimeAxisymmetricVorticityFromCoefficients U Ω (timeSpaceCons t y) 0) =
        fun y ↦ -(y 0 * squaredCylindricalLift (profileSlice (∂[(2 : Fin 3)] U) t) y) -
          y 1 * squaredCylindricalLift (profileSlice Ω t) y by
      funext y; simp [spacetimeSquaredCylindricalLift_timeSpaceCons],
    PDE.laplacian_sub _ _ x (hlift (contDiff_profileSlice hUz t) 0).neg
      (hlift (contDiff_profileSlice hΩ t) 1), hneg,
    laplacian_coordinate_zero_mul_squaredCylindricalLift (contDiff_profileSlice hUz t),
    laplacian_coordinate_one_mul_squaredCylindricalLift (contDiff_profileSlice hΩ t),
    meridionalVorticityCoefficient_profileSlice (hUz.of_le (by simp)),
    meridionalVorticityCoefficient_profileSlice (hΩ.of_le (by simp))]
  ring

/-- Second component of the Cartesian vector Laplacian of independently
reconstructed axisymmetric vorticity. -/
theorem spatialVectorLaplacian_vorticityFromCoefficients_apply_one
    {U Ω : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.spatialVectorLaplacian 3
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
        (timeSpaceCons t x) 1 =
      -x 1 * spacetimeSquaredRadiusDiffusion (∂[(2 : Fin 3)] U)
          (timeSpaceCons t (squaredCylindricalMap x)) +
        x 0 * spacetimeSquaredRadiusDiffusion Ω
          (timeSpaceCons t (squaredCylindricalMap x)) := by
  have hUz := PDE.contDiff_top_partialDeriv hU (i := (2 : Fin 3))
  have hcomp : ContDiff ℝ (⊤ : ℕ∞)
      (fun y ↦ spacetimeAxisymmetricVorticityFromCoefficients U Ω y 1) := by
    simpa [Function.comp_def] using (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).contDiff.comp
      (contDiff_spacetimeAxisymmetricVorticityFromCoefficients (m := ⊤) hU hΩ)
  have hlift {Φ : ℝ^2 → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : Fin 3) :
      ContDiffAt ℝ 2 (fun y : ℝ^3 ↦ y i * squaredCylindricalLift Φ y) x :=
    (((contDiff_euclidean.1 contDiff_id i).mul (contDiff_squaredCylindricalLift hΦ)).of_le
      (by simp)).contDiffAt
  have hneg (F : ℝ^3 → ℝ) : laplacian (fun y ↦ -F y) x = -laplacian F x := PDE.laplacian_neg F x
  rw [IncompressibleFlow.spatialVectorLaplacian_apply,
    IncompressibleFlow.spatialLaplacian_timeSpaceCons (hcomp.of_le (by simp)),
    show (fun y ↦ spacetimeAxisymmetricVorticityFromCoefficients U Ω (timeSpaceCons t y) 1) =
        fun y ↦ -(y 1 * squaredCylindricalLift (profileSlice (∂[(2 : Fin 3)] U) t) y) +
          y 0 * squaredCylindricalLift (profileSlice Ω t) y by
      funext y; simp [spacetimeSquaredCylindricalLift_timeSpaceCons],
    PDE.laplacian_add _ _ x (hlift (contDiff_profileSlice hUz t) 1).neg
      (hlift (contDiff_profileSlice hΩ t) 0), hneg,
    laplacian_coordinate_one_mul_squaredCylindricalLift (contDiff_profileSlice hUz t),
    laplacian_coordinate_zero_mul_squaredCylindricalLift (contDiff_profileSlice hΩ t),
    meridionalVorticityCoefficient_profileSlice (hUz.of_le (by simp)),
    meridionalVorticityCoefficient_profileSlice (hΩ.of_le (by simp))]
  ring

/-- The scalar squared-radius Laplacian of the regular axial reconstruction
`U ↦ 2U + 2s ∂sU` is the corresponding reconstruction of the swirl
diffusion operator. -/
theorem spacetimeSquaredRadiusLaplacian_axialReconstruction
    {U : SpaceTime 2 → ℝ} (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (q : SpaceTime 2) :
    spacetimeSquaredRadiusLaplacian
        (fun p ↦ 2 * U p + 2 * p 1 * (∂[(1 : Fin 3)] U) p) q =
      2 * spacetimeSquaredRadiusDiffusion U q +
        2 * q 1 * (∂[(1 : Fin 3)]
          (spacetimeSquaredRadiusDiffusion U)) q := by
  have hd {G : SpaceTime 2 → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (j : Fin 3) :
      Differentiable ℝ (∂[j] G) := (PDE.contDiff_top_partialDeriv hG).differentiable (by simp)
  have hA := PDE.contDiff_top_partialDeriv hU (i := 1)
  have hG (i : Fin 3) :=
    partialDeriv_mul_add_coord_mul (hU.differentiable (by simp)) (hd hU 1) 2 2 i
  -- the two first derivatives of the reconstruction `G = 2U + 2s U_s`
  have hGs : ∂[1] (fun p ↦ 2 * U p + 2 * p 1 * (∂[1] U) p) =
      fun p ↦ 4 * (∂[1] U) p + 2 * p 1 * (∂[1] (∂[1] U)) p := by
    funext p
    rw [hG]
    simp only [ite_true]
    ring
  have hGz : ∂[2] (fun p ↦ 2 * U p + 2 * p 1 * (∂[1] U) p) =
      fun p ↦ 2 * (∂[2] U) p + 2 * p 1 * (∂[2] (∂[1] U)) p := by
    funext p
    rw [hG]
    simp only [Fin.reduceEq, ite_false]
    ring
  have hmixed : ∂[2] (∂[2] (∂[1] U)) = ∂[1] (∂[2] (∂[2] U)) := by
    simp only [PDE.partialDeriv_partialDeriv_comm_of_contDiff 2 1 (hU.of_le (by simp)),
      PDE.partialDeriv_partialDeriv_comm_of_contDiff 2 1
        ((PDE.contDiff_top_partialDeriv hU (i := 2)).of_le (by simp))]
  unfold spacetimeSquaredRadiusLaplacian
  rw [hGs, hGz, partialDeriv_mul_add_coord_mul (hd hU 1) (hd hA 1),
    partialDeriv_mul_add_coord_mul (hd hU 2) (hd hA 2),
    partialDeriv_spacetimeSquaredRadiusDiffusion hU, hmixed]
  simp only [spacetimeSquaredRadiusDiffusion, ite_true, Fin.reduceEq, ite_false]
  ring

/-- Axial component of the Cartesian vector Laplacian of independently
reconstructed axisymmetric vorticity. -/
theorem spatialVectorLaplacian_vorticityFromCoefficients_apply_two
    {U Ω : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.spatialVectorLaplacian 3
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
        (timeSpaceCons t x) 2 =
      2 * spacetimeSquaredRadiusDiffusion U
          (timeSpaceCons t (squaredCylindricalMap x)) +
        2 * cylindricalRadiusSq x * (∂[(1 : Fin 3)]
          (spacetimeSquaredRadiusDiffusion U))
          (timeSpaceCons t (squaredCylindricalMap x)) := by
  let G : SpaceTime 2 → ℝ := fun q ↦ 2 * U q + 2 * q 1 * (∂[(1 : Fin 3)] U) q
  have hG : ContDiff ℝ (⊤ : ℕ∞) G :=
    (contDiff_const.mul hU).add ((contDiff_const.mul (contDiff_euclidean.1 contDiff_id 1)).mul
      (PDE.contDiff_top_partialDeriv hU))
  have hq (s : ℝ) (y : ℝ^3) :
      timeSpaceCons s (squaredCylindricalMap y) 1 = cylindricalRadiusSq y :=
    squaredCylindricalMap_apply_zero y
  have hcomponent :
      (fun xt ↦ spacetimeAxisymmetricVorticityFromCoefficients U Ω xt 2) =
        spacetimeSquaredCylindricalLift G := by
    funext xt
    rw [← timeSpaceCons_spatialPart xt,
      spacetimeAxisymmetricVorticityFromCoefficients_timeSpaceCons_apply_two]
    unfold spacetimeSquaredCylindricalLift
    rw [spacetimeSquaredCylindricalMap_timeSpaceCons]
    simp only [G, hq]
  rw [IncompressibleFlow.spatialVectorLaplacian_apply, hcomponent,
    spatialLaplacian_spacetimeSquaredCylindricalLift_eq hG,
    spacetimeSquaredRadiusLaplacian_axialReconstruction hU, hq]

/-- The Cartesian vector Laplacian preserves the regular axisymmetric
vorticity reconstruction and applies the swirl diffusion operator to both
reduced coefficients. -/
theorem spatialVectorLaplacian_vorticityFromCoefficients
    {U Ω : SpaceTime 2 → ℝ}
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hΩ : ContDiff ℝ (⊤ : ℕ∞) Ω)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.spatialVectorLaplacian 3
        (spacetimeAxisymmetricVorticityFromCoefficients U Ω)
        (timeSpaceCons t x) =
      spacetimeAxisymmetricVorticityFromCoefficients
        (spacetimeSquaredRadiusDiffusion U)
        (spacetimeSquaredRadiusDiffusion Ω)
        (timeSpaceCons t x) := by
  ext i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · rw [spatialVectorLaplacian_vorticityFromCoefficients_apply_zero hU hΩ,
      spacetimeSquaredRadiusDiffusion_partialDeriv_two hU]
    simp only [spacetimeAxisymmetricVorticityFromCoefficients_timeSpaceCons_apply_zero,
      spacetimeSquaredCylindricalLift_timeSpaceCons, squaredCylindricalLift, profileSlice_apply]
  · rw [spatialVectorLaplacian_vorticityFromCoefficients_apply_one hU hΩ,
      spacetimeSquaredRadiusDiffusion_partialDeriv_two hU]
    simp only [spacetimeAxisymmetricVorticityFromCoefficients_timeSpaceCons_apply_one,
      spacetimeSquaredCylindricalLift_timeSpaceCons, squaredCylindricalLift, profileSlice_apply]
  · rw [spatialVectorLaplacian_vorticityFromCoefficients_apply_two (U := U) (Ω := Ω) hU]
    simp only [spacetimeAxisymmetricVorticityFromCoefficients_timeSpaceCons_apply_two,
      spacetimeSquaredCylindricalLift_timeSpaceCons, squaredCylindricalLift, profileSlice_apply]

end

end AxisymmetricFlow
