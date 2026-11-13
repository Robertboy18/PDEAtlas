/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Axisymmetric.SpacetimeReconstruction
public import PDE.Fluid.Incompressible.VorticityEvolution
import PDE.FDeriv.SpaceTime
import CAS.ExactTactic

/-!
# Cartesian transport of squared-radius profiles

The Cartesian material derivative of a lifted scalar agrees with the reduced material
derivative `squaredRadiusMaterialDerivative` in `(t,s,z)` coordinates, with `s = r²`
(`scalarMaterialDerivative_spacetimeSquaredCylindricalLift`). The commutators
`squaredRadiusMaterialDerivative_partialDeriv_one` and `_two` move one `s` or `z` derivative
through the reduced material derivative. All identities hold on the symmetry axis as well as
away from it, under finite smoothness hypotheses. See `CartesianReconstruction` for the velocity
convention.
-/

@[expose] public section

open PDE (SpaceTime)

namespace AxisymmetricFlow

open EuclideanSpace
open PDE.Common
open PDE.CoordinateSystems

set_option linter.missingDocs true

noncomputable section

/-! ## Cartesian transport of squared-radius scalars -/

/-- Material derivative `∂_t - 2sΨ_z ∂_s + (2Ψ + 2sΨ_s) ∂_z` in `(t,s,z)` coordinates, induced
by the meridional velocity reconstructed from the streamfunction profile `Ψ`. The swirl does not
transport axisymmetric scalars. -/
def squaredRadiusMaterialDerivative
    (Ψ F : SpaceTime 2 → ℝ) (q : SpaceTime 2) : ℝ :=
  (∂[(0 : Fin 3)] F) q -
    2 * q 1 * (∂[(2 : Fin 3)] Ψ) q *
      (∂[(1 : Fin 3)] F) q +
    (2 * Ψ q + 2 * q 1 * (∂[(1 : Fin 3)] Ψ) q) *
      (∂[(2 : Fin 3)] F) q

/-- Time differentiation commutes with the squared-cylindrical spacetime
lift. -/
theorem partialDeriv_zero_spacetimeSquaredCylindricalLift
    {F : SpaceTime 2 → ℝ} (hF : ContDiff ℝ 1 F)
    (t : ℝ) (x : ℝ^3) :
    (∂[(0 : Fin 4)] (spacetimeSquaredCylindricalLift F))
        (timeSpaceCons t x) =
      (∂[(0 : Fin 3)] F)
        (timeSpaceCons t (squaredCylindricalMap x)) := by
  have hLift : DifferentiableAt ℝ (spacetimeSquaredCylindricalLift F)
      (timeSpaceCons t x) :=
    (contDiff_spacetimeSquaredCylindricalLift hF).differentiable
      one_ne_zero |>.differentiableAt
  have hFAt : DifferentiableAt ℝ F
      (timeSpaceCons t (squaredCylindricalMap x)) :=
    (hF.differentiable one_ne_zero).differentiableAt
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ x t hLift,
    PDE.partialDeriv_timeSpaceCons_eq_deriv F (squaredCylindricalMap x) t hFAt]
  congr 1

/-- A spatial derivative of the spacetime lift is the derivative of the lifted time slice. -/
private theorem partialDeriv_succ_spacetimeSquaredCylindricalLift
    {F : SpaceTime 2 → ℝ} (hF : ContDiff ℝ 1 F) (j : Fin 3) (t : ℝ) (x : ℝ^3) :
    (∂[j.succ] (spacetimeSquaredCylindricalLift F)) (timeSpaceCons t x) =
      (∂[j] (squaredCylindricalLift (profileSlice F t))) x := by
  rw [← PDE.partialDeriv_timeSpaceCons_spatial j _ t x
    ((contDiff_spacetimeSquaredCylindricalLift hF).differentiable one_ne_zero).differentiableAt]
  rfl

/-- Differentiation in the first transverse Cartesian coordinate produces
the squared-radius chain-rule factor `2 x_1`. -/
theorem partialDeriv_one_spacetimeSquaredCylindricalLift
    {F : SpaceTime 2 → ℝ} (hF : ContDiff ℝ 1 F)
    (t : ℝ) (x : ℝ^3) :
    (∂[(Fin.succ (0 : Fin 3))] (spacetimeSquaredCylindricalLift F))
        (timeSpaceCons t x) =
      2 * x 0 * (∂[(1 : Fin 3)] F)
        (timeSpaceCons t (squaredCylindricalMap x)) := by
  rw [partialDeriv_succ_spacetimeSquaredCylindricalLift hF,
    partialDeriv_zero_squaredCylindricalLift (contDiff_profileSlice hF t),
    partialDeriv_profileSlice (hF.differentiable one_ne_zero) (0 : Fin 2)]
  rfl

/-- Differentiation in the second transverse Cartesian coordinate produces
the squared-radius chain-rule factor `2 x_2`. -/
theorem partialDeriv_two_spacetimeSquaredCylindricalLift
    {F : SpaceTime 2 → ℝ} (hF : ContDiff ℝ 1 F)
    (t : ℝ) (x : ℝ^3) :
    (∂[(Fin.succ (1 : Fin 3))] (spacetimeSquaredCylindricalLift F))
        (timeSpaceCons t x) =
      2 * x 1 * (∂[(1 : Fin 3)] F)
        (timeSpaceCons t (squaredCylindricalMap x)) := by
  rw [partialDeriv_succ_spacetimeSquaredCylindricalLift hF,
    partialDeriv_one_squaredCylindricalLift (contDiff_profileSlice hF t),
    partialDeriv_profileSlice (hF.differentiable one_ne_zero) (0 : Fin 2)]
  rfl

/-- Axial differentiation commutes with the squared-cylindrical spacetime
lift. -/
theorem partialDeriv_three_spacetimeSquaredCylindricalLift
    {F : SpaceTime 2 → ℝ} (hF : ContDiff ℝ 1 F)
    (t : ℝ) (x : ℝ^3) :
    (∂[(Fin.succ (2 : Fin 3))] (spacetimeSquaredCylindricalLift F))
        (timeSpaceCons t x) =
      (∂[(2 : Fin 3)] F)
        (timeSpaceCons t (squaredCylindricalMap x)) := by
  rw [partialDeriv_succ_spacetimeSquaredCylindricalLift hF,
    partialDeriv_two_squaredCylindricalLift (contDiff_profileSlice hF t),
    partialDeriv_profileSlice (hF.differentiable one_ne_zero) (1 : Fin 2)]
  rfl

/-- The Cartesian material derivative of a squared-radius scalar is exactly
the induced `(t,s,z)` material derivative. The reconstructed swirl velocity
drops out because the scalar is axisymmetric. -/
theorem scalarMaterialDerivative_spacetimeSquaredCylindricalLift
    {U Ψ F : SpaceTime 2 → ℝ}
    (hΨ : ContDiff ℝ 2 Ψ) (hF : ContDiff ℝ 1 F)
    (t : ℝ) (x : ℝ^3) :
    IncompressibleFlow.scalarMaterialDerivative 3
        (spacetimeAxisymmetricVelocity U Ψ)
        (spacetimeSquaredCylindricalLift F) (timeSpaceCons t x) =
      squaredRadiusMaterialDerivative Ψ F
        (timeSpaceCons t (squaredCylindricalMap x)) := by
  rw [IncompressibleFlow.scalarMaterialDerivative_apply]
  simp only [Fin.sum_univ_three]
  rw [partialDeriv_zero_spacetimeSquaredCylindricalLift hF,
    partialDeriv_one_spacetimeSquaredCylindricalLift hF,
    partialDeriv_two_spacetimeSquaredCylindricalLift hF,
    partialDeriv_three_spacetimeSquaredCylindricalLift hF,
    spacetimeAxisymmetricVelocity_timeSpaceCons_apply_zero,
    spacetimeAxisymmetricVelocity_timeSpaceCons_apply_one,
    spacetimeAxisymmetricVelocity_timeSpaceCons_apply_two,
    partialDeriv_profileSlice_eq
    (hΨ.differentiable (by norm_num)) (1 : Fin 2),
    partialDeriv_profileSlice_eq
    (hΨ.differentiable (by norm_num)) (0 : Fin 2)]
  simp only [squaredCylindricalLift, profileSlice_apply]
  unfold squaredRadiusMaterialDerivative
  have hsqCoordinate :
      timeSpaceCons t (squaredCylindricalMap x) (1 : Fin 3) =
        PDE.CoordinateSystems.cylindricalRadiusSq x := by
    change squaredCylindricalMap x (0 : Fin 2) = _
    exact squaredCylindricalMap_apply_zero x
  rw [hsqCoordinate, show PDE.CoordinateSystems.cylindricalRadiusSq x = x 0 ^ 2 + x 1 ^ 2 from rfl,
    show Fin.succ (0 : Fin 2) = (1 : Fin 3) from rfl,
    show Fin.succ (1 : Fin 2) = (2 : Fin 3) from rfl]
  ring

/-! ## Commutators of the reduced material derivative -/

/-- The derivative of the reduced material derivative in the direction `i`, by the product rule. -/
private theorem partialDeriv_squaredRadiusMaterialDerivative {Ψ F : SpaceTime 2 → ℝ}
    (hΨ : ContDiff ℝ 2 Ψ) (hF : ContDiff ℝ 2 F) (i : Fin 3) (q : SpaceTime 2) :
    (∂[i] (squaredRadiusMaterialDerivative Ψ F)) q =
      (∂[i] (∂[0] F)) q -
        ((2 * (if i = 1 then 1 else 0) * (∂[2] Ψ) q + 2 * q 1 * (∂[i] (∂[2] Ψ)) q) *
            (∂[1] F) q + 2 * q 1 * (∂[2] Ψ) q * (∂[i] (∂[1] F)) q) +
        ((2 * (∂[i] Ψ) q + (2 * (if i = 1 then 1 else 0) * (∂[1] Ψ) q +
            2 * q 1 * (∂[i] (∂[1] Ψ)) q)) * (∂[2] F) q +
          (2 * Ψ q + 2 * q 1 * (∂[1] Ψ) q) * (∂[i] (∂[2] F)) q) := by
  have hd {f : SpaceTime 2 → ℝ} (hf : ContDiff ℝ 1 f) : DifferentiableAt ℝ f q :=
    (hf.differentiable one_ne_zero).differentiableAt
  have hc : ContDiff ℝ 1 fun p : SpaceTime 2 ↦ 2 * p 1 := by cas
  have hΨ1 (j : Fin 3) : ContDiff ℝ 1 (∂[j] Ψ) := PDE.contDiff_partialDeriv_of_succ hΨ
  have hF1 (j : Fin 3) : ContDiff ℝ 1 (∂[j] F) := PDE.contDiff_partialDeriv_of_succ hF
  have hΨ2 : ContDiff ℝ 1 fun p ↦ 2 * Ψ p := contDiff_const.mul (hΨ.of_le (by norm_num))
  have hA := hc.mul (hΨ1 2)
  have hB := hΨ2.add (hc.mul (hΨ1 1))
  have h2c : (∂[i] (fun p : SpaceTime 2 ↦ 2 * p 1)) q = 2 * if i = 1 then 1 else 0 := by
    simpa [smul_eq_mul, PDE.partialDeriv_coord] using
      PDE.partialDeriv_const_smul (n := 3) 2 (i := i) (f := fun p : SpaceTime 2 ↦ p 1) (x := q)
  have h2Ψ : (∂[i] (fun p ↦ 2 * Ψ p)) q = 2 * (∂[i] Ψ) q := by
    simpa [smul_eq_mul] using PDE.partialDeriv_const_smul (n := 3) 2 (i := i) (f := Ψ) (x := q)
  unfold squaredRadiusMaterialDerivative
  rw [PDE.partialDeriv_add (hd ((hF1 0).sub (hA.mul (hF1 1)))) (hd (hB.mul (hF1 2))),
    PDE.partialDeriv_sub (hd (hF1 0)) (hd (hA.mul (hF1 1))),
    PDE.partialDeriv_mul (hd hA) (hd (hF1 1)), PDE.partialDeriv_mul (hd hB) (hd (hF1 2)),
    PDE.partialDeriv_mul (hd hc) (hd (hΨ1 2)), PDE.partialDeriv_add (hd hΨ2) (hd (hc.mul (hΨ1 1))),
    PDE.partialDeriv_mul (hd hc) (hd (hΨ1 1)), h2c, h2Ψ]

/-- Commuting one axial derivative through the squared-radius material
derivative produces derivatives of the meridional velocity coefficients. -/
theorem squaredRadiusMaterialDerivative_partialDeriv_two
    {Ψ F : SpaceTime 2 → ℝ} (hΨ : ContDiff ℝ 2 Ψ)
    (hF : ContDiff ℝ 2 F) (q : SpaceTime 2) :
    squaredRadiusMaterialDerivative Ψ (∂[(2 : Fin 3)] F) q =
      (∂[(2 : Fin 3)]
          (squaredRadiusMaterialDerivative Ψ F)) q +
        2 * q 1 *
            (∂[(2 : Fin 3)] (∂[(2 : Fin 3)] Ψ)) q *
            (∂[(1 : Fin 3)] F) q -
        (2 * (∂[(2 : Fin 3)] Ψ) q +
            2 * q 1 *
              (∂[(2 : Fin 3)] (∂[(1 : Fin 3)] Ψ)) q) *
          (∂[(2 : Fin 3)] F) q := by
  rw [partialDeriv_squaredRadiusMaterialDerivative hΨ hF,
    PDE.partialDeriv_partialDeriv_comm (2 : Fin 3) (0 : Fin 3) hF q,
    PDE.partialDeriv_partialDeriv_comm (2 : Fin 3) (1 : Fin 3) hF q]
  simp only [squaredRadiusMaterialDerivative, Fin.reduceEq, ite_false]
  ring

/-- Commuting one squared-radius derivative through the reduced material
derivative produces derivatives of the meridional velocity coefficients. -/
theorem squaredRadiusMaterialDerivative_partialDeriv_one
    {Ψ F : SpaceTime 2 → ℝ} (hΨ : ContDiff ℝ 2 Ψ)
    (hF : ContDiff ℝ 2 F) (q : SpaceTime 2) :
    squaredRadiusMaterialDerivative Ψ (∂[(1 : Fin 3)] F) q =
      (∂[(1 : Fin 3)]
          (squaredRadiusMaterialDerivative Ψ F)) q +
        (2 * (∂[(2 : Fin 3)] Ψ) q +
            2 * q 1 *
              (∂[(1 : Fin 3)] (∂[(2 : Fin 3)] Ψ)) q) *
          (∂[(1 : Fin 3)] F) q -
        (4 * (∂[(1 : Fin 3)] Ψ) q +
            2 * q 1 *
              (∂[(1 : Fin 3)] (∂[(1 : Fin 3)] Ψ)) q) *
          (∂[(2 : Fin 3)] F) q := by
  rw [partialDeriv_squaredRadiusMaterialDerivative hΨ hF,
    PDE.partialDeriv_partialDeriv_comm (1 : Fin 3) (0 : Fin 3) hF q,
    PDE.partialDeriv_partialDeriv_comm (1 : Fin 3) (2 : Fin 3) hF q]
  simp only [squaredRadiusMaterialDerivative, ite_true]
  ring
end

end AxisymmetricFlow
