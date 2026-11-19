/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.WeakSolutions
public import PDE.Fluid.NavierStokes.LocalEnergy.Pointwise
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Divergence form of the classical momentum and energy pairings

At a point where the velocity is `C²`, the pressure `C¹`, and the Navier–Stokes momentum
equation and incompressibility hold, two pairings are spatial divergences up to a time
derivative.

* The weak momentum integrand against a test `φ`, plus the time derivative of `u · φ`, is the
  spatial divergence of `weakMomentumFlux`, with components
  `ν ∑ᵢ ∂ⱼuᵢ φᵢ - ∑ᵢ uᵢ uⱼ φᵢ - p φⱼ`.
* The time derivative of `|u|²/2 · χ` for a scalar weight `χ`, corrected by the dissipation
  and by the terms carrying derivatives of `χ`, is the spatial divergence of
  `energyWeightFlux`, with components `(ν ∂ⱼ(|u|²/2) - (|u|²/2 + p) uⱼ) χ`, plus the force
  work.

Integrated over a time slice against compactly supported tests, the divergences vanish; this
gives the weak momentum equation and the energy equality of a classical solution.
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace IncompressibleFlow PDE

set_option linter.missingDocs true

/-- The coordinate algebra of the weak momentum pairing. If `Cᵢ + ∑ⱼ uⱼ Aᵢⱼ + Pᵢ` equals
`ν ∑ⱼ Lᵢⱼ + fᵢ` for every `i` and `∑ⱼ Aⱼⱼ = 0`, the pairing on the left equals the sum over `j`
of the expanded flux derivatives on the right. In the application `A` and `B` are the spatial
derivatives of `u` and `φ`, `C` and `D` their time derivatives, `L` the second spatial derivatives
of `u`, and `P` the pressure gradient. -/
private theorem weakMomentum_sum_identity {n : ℕ} (ν p : ℝ) (u φ C D P f : Fin n → ℝ)
    (A B L : Fin n → Fin n → ℝ)
    (hm : ∀ i, C i + ∑ j, u j * A i j + P i = ν * ∑ j, L i j + f i)
    (hdiv : ∑ j, A j j = 0) :
    -(∑ i, u i * D i) - (∑ i, ∑ j, u i * u j * B i j) + ν * (∑ i, ∑ j, A i j * B i j) -
        (∑ i, p * B i i) - (∑ i, f i * φ i) + ∑ i, (C i * φ i + u i * D i) =
      ∑ j, (∑ i, (ν * (L i j * φ i + A i j * B i j) -
        (A i j * u j * φ i + u i * A j j * φ i + u i * u j * B i j)) -
        (P j * φ j + p * B j j)) := by
  have key (i : Fin n) : ∑ j, (ν * (L i j * φ i + A i j * B i j) -
        (A i j * u j * φ i + u i * A j j * φ i + u i * u j * B i j)) =
      ν * (∑ j, L i j) * φ i + ν * (∑ j, A i j * B i j) - (∑ j, u j * A i j) * φ i -
        u i * φ i * (∑ j, A j j) - ∑ j, u i * u j * B i j := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  calc _ = ∑ i, (ν * (∑ j, A i j * B i j) - (∑ j, u i * u j * B i j) - p * B i i -
          f i * φ i + C i * φ i) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
        ring
    _ = ∑ i, (∑ j, (ν * (L i j * φ i + A i j * B i j) -
          (A i j * u j * φ i + u i * A j j * φ i + u i * u j * B i j)) -
          (P i * φ i + p * B i i)) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [key i, hdiv]
        linear_combination φ i * hm i
    _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_comm]

/-- Spatial flux whose divergence is the weak momentum pairing plus `∂ₜ(u · φ)`. Component
`j` is `ν ∑ᵢ ∂ⱼuᵢ φᵢ - ∑ᵢ uᵢ uⱼ φᵢ - p φⱼ`. -/
noncomputable def weakMomentumFlux {n : ℕ} (nse : Problem n) (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (φ : ℝ^(n + 1) → ℝ^n) (j : Fin n) (z : ℝ^(n + 1)) : ℝ :=
  (nse.kinematicViscosity : ℝ) * ∑ i : Fin n, (∂[j.succ] (fun y ↦ u y i)) z * φ z i -
    ∑ i : Fin n, u z i * u z j * φ z i - p z * φ z j

/-- The weak momentum flux vanishes where the test vanishes. -/
theorem weakMomentumFlux_eq_zero {n : ℕ} {nse : Problem n} {u : ℝ^(n + 1) → ℝ^n}
    {p : ℝ^(n + 1) → ℝ} {φ : ℝ^(n + 1) → ℝ^n} (j : Fin n) {z : ℝ^(n + 1)} (hz : φ z = 0) :
    weakMomentumFlux nse u p φ j z = 0 := by
  simp [weakMomentumFlux, hz]

/-- At a classical point, the weak momentum integrand with the classical gradient plus the
time derivative of `u · φ` is the spatial divergence of `weakMomentumFlux`. -/
theorem weakMomentumIntegrand_add_partialDeriv_inner_eq_sum {n : ℕ} {nse : Problem n}
    {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} {φ : ℝ^(n + 1) → ℝ^n} {t : ℝ} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons t x))
    (hp : DifferentiableAt ℝ p (PDE.Common.timeSpaceCons t x))
    (hφ : ContDiffAt ℝ 1 φ (PDE.Common.timeSpaceCons t x))
    (hdiv : DivergenceFreeAt u (PDE.Common.timeSpaceCons t x))
    (hmom : MomentumEquationAt nse u p (PDE.Common.timeSpaceCons t x)) :
    weakMomentumIntegrand nse u p (spatialVelocityGradient n u) φ t x +
        (∂[0] (fun z ↦ inner ℝ (u z) (φ z))) (PDE.Common.timeSpaceCons t x) =
      ∑ j : Fin n, (∂[j.succ] (weakMomentumFlux nse u p φ j)) (PDE.Common.timeSpaceCons t x) := by
  rw [weakMomentumIntegrand_eq_sum nse u p (spatialVelocityGradient n u) φ t x]
  simp only [spatialVelocityGradient_apply]
  generalize PDE.Common.timeSpaceCons t x = z at hu hp hφ hdiv hmom ⊢
  have hui (i : Fin n) : ContDiffAt ℝ 2 (fun y ↦ u y i) z := (contDiffAt_piLp 2).mp hu i
  have hud (i : Fin n) : DifferentiableAt ℝ (fun y ↦ u y i) z :=
    (hui i).differentiableAt (by norm_num)
  have hDud (i j : Fin n) : DifferentiableAt ℝ (∂[j.succ] (fun y ↦ u y i)) z :=
    ((hui i).partialDeriv j.succ (k := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφd (i : Fin n) : DifferentiableAt ℝ (fun y ↦ φ y i) z :=
    ((contDiffAt_piLp 2).mp hφ i).differentiableAt one_ne_zero
  have htime : (∂[0] (fun y ↦ inner ℝ (u y) (φ y))) z =
      ∑ i : Fin n, ((∂[0] (fun y ↦ u y i)) z * φ z i + u z i * (∂[0] (fun y ↦ φ y i)) z) := by
    have h : (fun y ↦ inner ℝ (u y) (φ y)) = fun y ↦ ∑ i : Fin n, u y i * φ y i := by
      funext y
      simp [PiLp.inner_apply, mul_comm]
    rw [h, partialDeriv_sum _ (fun i _ ↦ (hud i).fun_mul (hφd i))]
    exact Finset.sum_congr rfl fun i _ ↦ partialDeriv_mul (hud i) (hφd i)
  have hflux (j : Fin n) : (∂[j.succ] (weakMomentumFlux nse u p φ j)) z =
      ∑ i : Fin n, ((nse.kinematicViscosity : ℝ) *
          ((∂[j.succ] (∂[j.succ] (fun y ↦ u y i))) z * φ z i +
            (∂[j.succ] (fun y ↦ u y i)) z * (∂[j.succ] (fun y ↦ φ y i)) z) -
        ((∂[j.succ] (fun y ↦ u y i)) z * u z j * φ z i +
          u z i * (∂[j.succ] (fun y ↦ u y j)) z * φ z i +
          u z i * u z j * (∂[j.succ] (fun y ↦ φ y i)) z)) -
      ((∂[j.succ] p) z * φ z j + p z * (∂[j.succ] (fun y ↦ φ y j)) z) := by
    have h1 (i : Fin n) : DifferentiableAt ℝ
        (fun y ↦ (∂[j.succ] (fun y ↦ u y i)) y * φ y i) z := (hDud i j).fun_mul (hφd i)
    have h2 (i : Fin n) : DifferentiableAt ℝ (fun y ↦ u y i * u y j * φ y i) z :=
      ((hud i).fun_mul (hud j)).fun_mul (hφd i)
    have hS1 : DifferentiableAt ℝ
        (fun y ↦ ∑ i : Fin n, (∂[j.succ] (fun y ↦ u y i)) y * φ y i) z :=
      DifferentiableAt.fun_sum fun i _ ↦ h1 i
    have hS2 : DifferentiableAt ℝ (fun y ↦ ∑ i : Fin n, u y i * u y j * φ y i) z :=
      DifferentiableAt.fun_sum fun i _ ↦ h2 i
    unfold weakMomentumFlux
    rw [partialDeriv_sub ((hS1.const_mul _).fun_sub hS2) (hp.fun_mul (hφd j)),
      partialDeriv_sub (hS1.const_mul _) hS2,
      partialDeriv_mul (differentiableAt_const _) hS1, partialDeriv_const, zero_mul, zero_add,
      partialDeriv_sum _ (fun i _ ↦ h1 i), partialDeriv_sum _ (fun i _ ↦ h2 i),
      partialDeriv_mul hp (hφd j), Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [partialDeriv_mul (hDud i j) (hφd i),
      partialDeriv_triple_product _ (hud i) (hud j) (hφd i)]
  have hmi (i : Fin n) := congrArg (fun v : ℝ^n ↦ v i) hmom
  simp only [PiLp.add_apply, materialDerivative_apply, spatialGradient_apply, viscousTerm_apply,
    spatialVectorLaplacian_apply, spatialLaplacian_apply] at hmi
  rw [htime, Finset.sum_congr rfl fun j _ ↦ hflux j]
  exact weakMomentum_sum_identity (nse.kinematicViscosity : ℝ) (p z) (fun i ↦ u z i)
    (fun i ↦ φ z i) (fun i ↦ (∂[0] (fun y ↦ u y i)) z) (fun i ↦ (∂[0] (fun y ↦ φ y i)) z)
    (fun i ↦ (∂[i.succ] p) z) (fun i ↦ nse.forcing z i)
    (fun i j ↦ (∂[j.succ] (fun y ↦ u y i)) z) (fun i j ↦ (∂[j.succ] (fun y ↦ φ y i)) z)
    (fun i j ↦ (∂[j.succ] (∂[j.succ] (fun y ↦ u y i))) z) hmi hdiv

/-- Spatial flux of the kinetic energy weighted by `χ`. Component `j` is
`(ν ∂ⱼ(|u|²/2) - (|u|²/2 + p) uⱼ) χ`. -/
noncomputable def energyWeightFlux {n : ℕ} (nse : Problem n) (u : ℝ^(n + 1) → ℝ^n)
    (p χ : ℝ^(n + 1) → ℝ) (j : Fin n) (z : ℝ^(n + 1)) : ℝ :=
  ((nse.kinematicViscosity : ℝ) * (∂[j.succ] (specificKineticEnergy u)) z -
    (specificKineticEnergy u z + p z) * u z j) * χ z

/-- At a classical point, the time derivative of the kinetic energy weighted by `χ`, corrected by
the weighted dissipation and the terms carrying spatial derivatives of `χ`, is the spatial
divergence of `energyWeightFlux` plus the weighted force work. -/
theorem partialDeriv_energy_mul_eq_sum {n : ℕ} {nse : Problem n}
    {u : ℝ^(n + 1) → ℝ^n} {p χ : ℝ^(n + 1) → ℝ} {z : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ 2 u z) (hp : ContDiffAt ℝ 1 p z) (hχ : DifferentiableAt ℝ χ z)
    (hdiv : DivergenceFreeAt u z) (hmom : MomentumEquationAt nse u p z) :
    (∂[0] (fun y ↦ specificKineticEnergy u y * χ y)) z -
        specificKineticEnergy u z * (∂[0] χ) z +
        (nse.kinematicViscosity : ℝ) * ‖spatialVelocityGradient n u z‖ ^ 2 * χ z +
        (nse.kinematicViscosity : ℝ) *
          ∑ j : Fin n, (∂[j.succ] (specificKineticEnergy u)) z * (∂[j.succ] χ) z -
        ∑ j : Fin n, (specificKineticEnergy u z + p z) * u z j * (∂[j.succ] χ) z =
      ∑ j : Fin n, (∂[j.succ] (energyWeightFlux nse u p χ j)) z +
        inner ℝ (nse.forcing z) (u z) * χ z := by
  have he : ContDiffAt ℝ 2 (specificKineticEnergy u) z := contDiffAt_const.mul (hu.norm_sq ℝ)
  have hed : DifferentiableAt ℝ (specificKineticEnergy u) z := he.differentiableAt (by norm_num)
  have hDed (j : Fin n) : DifferentiableAt ℝ (∂[j.succ] (specificKineticEnergy u)) z :=
    (he.partialDeriv j.succ (k := 1) (by norm_num)).differentiableAt (by norm_num)
  have hud (j : Fin n) : DifferentiableAt ℝ (fun y ↦ u y j) z :=
    ((contDiffAt_piLp 2).mp hu j).differentiableAt (by norm_num)
  have hpd : DifferentiableAt ℝ p z := hp.differentiableAt (by norm_num)
  have hF (j : Fin n) : DifferentiableAt ℝ
      (fun y ↦ (specificKineticEnergy u y + p y) * u y j) z :=
    (hed.fun_add hpd).fun_mul (hud j)
  have hbalance : (∂[0] (specificKineticEnergy u)) z - (nse.kinematicViscosity : ℝ) *
        (∑ j : Fin n, (∂[j.succ] (∂[j.succ] (specificKineticEnergy u))) z) +
        (nse.kinematicViscosity : ℝ) * ‖spatialVelocityGradient n u z‖ ^ 2 +
        (∑ j : Fin n, (∂[j.succ] (fun y ↦ (specificKineticEnergy u y + p y) * u y j)) z) =
      inner ℝ (nse.forcing z) (u z) := by
    have h := NavierStokes.local_energy_balance hu hpd hdiv hmom
    have hflux := spatialDivergence_pressureFlux_eq_pressurePower_add
      (fun y ↦ specificKineticEnergy u y + p y) u z (hed.fun_add hpd) hud
    change (∑ j : Fin n, (∂[j.succ] (fun y ↦ (specificKineticEnergy u y + p y) * u y j)) z) =
      bernoulliTransport u p z + (specificKineticEnergy u z + p z) * spatialDivergence n u z
      at hflux
    rw [show spatialDivergence n u z = 0 from hdiv, mul_zero, add_zero,
      bernoulliTransport_eq_kineticEnergyTransport_add_pressurePower u p z hud hpd,
      kineticEnergyTransport_eq_spatialDivergence_kineticEnergyFlux_of_divergenceFreeAt
        u z hud hdiv,
      pressurePower_eq_spatialDivergence_pressureFlux_of_divergenceFreeAt
        p u z hpd hud hdiv] at hflux
    rw [hflux]
    simpa only [spatialLaplacian, add_assoc] using h
  have hflux (j : Fin n) : (∂[j.succ] (energyWeightFlux nse u p χ j)) z =
      ((nse.kinematicViscosity : ℝ) * (∂[j.succ] (∂[j.succ] (specificKineticEnergy u))) z -
          (∂[j.succ] (fun y ↦ (specificKineticEnergy u y + p y) * u y j)) z) * χ z +
        ((nse.kinematicViscosity : ℝ) * (∂[j.succ] (specificKineticEnergy u)) z -
          (specificKineticEnergy u z + p z) * u z j) * (∂[j.succ] χ) z := by
    unfold energyWeightFlux
    rw [partialDeriv_mul (((hDed j).const_mul _).fun_sub (hF j)) hχ,
      partialDeriv_sub ((hDed j).const_mul _) (hF j),
      partialDeriv_mul (differentiableAt_const _) (hDed j), partialDeriv_const, zero_mul,
      zero_add]
  have hsum : ∑ j : Fin n, (∂[j.succ] (energyWeightFlux nse u p χ j)) z =
      ((nse.kinematicViscosity : ℝ) *
          (∑ j : Fin n, (∂[j.succ] (∂[j.succ] (specificKineticEnergy u))) z) -
          (∑ j : Fin n, (∂[j.succ] (fun y ↦ (specificKineticEnergy u y + p y) * u y j)) z)) *
          χ z +
        (nse.kinematicViscosity : ℝ) *
          ∑ j : Fin n, (∂[j.succ] (specificKineticEnergy u)) z * (∂[j.succ] χ) z -
        ∑ j : Fin n, (specificKineticEnergy u z + p z) * u z j * (∂[j.succ] χ) z := by
    rw [Finset.sum_congr rfl fun j _ ↦ hflux j]
    simp only [sub_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [partialDeriv_mul hed hχ, hsum]
  linear_combination χ z * hbalance

end NavierStokes
