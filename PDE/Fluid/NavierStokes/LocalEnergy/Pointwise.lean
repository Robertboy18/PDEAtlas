/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Problem
public import PDE.Fluid.Incompressible.EnergyIdentities
import Mathlib.Analysis.InnerProductSpace.Calculus
import PDE.FDeriv.Calculus

/-!
# The classical local energy balance

Pairing the Navier–Stokes momentum equation with velocity gives the local
energy equality. The viscous term is the Laplacian of kinetic energy minus
the squared spatial gradient. All regularity hypotheses are local at the
evaluation point, so the result applies to solutions smooth only for positive
time. This pointwise result does not assert the integrability needed to pass
to the distributional suitable-solution interface.
-/

@[expose] public section

namespace IncompressibleFlow

open EuclideanSpace Filter PDE
open scoped Topology

set_option linter.missingDocs true

/-- A coordinate derivative of kinetic energy pairs velocity with its derivative. -/
theorem partialDeriv_specificKineticEnergy_inner {m n : ℕ}
    {u : ℝ^m → ℝ^n} {x : ℝ^m} (hu : DifferentiableAt ℝ u x) (j : Fin m) :
    (∂[j] (specificKineticEnergy u)) x = inner ℝ (u x) ((∂[j] u) x) := by
  have h := hu.hasFDerivAt.norm_sq.const_mul (1 / 2 : ℝ)
  change fderiv ℝ (fun y ↦ (1 / 2 : ℝ) * ‖u y‖ ^ 2) x
    (EuclideanSpace.single j 1) = _
  rw [h.fderiv]
  simp [partialDeriv]

/-- The diagonal second derivative of kinetic energy has its gradient-square term. -/
theorem secondPartialDeriv_specificKineticEnergy {m n : ℕ}
    {u : ℝ^m → ℝ^n} {x : ℝ^m} (hu : ContDiffAt ℝ 2 u x) (j : Fin m) :
    (∂[j] (∂[j] (specificKineticEnergy u))) x =
      inner ℝ (u x) ((∂[j] (∂[j] u)) x) + ‖(∂[j] u) x‖ ^ 2 := by
  have hdu := (hu.partialDeriv j (k := 1) (by norm_num)).differentiableAt
    (by norm_num)
  have hfirst : (∂[j] (specificKineticEnergy u)) =ᶠ[𝓝 x]
      fun y ↦ inner ℝ (u y) ((∂[j] u) y) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact partialDeriv_specificKineticEnergy_inner (hy.differentiableAt (by norm_num)) j
  rw [partialDeriv_congr_nhds j hfirst]
  change fderiv ℝ (fun y ↦ inner ℝ (u y) ((∂[j] u) y)) x
    (EuclideanSpace.single j 1) = _
  rw [fderiv_inner_apply ℝ (hu.differentiableAt (by norm_num)) hdu]
  simp [partialDeriv]

/-- The spatial vector Laplacian is the sum of vector-valued coordinate derivatives. -/
theorem spatialVectorLaplacian_eq_sum_secondPartialDeriv {n : ℕ}
    {u : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u x) :
    spatialVectorLaplacian n u x =
      ∑ j : Fin n, (∂[j.succ] (∂[j.succ] u)) x := by
  ext i
  simp only [spatialVectorLaplacian_apply, spatialLaplacian_apply,
    WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hfirst : (fun y ↦ (∂[j.succ] u) y i) =ᶠ[𝓝 x]
      ∂[j.succ] (fun y ↦ u y i) := by
    filter_upwards [hu.eventually (by norm_num)] with y hy
    exact partialDeriv_apply j.succ i (hy.differentiableAt (by norm_num))
  rw [partialDeriv_apply j.succ i
    ((hu.partialDeriv j.succ (k := 1) (by norm_num)).differentiableAt (by norm_num)),
    partialDeriv_congr_nhds j.succ hfirst]

/-- The sum of directional velocity squares is the squared full spatial-gradient norm. -/
theorem sum_norm_partialDeriv_sq_eq_spatialVelocityGradient {n : ℕ}
    {u : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)} (hu : DifferentiableAt ℝ u x) :
    (∑ j : Fin n, ‖(∂[j.succ] u) x‖ ^ 2) = ‖spatialVelocityGradient n u x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type,
    spatialVelocityGradient_apply, partialDeriv_apply _ _ hu]
  exact Finset.sum_comm

/-- Viscous power is the Laplacian of energy minus squared spatial gradients. -/
theorem spatialLaplacian_specificKineticEnergy {n : ℕ}
    {u : ℝ^(n + 1) → ℝ^n} {x : ℝ^(n + 1)} (hu : ContDiffAt ℝ 2 u x) :
    spatialLaplacian n (specificKineticEnergy u) x =
      inner ℝ (u x) (spatialVectorLaplacian n u x) +
        ‖spatialVelocityGradient n u x‖ ^ 2 := by
  simp only [spatialLaplacian_apply, secondPartialDeriv_specificKineticEnergy hu]
  rw [Finset.sum_add_distrib, ← inner_sum,
    ← spatialVectorLaplacian_eq_sum_secondPartialDeriv hu,
    sum_norm_partialDeriv_sq_eq_spatialVelocityGradient (hu.differentiableAt (by norm_num))]

end IncompressibleFlow

namespace NavierStokes

open EuclideanSpace IncompressibleFlow

set_option linter.missingDocs true

/-- The classical local energy equality for an incompressible Navier–Stokes field. -/
theorem local_energy_balance {n : ℕ} {nse : Problem n}
    {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} {x : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ 2 u x) (hp : DifferentiableAt ℝ p x)
    (hdiv : DivergenceFreeAt u x) (hmom : MomentumEquationAt nse u p x) :
    (∂[0] (specificKineticEnergy u)) x -
        nse.kinematicViscosity * spatialLaplacian n (specificKineticEnergy u) x +
        nse.kinematicViscosity * ‖spatialVelocityGradient n u x‖ ^ 2 +
        spatialDivergence n (kineticEnergyFlux u) x +
        spatialDivergence n (pressureFlux p u) x =
      inner ℝ (nse.forcing x) (u x) := by
  have hud := hu.differentiableAt (by norm_num)
  have huc (i : Fin n) : DifferentiableAt ℝ (fun y ↦ u y i) x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n ↦ ℝ) i).differentiableAt.comp x hud
  have htime : timeDerivative n u x = (∂[0] u) x := by
    ext i
    exact (PDE.partialDeriv_apply 0 i hud).symm
  have h := congrArg (fun v : ℝ^n ↦ inner ℝ (u x) v) hmom
  rw [materialDerivative_eq_timeDerivative_add_convectiveDerivative,
    inner_add_right, inner_add_right, inner_add_right, htime] at h
  change inner ℝ (u x) ((∂[0] u) x) + convectivePower u x + pressurePower p u x =
    inner ℝ (u x) ((nse.kinematicViscosity : ℝ) • spatialVectorLaplacian n u x) +
      inner ℝ (u x) (nse.forcing x) at h
  rw [inner_smul_right,
    convectivePower_eq_spatialDivergence_kineticEnergyFlux_of_divergenceFreeAt u x huc hdiv,
    pressurePower_eq_spatialDivergence_pressureFlux_of_divergenceFreeAt p u x hp huc hdiv] at h
  rw [partialDeriv_specificKineticEnergy_inner hud,
    spatialLaplacian_specificKineticEnergy hu, real_inner_comm (u x) (nse.forcing x)]
  linarith

/-- Every interior point of a smooth solution satisfies the local energy equality. -/
theorem SmoothSolution.local_energy_balance {n : ℕ} {nse : Problem n}
    (sol : SmoothSolution nse) {x : ℝ^(n + 1)}
    (hx : x ∈ finiteTimeDomain n sol.T) :
    (∂[0] (specificKineticEnergy sol.u)) x -
        nse.kinematicViscosity * spatialLaplacian n (specificKineticEnergy sol.u) x +
        nse.kinematicViscosity * ‖spatialVelocityGradient n sol.u x‖ ^ 2 +
        spatialDivergence n (kineticEnergyFlux sol.u) x +
        spatialDivergence n (pressureFlux sol.p sol.u) x =
      inner ℝ (nse.forcing x) (sol.u x) :=
  NavierStokes.local_energy_balance ((sol.velocity_contDiffAt hx).of_le (by norm_num))
    ((sol.pressure_contDiffAt hx).differentiableAt (by norm_num))
    (sol.incompressible_at hx) (sol.momentum_at hx)

end NavierStokes
