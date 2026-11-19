/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime.Gradient.Regularity
public import PDE.Fluid.Euler.GlobalSolutions
public import PDE.Fluid.Incompressible.EnergyIdentities
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Time-dependent potential Euler flow

For a velocity potential `v` and force potential `h`, set `u = ∇ₓv` and
`p = h - v_t - |u|²/2`. Commutation of mixed derivatives and the irrotational
convective-acceleration identity give the Euler momentum equation. Incompressibility
is exactly spatial harmonicity of `v`.

The pointwise identities need only `C²` velocity potential and differentiable force
potential. Finite regularity on open sets and a global smooth solution construction
supply classical meaning to the operators. The initial data constructor derives
distributional incompressibility from harmonicity at time zero.

This is the potential-function reduction of Evans (§4.4.2), with Bernoulli's law giving the
pressure. A harmonic potential with the prescribed initial gradient is an input of
`Euler.potentialGlobalSmoothSolution`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.4.2, equations (11)-(16), p. 208.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE EuclideanSpace

namespace IncompressibleFlow

set_option linter.missingDocs true

/-- Time differentiation commutes with the spatial gradient of a `C²` potential. -/
theorem timeDerivative_spatialGradient {n : ℕ} {v : ℝ^(n + 1) → ℝ}
    {x : ℝ^(n + 1)} (hv : ContDiffAt ℝ 2 v x) :
    timeDerivative n (spatialGradient v) x = spatialGradient (∂[0] v) x := by
  ext i
  simp only [timeDerivative_apply, spatialGradient_apply]
  exact partialDeriv_partialDeriv_comm_at 0 i.succ hv

/-- A `C²` velocity potential generates an irrotational velocity field. -/
theorem vorticityTensor_spatialGradient {n : ℕ} {v : ℝ^(n + 1) → ℝ}
    {x : ℝ^(n + 1)} (hv : ContDiffAt ℝ 2 v x) :
    vorticityTensor n (spatialGradient v) x = 0 := by
  ext ⟨i, j⟩
  simp only [vorticityTensor_apply, spatialGradient_apply, PiLp.zero_apply]
  exact sub_eq_zero.mpr (partialDeriv_partialDeriv_comm_at j.succ i.succ hv)

/-- Each spatial-gradient component of a `C²` potential is differentiable. -/
private theorem differentiableAt_spatialGradient_apply {n : ℕ} {v : ℝ^(n + 1) → ℝ}
    {x : ℝ^(n + 1)} (hv : ContDiffAt ℝ 2 v x) (i : Fin n) :
    DifferentiableAt ℝ (fun y ↦ spatialGradient v y i) x := by
  simpa only [spatialGradient_apply] using
    (contDiffAt_partialDeriv 1 hv i.succ).differentiableAt (by norm_num)

/-- For potential velocity and force, the Euler momentum residual is the spatial gradient
of the unsteady Bernoulli expression `v_t + |∇ₓv|²/2 + p - h`. -/
theorem eulerMomentumResidual_spatialGradient {n : ℕ} {v p h : ℝ^(n + 1) → ℝ}
    {x : ℝ^(n + 1)} (hv : ContDiffAt ℝ 2 v x)
    (hp : DifferentiableAt ℝ p x) (hh : DifferentiableAt ℝ h x) :
    eulerMomentumResidual n (spatialGradient v) p (spatialGradient h) x =
      spatialGradient (fun y ↦ (∂[0] v) y +
        specificKineticEnergy (spatialGradient v) y + p y - h y) x := by
  have hu := differentiableAt_spatialGradient_apply hv
  have ht := (contDiffAt_partialDeriv 1 hv 0).differentiableAt (by norm_num)
  have hk := differentiableAt_specificKineticEnergy (spatialGradient v) x hu
  rw [eulerMomentumResidual,
    materialDerivative_eq_timeDerivative_add_convectiveDerivative,
    timeDerivative_spatialGradient hv,
    convectiveDerivative_eq_spatialGradient_specificKineticEnergy_of_vorticityTensor_eq_zero
      _ _ hu (vorticityTensor_spatialGradient hv)]
  ext i
  simp only [spatialGradient_apply, PiLp.add_apply, PiLp.sub_apply]
  rw [partialDeriv_sub ((ht.fun_add hk).fun_add hp) hh,
    partialDeriv_add (ht.fun_add hk) hp, partialDeriv_add ht hk]

/-- Pressure recovered from a velocity potential `v` and force potential `h`:
`p = h - v_t - |∇ₓv|²/2`. -/
noncomputable def potentialPressure {n : ℕ} (v h : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) : ℝ :=
  h x - (∂[0] v) x - specificKineticEnergy (spatialGradient v) x

/-- Bernoulli pressure makes the potential velocity satisfy the Euler momentum equation.
Spatial harmonicity is needed separately for incompressibility. -/
theorem eulerMomentumResidual_potentialPressure {n : ℕ} {v h : ℝ^(n + 1) → ℝ}
    {x : ℝ^(n + 1)} (hv : ContDiffAt ℝ 2 v x) (hh : DifferentiableAt ℝ h x) :
    eulerMomentumResidual n (spatialGradient v) (potentialPressure v h)
      (spatialGradient h) x = 0 := by
  have ht := (contDiffAt_partialDeriv 1 hv 0).differentiableAt (by norm_num)
  have hk := differentiableAt_specificKineticEnergy (spatialGradient v) x
    (differentiableAt_spatialGradient_apply hv)
  have hp : DifferentiableAt ℝ (potentialPressure v h) x :=
    (hh.fun_sub ht).fun_sub hk
  rw [eulerMomentumResidual_spatialGradient hv hp hh]
  have heq : (fun y ↦ (∂[0] v) y + specificKineticEnergy (spatialGradient v) y +
      potentialPressure v h y - h y) = fun _ ↦ 0 := by
    funext y
    simp only [potentialPressure]
    abel
  rw [heq]
  ext i
  simp [spatialGradient_apply, partialDeriv]

/-- Bernoulli pressure loses one finite local differentiability order from the
velocity potential. -/
theorem contDiffAt_potentialPressure {n m : ℕ} {v h : ℝ^(n + 1) → ℝ}
    {x : ℝ^(n + 1)} (hv : ContDiffAt ℝ (m + 1) v x) (hh : ContDiffAt ℝ m h x) :
    ContDiffAt ℝ m (potentialPressure v h) x := by
  exact (hh.sub (contDiffAt_partialDeriv m hv 0)).sub
    (contDiffAt_const.mul ((contDiffAt_spatialGradient hv).norm_sq ℝ))

/-- The potential velocity is incompressible exactly where its spatial Laplacian vanishes.
This operator identity is total; classical applications also supply `C²` regularity. -/
theorem divergenceFreeAt_spatialGradient_iff {n : ℕ} (v : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) :
    DivergenceFreeAt (spatialGradient v) x ↔ spatialLaplacian n v x = 0 := by
  rw [DivergenceFreeAt, spatialDivergence_spatialGradient_eq_spatialLaplacian]

/-- On an open spacetime region, Bernoulli pressure is `C^m` when the velocity potential is
`C^(m+1)` and the force potential is `C^m`. -/
theorem contDiffOn_potentialPressure {n m : ℕ} {v h : ℝ^(n + 1) → ℝ}
    {Ω : Set (ℝ^(n + 1))} (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ (m + 1) v Ω)
    (hh : ContDiffOn ℝ m h Ω) : ContDiffOn ℝ m (potentialPressure v h) Ω := by
  exact hΩ.contDiffOn_iff.mpr fun _ hx ↦
    contDiffAt_potentialPressure (hv.contDiffAt (hΩ.mem_nhds hx))
      (hh.contDiffAt (hΩ.mem_nhds hx))

/-- Smooth velocity and force potentials give smooth Bernoulli pressure. -/
theorem contDiff_top_potentialPressure {n : ℕ} {v h : ℝ^(n + 1) → ℝ}
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (potentialPressure v h) := by
  exact (hh.sub (contDiff_top_partialDeriv hv)).sub
    (contDiff_const.mul ((contDiff_top_spatialGradient hv).norm_sq ℝ))

/-- Spatial harmonicity at time zero makes the initial potential velocity distributionally
incompressible. The `C²` hypothesis supplies the classical-to-distributional bridge. -/
theorem distributionallyDivergenceFree_initial_spatialGradient {n : ℕ}
    {v : ℝ^(n + 1) → ℝ} (hv : ContDiff ℝ 2 v)
    (hharmonic : ∀ x : ℝ^n, spatialLaplacian n v (PDE.Common.timeSpaceCons 0 x) = 0) :
    DistributionallyDivergenceFree
      (fun x ↦ spatialGradient v (PDE.Common.timeSpaceCons 0 x)) := by
  have hregular : ContDiff ℝ 1
      (fun x ↦ spatialGradient v (PDE.Common.timeSpaceCons 0 x)) :=
    (contDiff_spatialGradient_of_succ hv).comp
      (PDE.Common.contDiff_timeSpaceCons_spatial n 0)
  apply SpatialFieldDivergenceFree.distributionallyDivergenceFree ?_ hregular
  intro x
  simp only [spatialFieldDivergence_apply, spatialGradient_apply]
  calc
    _ = ∑ i : Fin n,
        (∂[i.succ] (∂[i.succ] v)) (PDE.Common.timeSpaceCons 0 x) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact partialDeriv_timeSpaceCons_spatial i (∂[i.succ] v) 0 x
        ((contDiff_partialDeriv_of_succ hv).differentiable (by norm_num)).differentiableAt
    _ = 0 := hharmonic x

end IncompressibleFlow

namespace Euler

open IncompressibleFlow

set_option linter.missingDocs true

/-- Euler data induced by velocity and force potentials. Initial distributional
incompressibility follows from harmonicity of the velocity potential at time zero. -/
noncomputable def potentialInitialValueData {n : ℕ}
    (v h : ℝ^(n + 1) → ℝ) (hv : ContDiff ℝ 2 v)
    (hharmonic : ∀ x : ℝ^n, spatialLaplacian n v (PDE.Common.timeSpaceCons 0 x) = 0) :
    InitialValueData n where
  forcing := spatialGradient h
  initialVelocity := fun x ↦ spatialGradient v (PDE.Common.timeSpaceCons 0 x)
  initialVelocity_distributionallyDivergenceFree :=
    distributionallyDivergenceFree_initial_spatialGradient hv hharmonic

/-- A smooth spatially harmonic velocity potential generates a global smooth Euler solution
with force `∇ₓh` and its prescribed initial gradient. The potential is an input. -/
noncomputable def potentialGlobalSmoothSolution {n : ℕ}
    (data : InitialValueData n) (v h : ℝ^(n + 1) → ℝ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hharmonic : ∀ x ∈ PDE.Common.positiveTimeDomain, spatialLaplacian n v x = 0)
    (hforcing : data.forcing = spatialGradient h)
    (hinitial : ∀ x : ℝ^n,
      spatialGradient v (PDE.Common.timeSpaceCons 0 x) = data.initialVelocity x) :
    GlobalSmoothSolution data where
  u := spatialGradient v
  p := potentialPressure v h
  momentum_at := by
    intro x _hx
    change materialDerivative n (spatialGradient v) (spatialGradient v) x +
      spatialGradient (potentialPressure v h) x = data.forcing x
    rw [hforcing]
    exact (eulerMomentumResidual_eq_zero_iff _ _ _ _ _).mp
      (eulerMomentumResidual_potentialPressure (hv.of_le (by norm_num)).contDiffAt
        (hh.differentiable (by simp)).differentiableAt)
  divergenceFreeOn := fun x hx ↦ (divergenceFreeAt_spatialGradient_iff v x).mpr
    (hharmonic x hx)
  initial_eq := hinitial
  velocity_contDiffOn := (contDiff_top_spatialGradient hv).contDiffOn
  pressure_contDiffOn := (contDiff_top_potentialPressure hv hh).contDiffOn
end Euler
