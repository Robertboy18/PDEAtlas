/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Vorticity
import Mathlib.Analysis.Calculus.FDeriv.Mul
import PDE.FDeriv.Calculus

/-!
# Strain rate and Newtonian stress

Continuum-mechanics tensors for a velocity field on spacetime.

Spacetime is `ℝ^(n + 1)`, coordinate `0` is time, and coordinate `i.succ`
is the `i`-th spatial coordinate. The spatial velocity gradient splits as

```text
∇u = D(u) + Ω(u) / 2,
```

where `D(u)` is symmetric and `Ω(u)` is the antisymmetric vorticity tensor.
For pressure `p` and dynamic viscosity `μ`, the Newtonian Cauchy stress is

```text
σ = -p I + 2 μ D(u).
```

The main computation is the divergence of this stress. For a `C²` velocity,

```text
(div σ)ᵢ = -∂ᵢp + μ Δuᵢ + μ ∂ᵢ(div u),
```

and the last term drops out for a locally incompressible velocity. This is the
identity that turns the Cauchy momentum equation `Dₜu = div σ + f` into the
Navier–Stokes momentum equation; at unit density the dynamic viscosity `μ` is
also the kinematic viscosity.

## Main results

* `strainRateTensor`, `strainRateTensor_apply_swap`,
  `spatialVelocityGradient_eq_strainRateTensor_add_half_vorticityTensor`: the
  symmetric strain rate and the splitting of the velocity gradient.
* `strainRateTrace_eq_spatialDivergence`: the trace of `D(u)` is `div u`.
* `newtonianCauchyStress`, `newtonianCauchyStress_apply_swap`: the stress tensor and its
  symmetry.
* `newtonianCauchyStressDivergence_eq`,
  `newtonianCauchyStressDivergence_eq_of_eventually_divergenceFreeAt`: the vector
  divergence formula and its incompressible reduction to `-∇p + μ Δu`.
* `newtonianCauchyMomentumResidual`: the unit-density Cauchy momentum residual.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1, for the splitting of the velocity
  gradient into a symmetric deformation matrix and an antisymmetric rotation matrix given by the
  vorticity.
  <https://doi.org/10.1017/CBO9780511613203>
* A. J. Chorin and J. E. Marsden, *A Mathematical Introduction to Fluid Mechanics*, Texts in Applied
  Mathematics, Springer, 1993, Chapter 1 (The Equations of Motion), for the Newtonian stress and the
  derivation of the Navier–Stokes equations from the Cauchy momentum balance.
  <https://doi.org/10.1007/978-1-4612-0883-9>
-/

@[expose] public section

open PDE (partialDeriv spatialGradient)

namespace IncompressibleFlow

open EuclideanSpace
open scoped Topology

set_option linter.missingDocs true

noncomputable section

/-- Symmetric strain-rate tensor `D(u) = (∇u + (∇u)ᵀ) / 2`. -/
def strainRateTensor (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    SpatialMatrix n :=
  WithLp.toLp 2 fun ij ↦
    (spatialVelocityGradient n u x ij +
      spatialVelocityGradient n u x (ij.2, ij.1)) / 2

/-- Coordinate formula
`Dᵢⱼ(u) = (∂ⱼuᵢ + ∂ᵢuⱼ) / 2` for the strain-rate tensor. -/
@[simp]
theorem strainRateTensor_apply (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (i j : Fin n) :
    strainRateTensor n u x (i, j) =
      ((∂[j.succ] (fun y ↦ u y i)) x +
        (∂[i.succ] (fun y ↦ u y j)) x) / 2 := by
  simp [strainRateTensor, PiLp.toLp_apply]

/-- Trace of the strain-rate tensor. -/
def strainRateTrace (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ :=
  ∑ i : Fin n, strainRateTensor n u x (i, i)

/-- The strain-rate tensor is symmetric. -/
theorem strainRateTensor_apply_swap (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (i j : Fin n) :
    strainRateTensor n u x (j, i) =
      strainRateTensor n u x (i, j) := by
  simp only [strainRateTensor_apply, add_comm]

/-- The velocity gradient is the sum of strain rate and half the vorticity. -/
theorem spatialVelocityGradient_eq_strainRateTensor_add_half_vorticityTensor
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    spatialVelocityGradient n u x =
      strainRateTensor n u x + (1 / 2 : ℝ) • vorticityTensor n u x := by
  ext ⟨i, j⟩
  simp only [strainRateTensor_apply, vorticityTensor_apply,
    spatialVelocityGradient_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The trace of the strain-rate tensor is the spatial divergence. -/
theorem strainRateTrace_eq_spatialDivergence
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    strainRateTrace n u x = spatialDivergence n u x := by
  unfold strainRateTrace
  rw [spatialDivergence_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [strainRateTensor_apply]
  ring

/-- Incompressibility makes the strain-rate tensor trace free. -/
theorem strainRateTrace_eq_zero_of_divergenceFreeAt
    (n : ℕ) (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hdiv : IncompressibleFlow.DivergenceFreeAt u x) :
    strainRateTrace n u x = 0 := by
  rw [strainRateTrace_eq_spatialDivergence]
  exact hdiv

/-- Newtonian Cauchy stress tensor `σ = -p I + 2 μ D(u)`. -/
def newtonianCauchyStress (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : SpatialMatrix n :=
  WithLp.toLp 2 fun ij ↦
    (if ij.1 = ij.2 then -p x else 0) +
      2 * dynamicViscosity * strainRateTensor n u x ij

/-- Coordinate formula for the Newtonian Cauchy stress. -/
@[simp]
theorem newtonianCauchyStress_apply (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (i j : Fin n) :
    newtonianCauchyStress n dynamicViscosity p u x (i, j) =
      (if i = j then -p x else 0) +
        2 * dynamicViscosity * strainRateTensor n u x (i, j) := by
  simp [newtonianCauchyStress, PiLp.toLp_apply]

/-- Newtonian Cauchy stress is symmetric. -/
theorem newtonianCauchyStress_apply_swap (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (i j : Fin n) :
    newtonianCauchyStress n dynamicViscosity p u x (j, i) =
      newtonianCauchyStress n dynamicViscosity p u x (i, j) := by
  simp only [newtonianCauchyStress_apply, eq_comm]
  rw [strainRateTensor_apply_swap]

/-- Spatial divergence of the Newtonian Cauchy stress. -/
def newtonianCauchyStressDivergence (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : ℝ^n :=
  spatialMatrixDivergence
    (newtonianCauchyStress n dynamicViscosity p u) x

/-- Component formula for the spatial divergence of the Newtonian stress. -/
@[simp]
theorem newtonianCauchyStressDivergence_apply (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (i : Fin n) :
    newtonianCauchyStressDivergence n dynamicViscosity p u x i =
      ∑ j : Fin n,
        (∂[j.succ]
          (fun y ↦ newtonianCauchyStress n dynamicViscosity p u y (i, j))) x := by
  simp [newtonianCauchyStressDivergence]

/--
The divergence of Newtonian stress consists of the pressure gradient,
componentwise viscosity, and the gradient of the velocity divergence:

```text
(div sigma)_i = -partial_i p + μ Delta u_i + μ partial_i(div u).
```

The `C²` hypothesis permits the mixed spatial derivatives to commute.
-/
theorem newtonianCauchyStressDivergence_apply_eq
    (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (i : Fin n)
    (hp : DifferentiableAt ℝ p x)
    (hu : ∀ k : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y k) x) :
    newtonianCauchyStressDivergence n dynamicViscosity p u x i =
      -(∂[i.succ] p) x +
        dynamicViscosity * spatialLaplacian n (fun y ↦ u y i) x +
        dynamicViscosity * (∂[i.succ]
          (spatialDivergence n u)) x := by
  classical
  have hfirst (k j : Fin n) : DifferentiableAt ℝ (fun y ↦ (∂[j.succ] (fun z ↦ u z k)) y) x :=
    (PDE.contDiffAt_partialDeriv (m := 1) (hu k) j.succ).differentiableAt (by norm_num)
  have hcomponent (j : Fin n) :
      (∂[j.succ] (fun y ↦ newtonianCauchyStress n dynamicViscosity p u y (i, j))) x =
        (if i = j then -(∂[j.succ] p) x else 0) +
          dynamicViscosity * ((∂[j.succ] (fun y ↦ (∂[j.succ] (fun z ↦ u z i)) y)) x +
            (∂[i.succ] (fun y ↦ (∂[j.succ] (fun z ↦ u z j)) y)) x) := by
    have hstress : (fun y ↦ newtonianCauchyStress n dynamicViscosity p u y (i, j)) =
        fun y ↦ (if i = j then -p y else 0) + dynamicViscosity •
          ((∂[j.succ] (fun z ↦ u z i)) y + (∂[i.succ] (fun z ↦ u z j)) y) := by
      funext y
      simp only [newtonianCauchyStress_apply, strainRateTensor_apply, smul_eq_mul]
      ring
    have hpressure : DifferentiableAt ℝ (fun y ↦ if i = j then -p y else 0) x := by
      by_cases hij : i = j <;> simp [hij, hp]
    rw [hstress,
      PDE.partialDeriv_add hpressure (((hfirst i j).fun_add (hfirst j i)).fun_const_smul _),
      PDE.partialDeriv_const_smul, PDE.partialDeriv_add (hfirst i j) (hfirst j i), smul_eq_mul,
      PDE.partialDeriv_partialDeriv_comm_at j.succ i.succ (hu j)]
    congr 1
    by_cases hij : i = j <;> simp [hij, PDE.partialDeriv_fun_neg]
  have hdiv : (∂[i.succ] (spatialDivergence n u)) x =
      ∑ j, (∂[i.succ] (fun y ↦ (∂[j.succ] (fun z ↦ u z j)) y)) x :=
    PDE.partialDeriv_sum Finset.univ (fun j _ ↦ hfirst j j) i.succ
  rw [newtonianCauchyStressDivergence_apply, spatialLaplacian_apply, hdiv]
  simp only [hcomponent, Finset.sum_add_distrib, mul_add, ← Finset.mul_sum, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  ring

/-- Vector formula for the divergence of Newtonian stress. -/
theorem newtonianCauchyStressDivergence_eq
    (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hp : DifferentiableAt ℝ p x)
    (hu : ∀ k : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y k) x) :
    newtonianCauchyStressDivergence n dynamicViscosity p u x =
      -spatialGradient p x +
        dynamicViscosity • spatialVectorLaplacian n u x +
        dynamicViscosity • spatialGradient (spatialDivergence n u) x := by
  ext i
  rw [newtonianCauchyStressDivergence_apply_eq n dynamicViscosity p u x i hp hu]
  simp only [PDE.spatialGradient_apply, spatialVectorLaplacian_apply, PiLp.neg_apply,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- If velocity is divergence-free near the evaluation point, Newtonian stress
divergence reduces to the pressure force plus dynamic viscosity times the
spatial vector Laplacian. -/
theorem newtonianCauchyStressDivergence_eq_of_eventually_divergenceFreeAt
    (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hp : DifferentiableAt ℝ p x)
    (hu : ∀ k : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y k) x)
    (hdiv : ∀ᶠ y in 𝓝 x, IncompressibleFlow.DivergenceFreeAt u y) :
    newtonianCauchyStressDivergence n dynamicViscosity p u x =
      -spatialGradient p x +
        dynamicViscosity • IncompressibleFlow.spatialVectorLaplacian n u x := by
  rw [newtonianCauchyStressDivergence_eq n dynamicViscosity p u x hp hu]
  have hdivFunction :
      spatialDivergence n u =ᶠ[𝓝 x] fun _ ↦ 0 := by
    filter_upwards [hdiv] with y hy
    exact hy
  have hgradient :
      spatialGradient (spatialDivergence n u) x = 0 := by
    ext i
    simp only [PDE.spatialGradient_apply, PiLp.zero_apply]
    rw [PDE.partialDeriv_congr_nhds i.succ hdivFunction]
    simp
  rw [hgradient, smul_zero, add_zero]

/-- For a globally divergence-free velocity, Newtonian stress divergence
reduces to the pressure force plus dynamic viscosity times the spatial vector
Laplacian. -/
theorem newtonianCauchyStressDivergence_eq_of_divergenceFree
    (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1))
    (hp : DifferentiableAt ℝ p x)
    (hu : ∀ k : Fin n, ContDiffAt ℝ 2 (fun y ↦ u y k) x)
    (hdiv : IncompressibleFlow.DivergenceFree u) :
    newtonianCauchyStressDivergence n dynamicViscosity p u x =
      -spatialGradient p x +
        dynamicViscosity • IncompressibleFlow.spatialVectorLaplacian n u x := by
  apply newtonianCauchyStressDivergence_eq_of_eventually_divergenceFreeAt
    n dynamicViscosity p u x hp hu
  exact Filter.Eventually.of_forall fun y ↦ hdiv.at y

/-- Unit-density Cauchy momentum residual
`Dₜu - div σ - f` for Newtonian stress. -/
def newtonianCauchyMomentumResidual (n : ℕ) (dynamicViscosity : ℝ)
    (p : ℝ^(n + 1) → ℝ) (u f : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : ℝ^n :=
  IncompressibleFlow.materialDerivative n u u x -
    newtonianCauchyStressDivergence n dynamicViscosity p u x -
    f x

end

end IncompressibleFlow
