/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Vorticity
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Pointwise kinetic-energy identities

The kinetic-energy calculation for incompressible Euler and Navier–Stokes flow rests on a few
pointwise differential identities.

For a velocity field `u`, the power of the convective acceleration is the
transport of the specific kinetic energy:

```text
((u · ∇)u) · u = u · ∇(1 / 2 |u|²).
```

The componentwise decomposition

```text
((u · ∇)u)ᵢ = ∂ᵢ(1 / 2 |u|²) + ∑ⱼ uⱼ Ωᵢⱼ
```

also gives Bernoulli transport along steady Euler streamlines and the
pointwise Bernoulli identity for irrotational flow.

The pressure work decomposes into a divergence and a compressibility term:

```text
u · ∇p = div(pu) - p div u.
```

Consequently, for divergence-free flow both convection and pressure are
pointwise divergences. Turning these identities into vanishing spatial
integrals requires the separate boundary, decay, and integrability hypotheses
appropriate to the domain. The integrated balance `d/dt ∫ |u|²/2 = -ν ∫ |∇u|²`, and the
hypotheses under which the flux terms vanish, are treated by Majda and Bertozzi (Chapter 3) and
Temam (Chapter III).

All statements are pointwise and hold at a spacetime point under explicit differentiability of
the fields there. `Ω` denotes the vorticity tensor `∇u - (∇u)ᵀ` of `Vorticity`, and `n` is the
space dimension, with time in coordinate `0` of `ℝ^(n + 1)`.

## Main results

* `convectiveDerivative_eq_spatialGradient_specificKineticEnergy_add_vorticityContraction`: the
  Lamb-type decomposition `(u·∇)u = ∇(|u|²/2) + Ωu`.
* `convectivePower_eq_kineticEnergyTransport`: `((u·∇)u)·u = u·∇(|u|²/2)`.
* `bernoulliTransport_eq_zero_of_steady_unforced_euler`,
  `spatialGradient_bernoulliFunction_eq_zero_of_steady_irrotational_euler`: Bernoulli's theorem
  along streamlines of a steady Euler flow, and its pointwise form for irrotational flow.
* `convectivePower_eq_spatialDivergence_kineticEnergyFlux_of_divergenceFreeAt`,
  `pressurePower_eq_spatialDivergence_pressureFlux_of_divergenceFreeAt`: for divergence-free
  `u`, the convective and pressure powers are `div(|u|²u/2)` and `div(pu)`.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 3 (energy methods for the Euler and the
  Navier–Stokes equations).
  <https://doi.org/10.1017/CBO9780511613203>
* R. Temam, *Navier–Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing, 2001,
  Chapter III (the evolution Navier–Stokes equation).
  <https://doi.org/10.1090/chel/343>
-/

@[expose] public section

open PDE (partialDeriv spatialGradient)

namespace IncompressibleFlow

open EuclideanSpace

set_option linter.missingDocs true

noncomputable section

/-- Specific kinetic energy `|u x|² / 2` of a vector field at a point. -/
def specificKineticEnergy {n : ℕ} {X : Type*} (u : X → ℝ^n)
    (x : X) : ℝ :=
  (1 / 2 : ℝ) * ‖u x‖ ^ 2

/-- Coordinate formula for specific kinetic energy. -/
theorem specificKineticEnergy_eq_sum_sq {n : ℕ} {X : Type*}
    (u : X → ℝ^n) (x : X) :
    specificKineticEnergy u x =
      (1 / 2 : ℝ) * ∑ i : Fin n, (u x i) ^ 2 := by
  simp [specificKineticEnergy, EuclideanSpace.real_norm_sq_eq]

/-- Vector obtained by contracting the vorticity tensor with velocity:
`(Ωu)ᵢ = ∑ⱼ Ωᵢⱼuⱼ`. -/
def vorticityContraction (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ^n :=
  WithLp.toLp 2 fun i ↦
    ∑ j : Fin n, vorticityTensor n u x (i, j) * u x j

/-- Component formula for contraction of the vorticity tensor with velocity. -/
@[simp]
theorem vorticityContraction_apply (n : ℕ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) (i : Fin n) :
    vorticityContraction n u x i =
      ∑ j : Fin n, vorticityTensor n u x (i, j) * u x j := by
  simp [vorticityContraction, PiLp.toLp_apply]

/-- Bernoulli function `|u|² / 2 + p`. -/
def bernoulliFunction {n : ℕ} (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (x : ℝ^(n + 1)) : ℝ :=
  specificKineticEnergy u x + p x

/-- Spatial transport `u · ∇B` of the Bernoulli function. -/
def bernoulliTransport {n : ℕ} (u : ℝ^(n + 1) → ℝ^n)
    (p : ℝ^(n + 1) → ℝ) (x : ℝ^(n + 1)) : ℝ :=
  spatialScalarAdvection n u (bernoulliFunction u p) x

/-- Pointwise power supplied by the convective acceleration. -/
def convectivePower {n : ℕ} (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : ℝ :=
  inner ℝ (u x) (convectiveDerivative n u u x)

/-- Transport of specific kinetic energy by the velocity field. -/
def kineticEnergyTransport {n : ℕ} (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : ℝ :=
  spatialScalarAdvection n u (specificKineticEnergy u) x

/-- Convective energy flux `eu`, where `e = |u|² / 2`. -/
def kineticEnergyFlux {n : ℕ} (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : ℝ^n :=
  specificKineticEnergy u x • u x

/-- Pointwise pressure power `u · ∇p`. -/
def pressurePower {n : ℕ} (p : ℝ^(n + 1) → ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ :=
  spatialScalarAdvection n u p x

/-- Pressure energy flux `pu`. -/
def pressureFlux {n : ℕ} (p : ℝ^(n + 1) → ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ^n :=
  p x • u x

/-- Coordinate formula for transport of the Bernoulli function. -/
theorem bernoulliTransport_eq_sum {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1)) :
    bernoulliTransport u p x =
      ∑ j : Fin n,
        u x j * (∂[j.succ] (bernoulliFunction u p)) x :=
  spatialScalarAdvection_eq_sum n u (bernoulliFunction u p) x

/-- Coordinate formula for convective power. -/
theorem convectivePower_eq_sum {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    convectivePower u x =
      ∑ i : Fin n, convectiveDerivative n u u x i * u x i := by
  simp [convectivePower, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Coordinate formula for transport of specific kinetic energy. -/
theorem kineticEnergyTransport_eq_sum {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    kineticEnergyTransport u x =
      ∑ j : Fin n,
        u x j * (∂[j.succ] (specificKineticEnergy u)) x :=
  spatialScalarAdvection_eq_sum n u (specificKineticEnergy u) x

/-- Coordinate formula for pressure power. -/
theorem pressurePower_eq_sum {n : ℕ}
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) :
    pressurePower p u x =
      ∑ j : Fin n, u x j * (∂[j.succ] p) x :=
  spatialScalarAdvection_eq_sum n u p x

/-- Componentwise differentiability of velocity implies differentiability
of its specific kinetic energy. -/
theorem differentiableAt_specificKineticEnergy {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, DifferentiableAt ℝ (fun y ↦ u y i) x) :
    DifferentiableAt ℝ (specificKineticEnergy u) x := by
  have henergy :
      specificKineticEnergy u =
        fun y ↦ (1 / 2 : ℝ) * ∑ i : Fin n, (u y i) ^ 2 := by
    funext y
    exact specificKineticEnergy_eq_sum_sq u y
  rw [henergy]
  exact
    (DifferentiableAt.fun_sum fun i _hi ↦ (hu i).pow 2).const_mul
      (1 / 2 : ℝ)

/-- A spatial derivative of specific kinetic energy is the velocity paired
with the corresponding spatial derivative of velocity. -/
theorem partialDeriv_specificKineticEnergy {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) (j : Fin n)
    (hu : ∀ i : Fin n, DifferentiableAt ℝ (fun y ↦ u y i) x) :
    (∂[j.succ] (specificKineticEnergy u)) x =
      ∑ i : Fin n, u x i * (∂[j.succ] (fun y ↦ u y i)) x := by
  have henergy :
      specificKineticEnergy u =
        fun y ↦ (1 / 2 : ℝ) * ∑ i : Fin n, (u y i) ^ 2 := by
    funext y
    exact specificKineticEnergy_eq_sum_sq u y
  rw [henergy]
  have hsum :
      (∂[j.succ] (fun y ↦ ∑ i : Fin n, (u y i) ^ 2)) x =
        ∑ i : Fin n,
          ((∂[j.succ] (fun y ↦ u y i)) x * u x i +
            u x i * (∂[j.succ] (fun y ↦ u y i)) x) := by
    have hsplit :
        (∂[j.succ] (fun y ↦ ∑ i : Fin n, (u y i) ^ 2)) x =
          ∑ i : Fin n,
            (∂[j.succ] (fun y ↦ (u y i) ^ 2)) x := by
      unfold partialDeriv
      rw [fderiv_fun_sum]
      · simp
      · intro i _hi
        exact (hu i).pow 2
    rw [hsplit]
    apply Finset.sum_congr rfl
    intro i _hi
    simpa [pow_two] using
      PDE.partialDeriv_mul (i := j.succ) (f := fun y ↦ u y i)
        (g := fun y ↦ u y i) (x := x) (hu i) (hu i)
  have hconst :
      (∂[j.succ]
          (fun y ↦ (1 / 2 : ℝ) * ∑ i : Fin n, (u y i) ^ 2)) x =
        (1 / 2 : ℝ) *
          (∂[j.succ] (fun y ↦ ∑ i : Fin n, (u y i) ^ 2)) x := by
    simpa [smul_eq_mul] using
      PDE.partialDeriv_const_smul (n := n + 1) (E := ℝ) (1 / 2 : ℝ)
        (i := j.succ) (f := fun y ↦ ∑ i : Fin n, (u y i) ^ 2) (x := x)
  rw [hconst, hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Convective acceleration is the spatial gradient of specific kinetic
energy plus the contraction of vorticity with velocity. -/
theorem convectiveDerivative_eq_spatialGradient_specificKineticEnergy_add_vorticityContraction
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ j : Fin n, DifferentiableAt ℝ (fun y ↦ u y j) x) :
    convectiveDerivative n u u x =
      spatialGradient (specificKineticEnergy u) x +
        vorticityContraction n u x := by
  ext i
  simp only [convectiveDerivative_apply, PDE.spatialGradient_apply,
    PiLp.add_apply, vorticityContraction_apply, vorticityTensor_apply]
  rw [partialDeriv_specificKineticEnergy u x i hu]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- For irrotational flow, convective acceleration is the gradient of
specific kinetic energy. -/
theorem convectiveDerivative_eq_spatialGradient_specificKineticEnergy_of_vorticityTensor_eq_zero
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ j : Fin n, DifferentiableAt ℝ (fun y ↦ u y j) x)
    (hvort : vorticityTensor n u x = 0) :
    convectiveDerivative n u u x =
      spatialGradient (specificKineticEnergy u) x := by
  rw [
    convectiveDerivative_eq_spatialGradient_specificKineticEnergy_add_vorticityContraction
      u x hu]
  have hcontraction : vorticityContraction n u x = 0 := by
    ext i
    simp [vorticityContraction_apply, hvort]
  rw [hcontraction, add_zero]

/-- A steady, unforced, irrotational Euler balance makes the spatial
gradient of the Bernoulli function vanish. -/
theorem spatialGradient_bernoulliFunction_eq_zero_of_steady_irrotational_euler
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1))
    (hu : ∀ j : Fin n, DifferentiableAt ℝ (fun y ↦ u y j) x)
    (hp : DifferentiableAt ℝ p x)
    (hvort : vorticityTensor n u x = 0)
    (hmomentum :
      convectiveDerivative n u u x + spatialGradient p x = 0) :
    spatialGradient (bernoulliFunction u p) x = 0 := by
  rw [
    convectiveDerivative_eq_spatialGradient_specificKineticEnergy_of_vorticityTensor_eq_zero
      u x hu hvort] at hmomentum
  ext i
  simp only [PDE.spatialGradient_apply, PiLp.zero_apply]
  rw [show bernoulliFunction u p =
      fun y ↦ specificKineticEnergy u y + p y by rfl]
  rw [PDE.partialDeriv_add (differentiableAt_specificKineticEnergy u x hu) hp]
  simpa only [PiLp.add_apply, PiLp.zero_apply, PDE.spatialGradient_apply] using
    congrArg (fun v : ℝ^n ↦ v i) hmomentum

/-- The convective power equals transport of the specific kinetic energy. -/
theorem convectivePower_eq_kineticEnergyTransport {n : ℕ}
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, DifferentiableAt ℝ (fun y ↦ u y i) x) :
    convectivePower u x = kineticEnergyTransport u x := by
  rw [convectivePower_eq_sum, kineticEnergyTransport_eq_sum]
  simp_rw [convectiveDerivative_apply,
    partialDeriv_specificKineticEnergy u x _ hu]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Transport of the Bernoulli function is kinetic-energy transport plus
pressure power. -/
theorem bernoulliTransport_eq_kineticEnergyTransport_add_pressurePower
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, DifferentiableAt ℝ (fun y ↦ u y i) x)
    (hp : DifferentiableAt ℝ p x) :
    bernoulliTransport u p x =
      kineticEnergyTransport u x + pressurePower p u x := by
  rw [bernoulliTransport_eq_sum, kineticEnergyTransport_eq_sum,
    pressurePower_eq_sum]
  unfold bernoulliFunction
  simp_rw [
    PDE.partialDeriv_add (differentiableAt_specificKineticEnergy u x hu) hp,
    mul_add]
  rw [Finset.sum_add_distrib]

/-- For steady unforced Euler flow, the Bernoulli function has zero transport
along the velocity at the represented point. -/
theorem bernoulliTransport_eq_zero_of_steady_unforced_euler
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (x : ℝ^(n + 1))
    (hu : ∀ i : Fin n, DifferentiableAt ℝ (fun y ↦ u y i) x)
    (hp : DifferentiableAt ℝ p x)
    (hmomentum :
      convectiveDerivative n u u x + spatialGradient p x = 0) :
    bernoulliTransport u p x = 0 := by
  rw [
    bernoulliTransport_eq_kineticEnergyTransport_add_pressurePower
      u p x hu hp,
    ← convectivePower_eq_kineticEnergyTransport u x hu]
  unfold convectivePower pressurePower spatialScalarAdvection
  rw [← inner_add_right, hmomentum, inner_zero_right]

/-- The divergence of the kinetic-energy flux is energy transport plus
specific kinetic energy times the spatial divergence of velocity. -/
theorem spatialDivergence_kineticEnergyFlux_eq_kineticEnergyTransport_add
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ j : Fin n, DifferentiableAt ℝ (fun y ↦ u y j) x) :
    spatialDivergence n (kineticEnergyFlux u) x =
      kineticEnergyTransport u x +
        specificKineticEnergy u x * spatialDivergence n u x := by
  have henergy := differentiableAt_specificKineticEnergy u x hu
  have hproduct (j : Fin n) :
      (∂[j.succ] (fun y ↦ kineticEnergyFlux u y j)) x =
        (∂[j.succ] (specificKineticEnergy u)) x * u x j +
          specificKineticEnergy u x *
            (∂[j.succ] (fun y ↦ u y j)) x := by
    simpa [kineticEnergyFlux, PiLp.smul_apply, smul_eq_mul] using
      PDE.partialDeriv_mul (i := j.succ) henergy (hu j)
  simp only [spatialDivergence_apply]
  simp_rw [hproduct]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [kineticEnergyTransport_eq_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _hj
    ring
  · rfl

/-- For a divergence-free velocity, energy transport is the divergence of
the kinetic-energy flux. -/
theorem kineticEnergyTransport_eq_spatialDivergence_kineticEnergyFlux_of_divergenceFreeAt
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ j : Fin n, DifferentiableAt ℝ (fun y ↦ u y j) x)
    (hdiv : IncompressibleFlow.DivergenceFreeAt u x) :
    kineticEnergyTransport u x =
      spatialDivergence n (kineticEnergyFlux u) x := by
  rw [
    spatialDivergence_kineticEnergyFlux_eq_kineticEnergyTransport_add
      u x hu]
  rw [show spatialDivergence n u x = 0 from hdiv]
  simp

/-- For a differentiable divergence-free velocity, convective power is the
divergence of the kinetic-energy flux. -/
theorem convectivePower_eq_spatialDivergence_kineticEnergyFlux_of_divergenceFreeAt
    {n : ℕ} (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1))
    (hu : ∀ j : Fin n, DifferentiableAt ℝ (fun y ↦ u y j) x)
    (hdiv : IncompressibleFlow.DivergenceFreeAt u x) :
    convectivePower u x =
      spatialDivergence n (kineticEnergyFlux u) x := by
  rw [convectivePower_eq_kineticEnergyTransport u x hu]
  exact
    kineticEnergyTransport_eq_spatialDivergence_kineticEnergyFlux_of_divergenceFreeAt
      u x hu hdiv

/-- The divergence of the pressure flux is pressure power plus pressure times
the spatial divergence of velocity. -/
theorem spatialDivergence_pressureFlux_eq_pressurePower_add {n : ℕ}
    (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (hp : DifferentiableAt ℝ p x)
    (hu : ∀ j : Fin n, DifferentiableAt ℝ (fun y ↦ u y j) x) :
    spatialDivergence n (pressureFlux p u) x =
      pressurePower p u x +
        p x * spatialDivergence n u x := by
  have hproduct (j : Fin n) :
      (∂[j.succ] (fun y ↦ pressureFlux p u y j)) x =
        (∂[j.succ] p) x * u x j +
          p x * (∂[j.succ] (fun y ↦ u y j)) x := by
    simpa [pressureFlux, PiLp.smul_apply, smul_eq_mul] using
      PDE.partialDeriv_mul (i := j.succ) hp (hu j)
  simp only [spatialDivergence_apply]
  simp_rw [hproduct]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [pressurePower_eq_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _hj
    ring
  · rfl

/-- For a divergence-free velocity, pressure power is the divergence of the
pressure flux. -/
theorem pressurePower_eq_spatialDivergence_pressureFlux_of_divergenceFreeAt
    {n : ℕ} (p : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (hp : DifferentiableAt ℝ p x)
    (hu : ∀ j : Fin n, DifferentiableAt ℝ (fun y ↦ u y j) x)
    (hdiv : IncompressibleFlow.DivergenceFreeAt u x) :
    pressurePower p u x =
      spatialDivergence n (pressureFlux p u) x := by
  rw [spatialDivergence_pressureFlux_eq_pressurePower_add p u x hp hu]
  rw [show spatialDivergence n u x = 0 from hdiv]
  simp

end

end IncompressibleFlow
