/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators

/-!
# Conservation of mass

The pointwise continuity-equation residual is

```text
∂ₜρ + div(ρu)
```

for a density `ρ` and spacetime velocity `u`. The product rule decomposes the
residual into the material derivative of density and the volumetric expansion:

```text
Dₜρ + ρ div u.
```

For a nonzero constant density, conservation of mass is therefore equivalent
to incompressibility. The definitions use the same spacetime convention as
the Navier–Stokes operators: coordinate `0` is time, and coordinate `i.succ`
is the `i`-th spatial coordinate.

Majda and Bertozzi, Chapter 1, introduce the incompressible equations and the physical quantities
they involve.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

namespace IncompressibleFlow

open EuclideanSpace

set_option linter.missingDocs true

noncomputable section

/-- Mass flux `ρu` associated with density `ρ` and velocity `u`. -/
def massFlux {n : ℕ} (ρ : ℝ^(n + 1) → ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ^n :=
  ρ x • u x

/-- Pointwise continuity-equation residual `∂ₜρ + div(ρu)`. -/
def continuityResidual {n : ℕ} (ρ : ℝ^(n + 1) → ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ :=
  (∂[(0 : Fin (n + 1))] ρ) x +
    spatialDivergence n (massFlux ρ u) x

/-- The continuity residual is the material derivative of density plus the
density times the spatial divergence. -/
theorem continuityResidual_eq_scalarMaterialDerivative_add_density_mul_spatialDivergence
    {n : ℕ} (ρ : ℝ^(n + 1) → ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) (hρ : DifferentiableAt ℝ ρ x)
    (hu : ∀ j : Fin n, DifferentiableAt ℝ (fun y ↦ u y j) x) :
    continuityResidual ρ u x =
      scalarMaterialDerivative n u ρ x +
        ρ x * spatialDivergence n u x := by
  have hproduct (j : Fin n) :
      (∂[j.succ] (fun y ↦ massFlux ρ u y j)) x =
        (∂[j.succ] ρ) x * u x j +
          ρ x * (∂[j.succ] (fun y ↦ u y j)) x := by
    simpa [massFlux, PiLp.smul_apply, smul_eq_mul] using
      PDE.partialDeriv_mul (i := j.succ) hρ (hu j)
  simp only [continuityResidual, spatialDivergence_apply,
    scalarMaterialDerivative_apply]
  simp_rw [hproduct]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  have htransport :
      (∑ j : Fin n, (∂[j.succ] ρ) x * u x j) =
        ∑ j : Fin n, u x j * (∂[j.succ] ρ) x := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [htransport]
  ring

/-- At constant density, the continuity residual is density times spatial
divergence. -/
theorem continuityResidual_const {n : ℕ} (ρ₀ : ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    continuityResidual (fun _ ↦ ρ₀) u x =
      ρ₀ * spatialDivergence n u x := by
  have hflux (j : Fin n) :
      (∂[j.succ]
          (fun y ↦ massFlux (fun _ : ℝ^(n + 1) ↦ ρ₀) u y j)) x =
        ρ₀ * (∂[j.succ] (fun y ↦ u y j)) x := by
    simpa [massFlux, PiLp.smul_apply, smul_eq_mul] using
      (PDE.partialDeriv_const_smul (n := n + 1) (E := ℝ) ρ₀
        (i := j.succ) (f := fun y ↦ u y j) (x := x))
  simp only [continuityResidual, spatialDivergence_apply]
  simp_rw [hflux]
  simp only [PDE.partialDeriv_const, zero_add]
  rw [Finset.mul_sum]

/-- A divergence-free velocity conserves every constant density pointwise. -/
theorem continuityResidual_const_eq_zero_of_divergenceFreeAt
    {n : ℕ} (ρ₀ : ℝ) {u : ℝ^(n + 1) → ℝ^n}
    {x : ℝ^(n + 1)} (hdiv : IncompressibleFlow.DivergenceFreeAt u x) :
    continuityResidual (fun _ ↦ ρ₀) u x = 0 := by
  rw [continuityResidual_const, hdiv, mul_zero]

/-- For nonzero constant density, conservation of mass is equivalent to
pointwise incompressibility. -/
theorem continuityResidual_const_eq_zero_iff_divergenceFreeAt
    {n : ℕ} {ρ₀ : ℝ} (hρ₀ : ρ₀ ≠ 0)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    continuityResidual (fun _ ↦ ρ₀) u x = 0 ↔
      IncompressibleFlow.DivergenceFreeAt u x := by
  rw [continuityResidual_const]
  simp [IncompressibleFlow.DivergenceFreeAt, hρ₀]

end

end IncompressibleFlow
