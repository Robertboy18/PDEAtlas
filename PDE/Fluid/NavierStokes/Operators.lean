/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators

/-!
# Navier–Stokes operators

The viscous term `viscousTerm n ν u = ν Δu` is the spatial vector Laplacian scaled by the
viscosity. The material derivative, spatial Laplacian, pressure gradient, and
incompressibility predicates are model-independent and are in
`PDE.Fluid.Incompressible.Operators`. `spatialDivergence_viscousTerm` is used to show that the
viscous term contributes no source to the pressure Poisson equation (Majda and Bertozzi,
Chapter 1).

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge Texts in Applied
  Mathematics 27, Cambridge University Press, 2001, Chapter 1.
  <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace

set_option linter.missingDocs true

/-- The viscous term `viscosity Δu`, with the Laplacian taken only in spatial variables. -/
noncomputable def viscousTerm (n : ℕ) (viscosity : ℝ) (u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : ℝ^n :=
  viscosity • IncompressibleFlow.spatialVectorLaplacian n u x

/-- Component formula for the viscous term. -/
@[simp] theorem viscousTerm_apply (n : ℕ) (viscosity : ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) (i : Fin n) :
    viscousTerm n viscosity u x i =
      viscosity * IncompressibleFlow.spatialVectorLaplacian n u x i := by
  simp [viscousTerm]

/-- Spatial divergence commutes with the constant viscosity factor. -/
theorem spatialDivergence_viscousTerm (n : ℕ) (viscosity : ℝ)
    (u : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    IncompressibleFlow.spatialDivergence n
        (viscousTerm n viscosity u) x =
      viscosity * IncompressibleFlow.spatialDivergence n
        (IncompressibleFlow.spatialVectorLaplacian n u) x := by
  simp only [IncompressibleFlow.spatialDivergence_apply, viscousTerm_apply]
  have hderiv (i : Fin n) :
      (∂[i.succ]
          (fun y ↦ viscosity *
            IncompressibleFlow.spatialVectorLaplacian n u y i)) x =
        viscosity * (∂[i.succ]
          (fun y ↦ IncompressibleFlow.spatialVectorLaplacian n u y i)) x := by
    simpa [smul_eq_mul] using
      PDE.partialDeriv_const_smul (n := n + 1) (E := ℝ) viscosity
        (i := i.succ)
        (f := fun y ↦ IncompressibleFlow.spatialVectorLaplacian n u y i)
        (x := x)
  simp_rw [hderiv]
  rw [Finset.mul_sum]

end NavierStokes
