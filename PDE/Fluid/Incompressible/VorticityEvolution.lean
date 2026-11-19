/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.Operators

/-!
# Vorticity evolution operators

`vorticityTransportResidual` is the vector transport-stretching-diffusion residual
`Dₜᵘω - (ω · ∇)u - νΔω` on spacetime `ℝ^(n + 1)`, with time in coordinate zero. In three
dimensions, taking the
transported field to be the curl of a divergence-free velocity gives the
unforced Euler and Navier–Stokes vorticity residuals.

Vortex stretching and its balance by diffusion are discussed in Majda and Bertozzi, Chapter 1.

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

/-- Vorticity stretching `(ω · ∇)u`. -/
def vorticityStretching (n : ℕ) (ω u : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) : ℝ^n :=
  convectiveDerivative n ω u x

/-- Vorticity transport residual
`Dₜᵘω - (ω · ∇)u - νΔω`.

For `n = 3`, `ω = curl u`, and divergence-free velocity, vanishing of this
residual is the unforced Euler vorticity equation at `ν = 0` and the
Navier–Stokes vorticity equation at positive `ν`. A force with nonzero curl
contributes a source term. In general dimension the vorticity is a two-form;
the independent vector field supplied here is not automatically a velocity curl. -/
def vorticityTransportResidual (n : ℕ) (ν : ℝ)
    (u ω : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) : ℝ^n :=
  materialDerivative n u ω x - vorticityStretching n ω u x -
    ν • spatialVectorLaplacian n ω x

/-- A zero vorticity residual is exactly the transport-stretching-diffusion
equation. -/
theorem vorticityTransportResidual_eq_zero_iff
    (n : ℕ) (ν : ℝ) (u ω : ℝ^(n + 1) → ℝ^n)
    (x : ℝ^(n + 1)) :
    vorticityTransportResidual n ν u ω x = 0 ↔
      materialDerivative n u ω x =
        vorticityStretching n ω u x +
          ν • spatialVectorLaplacian n ω x := by
  unfold vorticityTransportResidual
  rw [sub_eq_zero, sub_eq_iff_eq_add]
  simp only [add_comm]

/-- At zero viscosity, the vector residual contains only transport and stretching. -/
theorem vorticityTransportResidual_zero_viscosity
    (n : ℕ) (u ω : ℝ^(n + 1) → ℝ^n) (x : ℝ^(n + 1)) :
    vorticityTransportResidual n 0 u ω x =
      materialDerivative n u ω x - vorticityStretching n ω u x := by
  simp [vorticityTransportResidual]

end

end IncompressibleFlow
