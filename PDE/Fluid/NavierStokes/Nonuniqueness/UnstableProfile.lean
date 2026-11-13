/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension
public import PDE.CoordinateSystems.Axisymmetric.Isometry
public import PDE.Fluid.NavierStokes.Nonuniqueness.WeakEquations
public import PDE.Fluid.NavierStokes.Stationary.Linearization

/-!
# Unstable self-similar profiles

An `UnstableProfile` is the input of the general nonuniqueness theorem: a smooth
divergence-free solution `U`, with pressure `P`, of the self-similar profile equation

`-½ U - ½ ξ·∇U + (U·∇)U - ΔU + ∇P = 0`

(Hou, Wang and Yang, (1.6)), whose linearization has a weak eigenvalue
`μ > 0`, so `λ̃ = -μ < 0` in (1.12). The profile has bounded derivatives of every order, all
tending to zero at infinity and lying in `L⁴`, derivatives of positive order in `L²`, and a
pressure in `H¹`. Its far field is the degree `-1` homogeneous field `‖ξ‖⁻¹ A(ξ)`, with `A`
of degree zero, smooth away from the origin, equivariant under rotations about the third axis
and with `‖x‖⁻¹ A(x)` distributionally divergence-free, as in (1.4) and (1.8): the difference
between `U` and the far field cut off near the origin by `1 - unitCutoff` is square
integrable.

`unitCutoff` is the smooth bump on `ℝ^n` equal to one on the closed unit ball and zero
outside the open ball of radius two.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 1.2, (1.4)-(1.8), p. 3,
  (1.12) and Theorem 2, p. 4, Propositions 1 and 2, pp. 5-6, and Propositions 3 and 4, pp. 9-10.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

/-- The smooth cutoff `χ` on `ℝ^n`: `χ = 1` on the closed unit ball, `χ = 0` outside the open
ball of radius two, and `0 ≤ χ ≤ 1`. It is the bump `PDE.Analysis.standardBump n`. -/
def unitCutoff {n : ℕ} (x : ℝ^n) : ℝ :=
  PDE.Analysis.standardBump n x

/-- The unit cutoff is smooth. -/
theorem contDiff_unitCutoff {n : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (unitCutoff (n := n)) :=
  (PDE.Analysis.standardBump n).contDiff

/-- The unit cutoff equals one on the closed unit ball. -/
theorem unitCutoff_of_norm_le_one {n : ℕ} {x : ℝ^n} (hx : ‖x‖ ≤ 1) : unitCutoff x = 1 :=
  (PDE.Analysis.standardBump n).one_of_mem_closedBall
    (by rw [Metric.mem_closedBall, dist_zero_right]; exact hx)

/-- The unit cutoff vanishes outside the open ball of radius two. -/
theorem unitCutoff_of_two_le_norm {n : ℕ} {x : ℝ^n} (hx : 2 ≤ ‖x‖) : unitCutoff x = 0 :=
  (PDE.Analysis.standardBump n).zero_of_le_dist (by rw [dist_zero_right]; exact hx)

/-- The unit cutoff is nonnegative. -/
theorem unitCutoff_nonneg {n : ℕ} (x : ℝ^n) : 0 ≤ unitCutoff x :=
  (PDE.Analysis.standardBump n).nonneg

/-- The unit cutoff is at most one. -/
theorem unitCutoff_le_one {n : ℕ} (x : ℝ^n) : unitCutoff x ≤ 1 :=
  (PDE.Analysis.standardBump n).le_one

/-- A smooth decaying self-similar profile with an axisymmetric degree `-1` far field and an
unstable weak eigenvalue of its linearization. These are the hypotheses of the general
nonuniqueness theorem for the unforced Navier–Stokes equations; Hou, Wang and Yang construct
such a profile (Theorem 2 and Propositions 1 to 4). -/
structure UnstableProfile where
  /-- The profile velocity `Ũ`. -/
  U : ℝ^3 → ℝ^3
  /-- The profile pressure `P̃`. -/
  P : ℝ^3 → ℝ
  /-- The velocity is smooth. -/
  contDiff_U : ContDiff ℝ (⊤ : ℕ∞) U
  /-- The pressure is smooth. -/
  contDiff_P : ContDiff ℝ (⊤ : ℕ∞) P
  /-- The velocity is divergence-free. -/
  divergence_eq_zero : ∀ ξ, PDE.divergence U ξ = 0
  /-- The self-similar profile equation `-½ U - ½ ξ·∇U + (U·∇)U - ΔU + ∇P = 0`. -/
  profile_eq : ∀ ξ, stationaryVelocityOperator U ξ + gradient P ξ = 0
  /-- Every derivative of the velocity is bounded. -/
  bounded_derivatives : ∀ k : ℕ, ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k U ξ‖ ≤ C
  /-- Every derivative of the velocity, including the velocity itself, tends to zero at
  infinity. -/
  derivatives_tendsto_zero :
    ∀ k : ℕ, Tendsto (iteratedFDeriv ℝ k U) (cocompact (ℝ^3)) (𝓝 0)
  /-- Every derivative of the velocity, including the velocity itself, lies in `L⁴`. -/
  derivatives_memLp_four : ∀ k : ℕ, MemLp (iteratedFDeriv ℝ k U) 4 volume
  /-- Every derivative of positive order lies in `L²`; the velocity itself does not, because
  of its inverse-radius far field. -/
  derivatives_memLp_two : ∀ k : ℕ, 1 ≤ k → MemLp (iteratedFDeriv ℝ k U) 2 volume
  /-- The pressure lies in `L²`. -/
  pressure_memLp_two : MemLp P 2 volume
  /-- The pressure gradient lies in `L²`. -/
  pressure_gradient_memLp_two : MemLp (fderiv ℝ P) 2 volume
  /-- The angular profile `A` of the far field `‖ξ‖⁻¹ A(ξ)`. -/
  A : ℝ^3 → ℝ^3
  /-- The angular profile is homogeneous of degree zero. -/
  A_homogeneous : ∀ x (c : ℝ), 0 < c → A (c • x) = A x
  /-- The angular profile is smooth away from the origin. -/
  A_contDiffAt : ∀ x, x ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) A x
  /-- The angular profile is equivariant under rotations about the third axis. -/
  A_axisymmetric : ∀ φ x, A (PDE.CoordinateSystems.axialRotation φ x) =
    PDE.CoordinateSystems.axialRotation φ (A x)
  /-- The scale-invariant datum `‖x‖⁻¹ A(x)` is distributionally divergence-free, (1.8). -/
  datum_divergenceFree :
    IncompressibleFlow.DistributionallyDivergenceFree (fun x ↦ ‖x‖⁻¹ • A x)
  /-- The velocity minus its far field, cut off near the origin, is square integrable. -/
  nearField_memLp :
    MemLp (fun ξ ↦ U ξ - (1 - unitCutoff ξ) • (‖ξ‖⁻¹ • A ξ)) 2 volume
  /-- The linearization at the profile has a weak eigenvalue `μ > 0` with a nonzero
  divergence-free eigenfunction in `H¹(ℝ^3; ℝ^3)`. -/
  unstable : ∃ μ : ℝ, 0 < μ ∧ ∃ v : PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3)),
    v ≠ 0 ∧ Stationary.divergenceCLM v = 0 ∧ WeakEigenEquation U μ v

end NavierStokes.Nonuniqueness
