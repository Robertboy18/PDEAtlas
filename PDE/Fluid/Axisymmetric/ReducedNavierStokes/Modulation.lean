/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Basic.Real.Basic
import CAS.ExactTactic

/-!
# Scalar modulation identities at a meridional fixed point

All statements are identities between real numbers. The PDE content enters only through the
hypotheses, which the application must supply by evaluating the reduced axisymmetric equations at
one point. We record the resulting modulation laws in a form that is easy to check and to bound.

The setting is the reduced axisymmetric flow with swirl in squared-radius variables, with a
normalisation point fixed on the symmetry axis and two modulation parameters: a translation rate
`c` along the axis and an amplitude rate `c_u` for the swirl.

* Translation. On the axis the reconstructed velocity is purely axial with value `2 Ψ(0, z)`
  (`axisymmetricVelocity_apply_two_of_mem_symmetryAxis` in `CartesianReconstruction`). In a
  frame translating with speed `c` the origin is a stagnation point of the meridional flow
  exactly when `c + 2 Ψ₀ = 0`, where `Ψ₀` is the streamfunction profile at the origin. If a
  background pair `(c̄, Ψ̄₀)` and its perturbation `(c̄ + δc, Ψ̄₀ + δΨ₀)` both satisfy this
  condition, then `δc = -2 δΨ₀` (`translationModulation_eq_of_fixedPoint`). No slope or
  nondegeneracy constant appears, in contrast to gauges that normalise a vorticity gradient.

* Amplitude. Evaluating the reduced swirl equation at the origin, where the transport terms
  vanish because the origin is a stagnation point, leaves the balance
  `2 u₀ Ψ_z + c_u u₀ + ν E_U = 0`. Here `u₀ ≠ 0` is the swirl coefficient at the origin, `Ψ_z`
  the axial derivative of the streamfunction profile there, and `E_U` the value at the origin
  of the diffusion operator applied to the swirl coefficient. Perturbing every quantity about a
  background `(Ψ̄_z, c̄_u, ν̄, Ē_U)` that satisfies the balance and subtracting gives the exact
  law `amplitudeModulation` for `δc_u`, which is linear in the perturbations except for the
  single product `δν · δE_U / u₀` (`amplitudeModulationNonlinear`). For Euler (`ν = 0`, `δν = 0`)
  the law is exactly `δc_u = -2 δΨ_z`. When the background is only an approximate profile, its
  residual at the origin is absorbed into a fixed offset of the amplitude rate
  (`amplitudeResidualOffset`), and the same law holds for the perturbation
  (`amplitudeModulation_eq_of_raw_origin_equation`).

The sign conventions are those of the hypotheses `hbar`, `hfull` and `heq`. For a concrete flow
these hypotheses are to be derived from the reduced equations of `ReducedNavierStokes`.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v1, for the Euler case: Section 3.1.2,
  (49)-(50), p. 14, gives the fixed-point and amplitude normalization; Section 3.2.3, (78)-(80),
  p. 17, absorbs the raw residual into the amplitude rate; Section 3.2.5, (94), p. 19, gives the two
  perturbation laws.
  <https://arxiv.org/abs/2609.10860v1>
-/

@[expose] public section

noncomputable section

namespace AxisymmetricFlow

/-- Translation-rate perturbation preserving the meridional fixed point. -/
def translationModulation (deltaPsi0 : ℝ) : ℝ := -2 * deltaPsi0

/-- Perturbing the background and full fixed-point identities gives the translation law. -/
theorem translationModulation_eq_of_fixedPoint
    (barC barPsi0 deltaC deltaPsi0 : ℝ)
    (hbar : barC + 2 * barPsi0 = 0)
    (hfull : barC + deltaC + 2 * (barPsi0 + deltaPsi0) = 0) :
    deltaC = translationModulation deltaPsi0 := by
  unfold translationModulation
  linarith

/-- The translation law satisfies the perturbation fixed-point identity. -/
@[simp]
theorem translationModulation_add (deltaPsi0 : ℝ) :
    translationModulation deltaPsi0 + 2 * deltaPsi0 = 0 := by
  unfold translationModulation
  ring

/-- `|δc| = 2 |δΨ₀|`: the translation bound has no slope or nondegeneracy constant. -/
theorem abs_translationModulation (deltaPsi0 : ℝ) :
    |translationModulation deltaPsi0| = 2 * |deltaPsi0| := by
  simp [translationModulation, abs_mul]

/-- Linear part of the amplitude-rate perturbation at a fixed meridional point. -/
def amplitudeModulationLinear
    (u0 barNu eBarU deltaPsiZ deltaEU deltaNu : ℝ) : ℝ :=
  -2 * deltaPsiZ - barNu / u0 * deltaEU - eBarU / u0 * deltaNu

/-- The sole nonlinear amplitude-rate term in the viscous problem. -/
def amplitudeModulationNonlinear (u0 deltaEU deltaNu : ℝ) : ℝ :=
  -(deltaNu / u0 * deltaEU)

/-- Exact amplitude-rate perturbation after the fixed residual offset has been absorbed. -/
def amplitudeModulation
    (u0 barNu eBarU deltaPsiZ deltaEU deltaNu : ℝ) : ℝ :=
  amplitudeModulationLinear u0 barNu eBarU deltaPsiZ deltaEU deltaNu +
    amplitudeModulationNonlinear u0 deltaEU deltaNu

/-- The exact amplitude formula solves the origin swirl equation. -/
theorem amplitudeModulation_solves
    (u0 barNu eBarU deltaPsiZ deltaEU deltaNu : ℝ) (hu0 : u0 ≠ 0) :
    u0 * amplitudeModulation u0 barNu eBarU deltaPsiZ deltaEU deltaNu =
      -2 * u0 * deltaPsiZ - barNu * deltaEU - eBarU * deltaNu - deltaNu * deltaEU := by
  unfold amplitudeModulation amplitudeModulationLinear amplitudeModulationNonlinear
  cas

/-- Nonzero background amplitude gives uniqueness of the amplitude rate. -/
theorem amplitudeModulation_eq_of_origin_equation
    (u0 barNu eBarU deltaPsiZ deltaEU deltaNu deltaCu : ℝ)
    (hu0 : u0 ≠ 0)
    (heq : u0 * deltaCu =
      -2 * u0 * deltaPsiZ - barNu * deltaEU - eBarU * deltaNu - deltaNu * deltaEU) :
    deltaCu = amplitudeModulation u0 barNu eBarU deltaPsiZ deltaEU deltaNu := by
  apply mul_left_cancel₀ hu0
  rw [heq, amplitudeModulation_solves _ _ _ _ _ _ hu0]

/-- In Euler, the amplitude modulation is exactly linear. -/
@[simp]
theorem amplitudeModulation_zero_viscosity
    (u0 eBarU deltaPsiZ deltaEU : ℝ) :
    amplitudeModulation u0 0 eBarU deltaPsiZ deltaEU 0 = -2 * deltaPsiZ := by
  simp [amplitudeModulation, amplitudeModulationLinear, amplitudeModulationNonlinear]

/-- Exact absolute value of the nonlinear viscous term. -/
theorem abs_amplitudeModulationNonlinear (u0 deltaEU deltaNu : ℝ) :
    |amplitudeModulationNonlinear u0 deltaEU deltaNu| =
      |deltaNu| / |u0| * |deltaEU| := by
  simp [amplitudeModulationNonlinear, abs_mul, abs_div]

/-- Fixed amplitude-rate correction cancelling the raw swirl residual at the origin. -/
def amplitudeResidualOffset (u0 rawResidualU0 : ℝ) : ℝ := -rawResidualU0 / u0

/-- The corrected swirl residual vanishes at the normalization point. -/
theorem amplitudeResidualOffset_cancels
    (u0 rawResidualU0 : ℝ) (hu0 : u0 ≠ 0) :
    rawResidualU0 + amplitudeResidualOffset u0 rawResidualU0 * u0 = 0 := by
  simp [amplitudeResidualOffset, hu0]

/-- The full origin equation yields the recentered amplitude law for an approximate profile. -/
theorem amplitudeModulation_eq_of_raw_origin_equation
    (u0 barPsiZ barCu barNu eBarU deltaPsiZ deltaEU deltaNu deltaCu : ℝ)
    (hu0 : u0 ≠ 0)
    (heq : 2 * u0 * (barPsiZ + deltaPsiZ) +
      (barCu + amplitudeResidualOffset u0
        (2 * u0 * barPsiZ + barCu * u0 + barNu * eBarU) + deltaCu) * u0 +
      (barNu + deltaNu) * (eBarU + deltaEU) = 0) :
    deltaCu = amplitudeModulation u0 barNu eBarU deltaPsiZ deltaEU deltaNu := by
  apply amplitudeModulation_eq_of_origin_equation _ _ _ _ _ _ _ hu0
  have hcancel := amplitudeResidualOffset_cancels u0
    (2 * u0 * barPsiZ + barCu * u0 + barNu * eBarU) hu0
  nlinarith

end AxisymmetricFlow
