/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Field
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Simple and self-similar waves for conservation-law systems

For a state-space curve `w` and scalar phase `φ`, a simple wave has the form
`u(t,x) = w(φ(t,x))`. Substitution into the quasilinear system reduces the
PDE to a scalar transport equation whenever the tangent to `w` is a right
eigenvector of the flux Jacobian.

We also prove the self-similar reduction for `u(t,x) = w(x / t)` and
use the characteristic eigenvector identities along integral curves.

The reduction is (3)-(6) of Evans, §11.2.1, and the self-similar waves are those of Theorem 1
in §11.2.2, which are constant on lines through the origin.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equations (3)-(6); §11.2.2, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System


variable {m : ℕ}

/-! ## Simple-wave reduction -/

/-- Tangent to a state-space curve. -/
def curveTangent (curve : ℝ → ℝ^m) (s : ℝ) : ℝ^m :=
  deriv curve s

/-- The simple wave obtained by composing a state-space curve with a scalar phase. -/
def simpleWave
    (curve : ℝ → ℝ^m) (phase : ℝ^2 → ℝ) :
    ℝ^2 → ℝ^m :=
  curve ∘ phase

/-- A simple wave evaluates the state curve at the phase. -/
@[simp]
theorem simpleWave_apply (curve : ℝ → ℝ^m) (phase : ℝ^2 → ℝ) (p : ℝ^2) :
    simpleWave curve phase p = curve (phase p) :=
  rfl

/-- Coordinate derivatives of a simple wave are scalar phase derivatives
times the curve tangent. -/
theorem partialDeriv_simpleWave (i : Fin 2) {curve : ℝ → ℝ^m} {phase : ℝ^2 → ℝ} {p : ℝ^2}
    (hcurve : DifferentiableAt ℝ curve (phase p)) (hphase : DifferentiableAt ℝ phase p) :
    (∂[i] (simpleWave curve phase)) p = (∂[i] phase) p • curveTangent curve (phase p) := by
  rw [show simpleWave curve phase = curve ∘ phase from rfl]
  unfold partialDeriv curveTangent
  rw [fderiv_comp p hcurve hphase, ContinuousLinearMap.comp_apply]
  rw [← fderiv_apply_one_eq_deriv]
  rw [← ContinuousLinearMap.map_smul]
  congr 1
  simp

/-- A simple wave reduces the system residual to its scalar characteristic
transport residual. -/
theorem quasilinearResidual_simpleWave {flux : ℝ^m → ℝ^m} {curve : ℝ → ℝ^m} {phase : ℝ^2 → ℝ}
    {speed : ℝ → ℝ} {p : ℝ^2} (hcurve : DifferentiableAt ℝ curve (phase p))
    (hphase : DifferentiableAt ℝ phase p)
    (heigen : fderiv ℝ flux (curve (phase p)) (curveTangent curve (phase p)) =
      speed (phase p) • curveTangent curve (phase p)) :
    quasilinearResidual flux (simpleWave curve phase) p =
      ((∂[0] phase) p + speed (phase p) * (∂[1] phase) p) • curveTangent curve (phase p) := by
  rw [quasilinearResidual, partialDeriv_simpleWave 0 hcurve hphase,
    partialDeriv_simpleWave 1 hcurve hphase]
  simp only [simpleWave_apply]
  rw [map_smul, heigen]
  simp only [smul_smul]
  rw [← add_smul]
  congr 1
  exact congrArg (fun r : ℝ ↦ (∂[0] phase) p + r) (mul_comm ((∂[1] phase) p) (speed (phase p)))

/-- The scalar characteristic equation makes the associated simple wave a
quasilinear solution. -/
theorem quasilinearResidual_simpleWave_eq_zero {flux : ℝ^m → ℝ^m} {curve : ℝ → ℝ^m}
    {phase : ℝ^2 → ℝ} {speed : ℝ → ℝ} {p : ℝ^2} (hcurve : DifferentiableAt ℝ curve (phase p))
    (hphase : DifferentiableAt ℝ phase p)
    (heigen : fderiv ℝ flux (curve (phase p)) (curveTangent curve (phase p)) =
      speed (phase p) • curveTangent curve (phase p))
    (htransport : (∂[0] phase) p + speed (phase p) * (∂[1] phase) p = 0) :
    quasilinearResidual flux (simpleWave curve phase) p = 0 := by
  rw [quasilinearResidual_simpleWave hcurve hphase heigen, htransport]
  exact zero_smul ℝ _

/-- Under differentiability of the flux, the same simple wave solves the
conservative form. -/
theorem fluxResidual_simpleWave_eq_zero {flux : ℝ^m → ℝ^m} {curve : ℝ → ℝ^m} {phase : ℝ^2 → ℝ}
    {speed : ℝ → ℝ} {p : ℝ^2} (hflux : DifferentiableAt ℝ flux (curve (phase p)))
    (hcurve : DifferentiableAt ℝ curve (phase p)) (hphase : DifferentiableAt ℝ phase p)
    (heigen : fderiv ℝ flux (curve (phase p)) (curveTangent curve (phase p)) =
      speed (phase p) • curveTangent curve (phase p))
    (htransport : (∂[0] phase) p + speed (phase p) * (∂[1] phase) p = 0) :
    fluxResidual flux (simpleWave curve phase) p = 0 := by
  change fluxResidual flux (curve ∘ phase) p = 0
  rw [fluxResidual_eq_quasilinearResidual hflux (hcurve.comp p hphase)]
  exact quasilinearResidual_simpleWave_eq_zero hcurve hphase heigen htransport

/-! ## Characteristic fields and Riemann invariants -/

/-- An integral curve of a characteristic field supplies the eigenvector
relation needed by the simple-wave reduction. -/
theorem CharacteristicField.eigenvector_eq_curveTangent {flux : ℝ^m → ℝ^m}
    (C : CharacteristicField flux) {curve : ℝ → ℝ^m} (hcurve : IsIntegralCurve curve C.vectorField)
    (s : ℝ) :
    fderiv ℝ flux (curve s) (curveTangent curve s) = C.speed (curve s) • curveTangent curve s := by
  rw [curveTangent, (hcurve s).deriv]
  exact (C.eigenvector (curve s)).apply_eq_smul

/-! ## Self-similar waves -/

/-- The self-similar coordinate `x / t`. -/
def similarityVariable (p : ℝ^2) : ℝ :=
  p 1 / p 0

/-- Nonzero spacetime dilation leaves the self-similar coordinate unchanged. -/
theorem similarityVariable_smul {a : ℝ} (ha : a ≠ 0) (p : ℝ^2) :
    similarityVariable (a • p) = similarityVariable p := by
  change a * p 1 / (a * p 0) = p 1 / p 0
  rw [mul_div_mul_left _ _ ha]

/-- The self-similar coordinate is differentiable away from `t = 0`. -/
theorem differentiableAt_similarityVariable {p : ℝ^2} (ht : p 0 ≠ 0) :
    DifferentiableAt ℝ similarityVariable p := by
  change DifferentiableAt ℝ (fun q : ℝ^2 ↦ q 1 * (q 0)⁻¹) p
  have hspace : DifferentiableAt ℝ (fun q : ℝ^2 ↦ q 1) p := by
    cas
  have htime : DifferentiableAt ℝ (fun q : ℝ^2 ↦ q 0) p := by
    cas
  exact hspace.mul (htime.inv ht)

/-- The self-similar coordinate is `C¹` away from the initial-time axis. -/
theorem contDiffAt_similarityVariable {p : ℝ^2} (ht : p 0 ≠ 0) :
    ContDiffAt ℝ 1 similarityVariable p := by
  change ContDiffAt ℝ 1 (fun q : ℝ^2 ↦ q 1 / q 0) p
  have hspace : ContDiffAt ℝ 1 (fun q : ℝ^2 ↦ q 1) p := by
    fun_prop
  have htime : ContDiffAt ℝ 1 (fun q : ℝ^2 ↦ q 0) p := by
    fun_prop
  exact hspace.div htime ht

/-- Time derivative of `x / t`. -/
theorem partialDeriv_similarityVariable_time (p : ℝ^2) (ht : p 0 ≠ 0) :
    (∂[0] similarityVariable) p = -(p 1) * (p 0)⁻¹ * (p 0)⁻¹ := by
  cas

/-- Spatial derivative of `x / t`. -/
theorem partialDeriv_similarityVariable_space (p : ℝ^2) (ht : p 0 ≠ 0) :
    (∂[1] similarityVariable) p = (p 0)⁻¹ := by
  cas

/-- The self-similar coordinate solves `ξ_t + ξ ξ_x = 0` away from `t = 0`. -/
theorem similarityVariable_transport (p : ℝ^2) (ht : p 0 ≠ 0) :
    (∂[0] similarityVariable) p + similarityVariable p * (∂[1] similarityVariable) p = 0 := by
  rw [partialDeriv_similarityVariable_time p ht,
    partialDeriv_similarityVariable_space p ht, similarityVariable]
  cas

/-- A state-space profile evaluated at `x / t`. -/
def selfSimilarWave (profile : ℝ → ℝ^m) :
    ℝ^2 → ℝ^m :=
  simpleWave profile similarityVariable

/-- A self-similar wave evaluates the profile at the similarity variable
`x / t`. -/
@[simp]
theorem selfSimilarWave_apply (profile : ℝ → ℝ^m) (p : ℝ^2) :
    selfSimilarWave profile p = profile (similarityVariable p) :=
  rfl

/-- A self-similar wave is invariant under every nonzero spacetime
dilation. -/
theorem selfSimilarWave_smul {a : ℝ} (ha : a ≠ 0) (profile : ℝ → ℝ^m) (p : ℝ^2) :
    selfSimilarWave profile (a • p) = selfSimilarWave profile p := by
  rw [selfSimilarWave_apply, selfSimilarWave_apply, similarityVariable_smul ha p]

/-- A `C¹` profile gives a `C¹` self-similar wave away from `t = 0`. -/
theorem contDiffAt_selfSimilarWave {profile : ℝ → ℝ^m} {p : ℝ^2}
    (hprofile : ContDiffAt ℝ 1 profile (similarityVariable p)) (ht : p 0 ≠ 0) :
    ContDiffAt ℝ 1 (selfSimilarWave profile) p :=
  hprofile.comp p (contDiffAt_similarityVariable ht)

/-- The rarefaction ODE
`Df(w(ξ)) w'(ξ) = ξ w'(ξ)` implies the quasilinear conservation law for
`w(x/t)`. -/
theorem quasilinearResidual_selfSimilarWave_eq_zero {flux : ℝ^m → ℝ^m} {profile : ℝ → ℝ^m} {p : ℝ^2}
    (ht : p 0 ≠ 0) (hprofile : DifferentiableAt ℝ profile (similarityVariable p))
    (hode : fderiv ℝ flux (profile (similarityVariable p)) (curveTangent profile
      (similarityVariable p)) = similarityVariable p • curveTangent profile (similarityVariable
      p)) :
    quasilinearResidual flux (selfSimilarWave profile) p = 0 := by
  rw [selfSimilarWave]
  apply quasilinearResidual_simpleWave_eq_zero (speed := fun s ↦ s) hprofile
    (differentiableAt_similarityVariable ht) hode
  exact similarityVariable_transport p ht

/-- Under differentiability of the flux, a rarefaction profile also solves
the conservative system. -/
theorem fluxResidual_selfSimilarWave_eq_zero {flux : ℝ^m → ℝ^m} {profile : ℝ → ℝ^m} {p : ℝ^2}
    (ht : p 0 ≠ 0) (hflux : DifferentiableAt ℝ flux (profile (similarityVariable p)))
    (hprofile : DifferentiableAt ℝ profile (similarityVariable p))
    (hode : fderiv ℝ flux (profile (similarityVariable p)) (curveTangent profile
      (similarityVariable p)) = similarityVariable p • curveTangent profile (similarityVariable
      p)) :
    fluxResidual flux (selfSimilarWave profile) p = 0 := by
  change fluxResidual flux (profile ∘ similarityVariable) p = 0
  rw [fluxResidual_eq_quasilinearResidual hflux
    (hprofile.comp p (differentiableAt_similarityVariable ht))]
  exact quasilinearResidual_selfSimilarWave_eq_zero ht hprofile hode

/-- Global pointwise form of the self-similar rarefaction reduction on any
set avoiding the initial-time axis. -/
theorem fluxResidual_selfSimilarWave_eq_zero_on {flux : ℝ^m → ℝ^m} {profile : ℝ → ℝ^m} {U : Set ℝ^2}
    (ht : ∀ p ∈ U, p 0 ≠ 0) (hflux : Differentiable ℝ flux) (hprofile : Differentiable ℝ profile)
    (hode : ∀ s, fderiv ℝ flux (profile s) (curveTangent profile s) = s • curveTangent profile s) :
    ∀ p ∈ U, fluxResidual flux (selfSimilarWave profile) p = 0 := by
  intro p hp
  exact fluxResidual_selfSimilarWave_eq_zero (ht p hp) (hflux (profile (similarityVariable p)))
    (hprofile (similarityVariable p)) (hode (similarityVariable p))

end PDE.Hyperbolic.ConservationLaw.System
