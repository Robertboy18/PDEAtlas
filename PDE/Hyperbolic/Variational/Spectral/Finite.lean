/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Finite spectral wave trajectories

A weak eigenfunction satisfies its variational equation against every energy
test. Consequently, a finite sum of evolving weak eigenfunctions solves the
ambient homogeneous wave equation, not merely its projection onto the trial
space. This property allows two different truncations to be compared by the
energy identity.

Each coefficient pair evolves by the exponential of the two-dimensional
operator `(q,p) ↦ (p,-λq)`. The construction works for every real eigenvalue;
positivity and coercivity enter only in the energy estimates and infinite
spectral limit. No smoothness of the spatial eigenfunctions is used.
-/

@[expose] public section

noncomputable section

namespace Hyperbolic.Variational

open scoped BigOperators InnerProductSpace

/-- The first-order operator for a scalar wave mode of eigenvalue `lambda`. -/
def waveModeGenerator (lambda : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-lambda) • ContinuousLinearMap.fst ℝ ℝ ℝ)

/-- The wave-mode generator maps displacement and velocity to velocity and
acceleration. -/
@[simp]
theorem waveModeGenerator_apply (lambda : ℝ) (x : ℝ × ℝ) :
    waveModeGenerator lambda x = (x.2, -lambda * x.1) := by
  rfl

/-- Global evolution of one spectral coefficient pair. -/
def waveModeEvolution (lambda t : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  NormedSpace.exp (t • waveModeGenerator lambda)

/-- A mode has the prescribed coefficient pair at time zero. -/
@[simp]
theorem waveModeEvolution_zero (lambda : ℝ) :
    waveModeEvolution lambda 0 = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  simp only [waveModeEvolution, zero_smul, NormedSpace.exp_zero, ContinuousLinearMap.one_def]

/-- The mode evolution obeys the group law for arbitrary real times. -/
theorem waveModeEvolution_add (lambda s t : ℝ) :
    waveModeEvolution lambda (s + t) =
      (waveModeEvolution lambda s).comp (waveModeEvolution lambda t) := by
  let : NormedAlgebra ℚ (ℝ × ℝ →L[ℝ] ℝ × ℝ) := NormedAlgebra.restrictScalars ℚ ℝ (ℝ × ℝ →L[ℝ] ℝ × ℝ)
  unfold waveModeEvolution
  rw [add_smul, NormedSpace.exp_add_of_commute
    (((Commute.refl (waveModeGenerator lambda)).smul_left s).smul_right t)]
  rfl

/-- Differentiating the operator exponential gives the two scalar wave
equations simultaneously. -/
theorem hasDerivAt_waveModeEvolution (lambda : ℝ) (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ waveModeEvolution lambda s x)
      (waveModeGenerator lambda (waveModeEvolution lambda t x)) t := by
  have h := (hasDerivAt_exp_smul_const' (waveModeGenerator lambda) t).clm_apply
    (hasDerivAt_const t x)
  simpa only [waveModeEvolution, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, map_zero, add_zero] using h

/-- The displacement coefficient has the velocity coefficient as derivative. -/
theorem hasDerivAt_waveModeDisplacement (lambda : ℝ) (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ (waveModeEvolution lambda s x).1) (waveModeEvolution lambda t x).2 t := by
  have h := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_waveModeEvolution lambda x t)
  simpa only [Function.comp_def, ContinuousLinearMap.coe_fst', waveModeGenerator_apply] using h

/-- The velocity coefficient has derivative `-lambda` times the displacement
coefficient. -/
theorem hasDerivAt_waveModeVelocity (lambda : ℝ) (x : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (fun s ↦ (waveModeEvolution lambda s x).2)
      (-lambda * (waveModeEvolution lambda t x).1) t := by
  have h := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_waveModeEvolution lambda x t)
  simpa only [Function.comp_def, ContinuousLinearMap.coe_snd', waveModeGenerator_apply] using h

variable {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The displacement obtained by evolving a finite family of weak eigenmodes. -/
def finiteSpectralDisplacement (lambda : ι → ℝ) (e : ι → V)
    (s : Finset ι) (data : ι → ℝ × ℝ) (t : ℝ) : V :=
  ∑ i ∈ s, (waveModeEvolution (lambda i) t (data i)).1 • e i

/-- The energy-space velocity of a finite spectral wave. Its pivot image is
the physical velocity. -/
def finiteSpectralVelocity (lambda : ι → ℝ) (e : ι → V)
    (s : Finset ι) (data : ι → ℝ × ℝ) (t : ℝ) : V :=
  ∑ i ∈ s, (waveModeEvolution (lambda i) t (data i)).2 • e i

/-- The acceleration of a finite spectral wave, before the pivot inclusion. -/
def finiteSpectralAcceleration (lambda : ι → ℝ) (e : ι → V)
    (s : Finset ι) (data : ι → ℝ × ℝ) (t : ℝ) : V :=
  ∑ i ∈ s, (-lambda i * (waveModeEvolution (lambda i) t (data i)).1) • e i

/-- Differentiating a finite spectral displacement gives its velocity. -/
theorem hasDerivAt_finiteSpectralDisplacement (lambda : ι → ℝ) (e : ι → V)
    (s : Finset ι) (data : ι → ℝ × ℝ) (t : ℝ) :
    HasDerivAt (finiteSpectralDisplacement lambda e s data)
      (finiteSpectralVelocity lambda e s data t) t :=
  HasDerivAt.fun_sum fun i _ ↦
    (hasDerivAt_waveModeDisplacement (lambda i) (data i) t).smul_const (e i)

/-- Differentiating the finite spectral velocity gives the acceleration used
in the variational equation. -/
theorem hasDerivAt_finiteSpectralVelocity (lambda : ι → ℝ) (e : ι → V)
    (s : Finset ι) (data : ι → ℝ × ℝ) (t : ℝ) :
    HasDerivAt (finiteSpectralVelocity lambda e s data)
      (finiteSpectralAcceleration lambda e s data t) t :=
  HasDerivAt.fun_sum fun i _ ↦ (hasDerivAt_waveModeVelocity (lambda i) (data i) t).smul_const (e i)

/-- At time zero, finite displacement is the prescribed spectral truncation. -/
@[simp]
theorem finiteSpectralDisplacement_zero (lambda : ι → ℝ) (e : ι → V)
    (s : Finset ι) (data : ι → ℝ × ℝ) :
    finiteSpectralDisplacement lambda e s data 0 = ∑ i ∈ s, (data i).1 • e i := by
  simp only [finiteSpectralDisplacement, waveModeEvolution_zero, ContinuousLinearMap.id_apply]

/-- At time zero, finite velocity is the prescribed spectral truncation. -/
@[simp]
theorem finiteSpectralVelocity_zero (lambda : ι → ℝ) (e : ι → V) (s : Finset ι) (data : ι → ℝ × ℝ) :
    finiteSpectralVelocity lambda e s data 0 = ∑ i ∈ s, (data i).2 • e i := by
  simp only [finiteSpectralVelocity, waveModeEvolution_zero, ContinuousLinearMap.id_apply]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A finite sum of weak eigenmodes solves the full ambient variational wave
equation. The test `w` is arbitrary in `V`. -/
theorem finiteSpectralWave_equation (B : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H) (lambda : ι → ℝ)
    (e : ι → V) (hweak : ∀ i w, B (e i) w = lambda i * ⟪J (e i), J w⟫_ℝ) (s : Finset ι)
    (data : ι → ℝ × ℝ) (t : ℝ) (w : V) :
    ⟪J (finiteSpectralAcceleration lambda e s data t), J w⟫_ℝ +
      B (finiteSpectralDisplacement lambda e s data t) w = 0 := by
  simp only [finiteSpectralAcceleration, finiteSpectralDisplacement,
    map_sum, map_smul, sum_inner, real_inner_smul_left, sum_apply, smul_apply, smul_eq_mul, hweak]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun _ _ ↦ by ring

/-- Both components of a finite wave are continuous in the energy topology. -/
theorem continuous_finiteSpectralWave (J : V →L[ℝ] H) (lambda : ι → ℝ) (e : ι → V) (s : Finset ι)
    (data : ι → ℝ × ℝ) :
    Continuous fun t ↦ (finiteSpectralDisplacement lambda e s data t,
      J (finiteSpectralVelocity lambda e s data t)) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  exact (hasDerivAt_finiteSpectralDisplacement lambda e s data t).continuousAt.prodMk
    (J.continuous.continuousAt.comp
      (hasDerivAt_finiteSpectralVelocity lambda e s data t).continuousAt)

end Hyperbolic.Variational
