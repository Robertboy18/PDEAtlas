/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import PDE.Common.Euclidean
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Scalar virial horizon for two-dimensional Keller–Segel

For the parabolic–elliptic Keller–Segel system on `ℝ^2`, with chemotactic sensitivity normalized
to one and the Newtonian potential fixed by

`Φ(x,t) = -(2π)⁻¹ ∫ log ‖x - y‖ u(y,t) dy`,

the formal second-moment identity is

`I'(t) = 4 M - M² / (2π)`.

The equation `-ΔΦ = u` alone determines `Φ` only up to a harmonic function. The displayed
coefficient therefore also depends on this Newtonian normalization and on the decay and
integration-by-parts hypotheses used to derive the identity. We take the identity as a
hypothesis rather than deriving it from the elliptic equation.

When `M > 8π`, the right-hand side is negative. We prove the scalar consequence: a continuous,
differentiable, nonnegative function satisfying that identity on `[0, T]` must have

`T ≤ I(0) / (M² / (2π) - 4 M)`.

So such a second moment cannot stay nonnegative on an interval reaching strictly past the virial
horizon. The density-level version `right_endpoint_le_horizon_of_density` follows. Mathlib's
Bochner integral of a nonintegrable function is zero, so that theorem assumes a finite quadratic
moment on every time slice in `[0, T]`. Integrability of the density slices comes for free: the
conserved supercritical mass is nonzero, and `MeasureTheory.Integrable.of_integral_ne_zero`
applies. Mass conservation and the virial identity then reduce the density statement to the
scalar one. Mass conservation and the virial identity are hypotheses of both theorems.

The potential is (2.3) of Blanchet, Dolbeault and Perthame, the identity is their Lemma 2.1
with `χ = 1`, and the horizon is their bound `T* ≤ 2π I₀ / (M (χ M - 8π))` of Corollary 2.2.
They credit the critical mass above which solutions blow up in finite time to Jäger and
Luckhaus.

## References

* W. Jäger and S. Luckhaus, "On explosions of solutions to a system of partial differential
  equations modelling chemotaxis", *Trans. Amer. Math. Soc.* 329 (1992), 819-824.
  <https://doi.org/10.1090/S0002-9947-1992-1046835-6>
* A. Blanchet, J. Dolbeault and B. Perthame, "Two-dimensional Keller–Segel model: optimal
  critical mass and qualitative properties of the solutions", *Electron. J. Differential
  Equations* 2006, No. 44, 1-33, (2.3), Lemma 2.1 and Corollary 2.2.
  <https://ejde.math.txstate.edu/Volumes/2006/44/blanchet.pdf>
-/

@[expose] public section

open Set

namespace PDE.Solution.Singularity.FiniteTime.KellerSegel.Virial

/-- Total mass of a time-dependent density at time `t`.

This is Mathlib's Bochner integral, which is zero for a nonintegrable function. Reading
`massAt u t` as a finite mass requires `u · t` to be integrable; a nonzero value of `massAt u t`
implies this by `MeasureTheory.Integrable.of_integral_ne_zero`. -/
noncomputable def massAt {d : ℕ} (u : ℝ^d → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, u x t

/-- Quadratic spatial moment of a time-dependent density at time `t`.

As with `massAt`, a nonintegrable integrand gives `0`. A finite second moment is expressed by
integrability of `fun x ↦ ‖x‖ ^ 2 * u x t`. -/
noncomputable def secondMomentAt {d : ℕ} (u : ℝ^d → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x, ‖x‖ ^ 2 * u x t

/-- A pointwise nonnegative density with finite quadratic moment has nonnegative second moment. -/
theorem second_moment_at_nonneg
    {d : ℕ} {u : ℝ^d → ℝ → ℝ} {t : ℝ}
    (hintegrable : MeasureTheory.Integrable (fun x ↦ ‖x‖ ^ 2 * u x t))
    (hu : ∀ x, 0 ≤ u x t) :
    0 ≤ secondMomentAt u t := by
  unfold secondMomentAt
  have hzero :
      MeasureTheory.Integrable (fun _ : ℝ^d ↦ (0 : ℝ)) :=
    MeasureTheory.integrable_zero (ℝ^d) ℝ MeasureTheory.volume
  have hnonnegative :
      (fun _ : ℝ^d ↦ (0 : ℝ)) ≤ fun x ↦ ‖x‖ ^ 2 * u x t := by
    intro x
    exact mul_nonneg (sq_nonneg ‖x‖) (hu x)
  simpa using MeasureTheory.integral_mono hzero hintegrable hnonnegative

/-- The positive decay rate of the second moment in the supercritical-mass regime.

With sensitivity normalized to one, the virial identity reads `I' = -decayRate M`. -/
noncomputable def decayRate (M : ℝ) : ℝ :=
  M ^ 2 / (2 * Real.pi) - 4 * M

/-- The algebraic virial horizon `I₀ / decayRate M`.

It is the zero-crossing time of the affine virial law when the decay rate is nonzero; the
supercritical-mass theorems below establish the positive-rate case used in applications. -/
noncomputable def horizon (M I₀ : ℝ) : ℝ :=
  I₀ / decayRate M

/-- Above the critical mass `8π`, the second-moment decay rate is strictly positive. -/
theorem decay_rate_pos {M : ℝ} (hM : 8 * Real.pi < M) :
    0 < decayRate M := by
  have hM_pos : 0 < M := lt_trans (mul_pos (by norm_num) Real.pi_pos) hM
  have hscaled := mul_lt_mul_of_pos_left hM hM_pos
  rw [decayRate, sub_pos]
  apply (lt_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)).2
  nlinarith

/-- The virial identity integrates exactly to affine second-moment decay on `[0, T]`.

No mass-sign assumption is needed for this identity. The supercritical condition enters only
when `decayRate M` must be positive in the continuation-time estimate. -/
theorem second_moment_eq_affine
    {secondMoment : ℝ → ℝ} {M T t : ℝ}
    (ht : t ∈ Icc 0 T)
    (hcontinuous : ContinuousOn secondMoment (Icc 0 T))
    (hdifferentiable : DifferentiableOn ℝ secondMoment (Ioo 0 T))
    (hderiv : ∀ s ∈ Ioo 0 T,
      deriv secondMoment s = 4 * M - M ^ 2 / (2 * Real.pi)) :
    secondMoment t = secondMoment 0 - decayRate M * t := by
  have hT : 0 ≤ T :=
    le_trans ht.1 ht.2
  have hdifferentiable' :
      DifferentiableOn ℝ secondMoment (interior (Icc 0 T)) := by
    simpa only [interior_Icc] using hdifferentiable
  have hderiv_eq :
      ∀ s ∈ interior (Icc 0 T), deriv secondMoment s = -decayRate M := by
    intro s hs
    rw [interior_Icc] at hs
    calc
      deriv secondMoment s = 4 * M - M ^ 2 / (2 * Real.pi) := hderiv s hs
      _ = -decayRate M := by
        rw [decayRate]
        ring
  have hlower :=
    (convex_Icc (0 : ℝ) T).mul_sub_le_image_sub_of_le_deriv
      hcontinuous hdifferentiable'
      (fun s hs ↦ (hderiv_eq s hs).ge)
      0 (left_mem_Icc.mpr hT) t ht ht.1
  have hupper :=
    (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le
      hcontinuous hdifferentiable'
      (fun s hs ↦ (hderiv_eq s hs).le)
      0 (left_mem_Icc.mpr hT) t ht ht.1
  nlinarith

/-- If the interval extends strictly beyond the virial horizon, the affine virial law forces
the second moment to be negative at its right endpoint.

This is the form the virial argument uses: for a PDE solution it only remains to show that the
second moment is nonnegative at `T`. -/
theorem second_moment_neg_of_horizon_lt
    {secondMoment : ℝ → ℝ} {M T : ℝ}
    (hM : 8 * Real.pi < M)
    (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn secondMoment (Icc 0 T))
    (hdifferentiable : DifferentiableOn ℝ secondMoment (Ioo 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T,
      deriv secondMoment t = 4 * M - M ^ 2 / (2 * Real.pi))
    (hhorizon : horizon M (secondMoment 0) < T) :
    secondMoment T < 0 := by
  have hdecay : 0 < decayRate M :=
    decay_rate_pos hM
  have hmoment :=
    second_moment_eq_affine (right_mem_Icc.mpr hT)
      hcontinuous hdifferentiable hderiv
  have hinitial : secondMoment 0 < decayRate M * T := by
    rw [horizon] at hhorizon
    simpa only [mul_comm] using (div_lt_iff₀ hdecay).1 hhorizon
  rw [hmoment]
  linarith

/-- If a nonnegative second moment satisfies the two-dimensional virial identity on `[0, T]`,
then the right endpoint `T` is at most the virial horizon.

This is a scalar theorem. In an application, `secondMoment` is the spatial second moment of a
Keller–Segel solution, and each analytic hypothesis below has to be proved from the PDE. `T` is
any right endpoint, not necessarily a maximal existence time. -/
theorem right_endpoint_le_horizon
    {secondMoment : ℝ → ℝ} {M T : ℝ}
    (hM : 8 * Real.pi < M)
    (hT : 0 ≤ T)
    (hcontinuous : ContinuousOn secondMoment (Icc 0 T))
    (hdifferentiable : DifferentiableOn ℝ secondMoment (Ioo 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T,
      deriv secondMoment t = 4 * M - M ^ 2 / (2 * Real.pi))
    (hnonnegative : 0 ≤ secondMoment T) :
    T ≤ horizon M (secondMoment 0) := by
  by_contra hhorizon
  have hnegative :=
    second_moment_neg_of_horizon_lt hM hT hcontinuous hdifferentiable hderiv
      (lt_of_not_ge hhorizon)
  exact (not_lt_of_ge hnonnegative) hnegative

/-- A density-level virial law with finite mass and finite quadratic moment bounds the right
endpoint of its interval by the virial horizon.

The hypotheses are finite quadratic moments on `[0, T]`, conserved supercritical mass, regularity
of the second moment, and the differentiated virial identity. By
`MeasureTheory.Integrable.of_integral_ne_zero`, the nonzero conserved mass also entails
integrability of every density slice. Nonnegativity is needed only for the slice at `T`, where it
gives the scalar contradiction through `second_moment_at_nonneg`. As in
`right_endpoint_le_horizon`, `T` need not be a maximal existence time. -/
theorem right_endpoint_le_horizon_of_density
    {u : ℝ^2 → ℝ → ℝ} {M T : ℝ}
    (hM : 8 * Real.pi < M)
    (hT : 0 ≤ T)
    (hsecondMomentIntegrable :
      ∀ t ∈ Icc 0 T, MeasureTheory.Integrable (fun x ↦ ‖x‖ ^ 2 * u x t))
    (hmass : ∀ t ∈ Icc 0 T, massAt u t = M)
    (hcontinuous : ContinuousOn (secondMomentAt u) (Icc 0 T))
    (hdifferentiable : DifferentiableOn ℝ (secondMomentAt u) (Ioo 0 T))
    (hvirial : ∀ t ∈ Ioo 0 T,
      deriv (secondMomentAt u) t =
        4 * massAt u t - massAt u t ^ 2 / (2 * Real.pi))
    (hnonnegativeAtEndpoint : ∀ x, 0 ≤ u x T) :
    T ≤ horizon M (secondMomentAt u 0) := by
  refine right_endpoint_le_horizon hM hT hcontinuous hdifferentiable ?_
    (second_moment_at_nonneg
      (hsecondMomentIntegrable T (right_mem_Icc.mpr hT))
      hnonnegativeAtEndpoint)
  intro t ht
  rw [hvirial t ht, hmass t ⟨ht.1.le, ht.2.le⟩]

end PDE.Solution.Singularity.FiniteTime.KellerSegel.Virial
