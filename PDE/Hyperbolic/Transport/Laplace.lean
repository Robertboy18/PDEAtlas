/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Laplace.Inversion
public import PDE.Analysis.Laplace.Operational

/-!
# Laplace representation of boundary-driven transport

A causal boundary pulse `g` enters the half-line at unit speed: `u(t,x) = g(t-x)`.
The solution satisfies `u_t + u_x = 0`, has zero initial data for nonnegative
positions, and takes the boundary value `g`. Its time Laplace transform is
`exp(-s*x) * transform g s`. For smooth compactly supported pulses, vertical-line
inversion reconstructs the solution by an absolutely convergent integral.

`transform` is the Laplace transform (43) of Evans, §4.3.3, for complex `s`, and we apply it in
`t` with `x` fixed, as Evans suggests there for equations involving time. Since the initial data
vanish, the transport equation becomes the ODE `s û + û_x = 0` in `x`
(`transform_time_deriv_boundarySolution`, `hasDerivAt_transformed_boundarySolution`), whose
solution with boundary value `transform g s` is `exp(-s*x) * transform g s`. Evans's Example 8
applies the same step to the heat equation (44), which becomes the resolvent equation (45).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.3, Definition (43) and Example 8, equations (44)-(45).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set Complex
open scoped ContDiff

namespace PDE.Hyperbolic.Transport

open PDE.Analysis.Laplace

/-- The unit-speed solution with a prescribed boundary signal. Causality of the
signal gives zero initial data on the positive spatial half-line. -/
def boundarySolution (g : ℝ → ℂ) (t x : ℝ) : ℂ := g (t - x)

/-- The boundary trace equals the prescribed signal. -/
@[simp] theorem boundarySolution_boundary (g : ℝ → ℂ) (t : ℝ) :
    boundarySolution g t 0 = g t := by simp [boundarySolution]

/-- Causal boundary data produce zero initial data on the half-line. -/
theorem boundarySolution_initial {g : ℝ → ℂ} (hg : ∀ t ≤ 0, g t = 0)
    {x : ℝ} (hx : 0 ≤ x) : boundarySolution g 0 x = 0 :=
  hg (0 - x) (sub_nonpos.mpr hx)

/-- The characteristic solution satisfies the transport equation classically. -/
theorem boundarySolution_transport {g : ℝ → ℂ} (hg : Differentiable ℝ g) (t x : ℝ) :
    deriv (fun τ ↦ boundarySolution g τ x) t + deriv (fun y ↦ boundarySolution g t y) x = 0 := by
  have ht := (hg (t - x)).hasDerivAt.scomp t ((hasDerivAt_id t).sub_const x)
  have hx := (hg (t - x)).hasDerivAt.scomp x ((hasDerivAt_id x).const_sub t)
  simp only [one_smul] at ht
  simp only [neg_smul, one_smul] at hx
  rw [show deriv (fun τ ↦ boundarySolution g τ x) t = deriv g (t - x) from ht.deriv]
  rw [show deriv (fun y ↦ boundarySolution g t y) x = -deriv g (t - x) from hx.deriv]
  exact add_neg_cancel _

/-- Spatial translation yields the delay factor in the time Laplace transform. -/
theorem transform_boundarySolution {g : ℝ → ℂ} (hg : ∀ t ≤ 0, g t = 0)
    {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    transform (fun t ↦ boundarySolution g t x) s = exp (-s * x) * transform g s := by
  have hcausal : ∀ t ≤ 0, boundarySolution g t x = 0 :=
    fun t ht ↦ hg (t - x) (sub_nonpos.mpr (ht.trans hx))
  rw [transform_eq_integral hcausal, transform_eq_integral hg]
  simp only [smul_eq_mul, boundarySolution]
  calc
    (∫ t : ℝ, exp (-s * t) * g (t - x)) =
        ∫ t : ℝ, exp (-s * x) * (exp (-s * (t - x : ℝ)) * g (t - x)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [← mul_assoc, ← exp_add]
      congr 2
      push_cast
      ring
    _ = exp (-s * x) * (∫ t : ℝ, exp (-s * (t - x : ℝ)) * g (t - x)) := integral_const_mul _ _
    _ = exp (-s * x) * (∫ t : ℝ, exp (-s * t) * g t) := by
      rw [integral_sub_right_eq_self (fun t : ℝ ↦ exp (-s * t) * g t) x]

/-- Operational calculus transforms the time derivative with zero initial term.
This is the time part of the transformed transport equation. -/
theorem transform_time_deriv_boundarySolution {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (hzero : ∀ t ≤ 0, g t = 0) {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    transform (deriv (fun t ↦ boundarySolution g t x)) s = s * (exp (-s * x) * transform g s) := by
  have hs : ContDiff ℝ 1 (fun t ↦ boundarySolution g t x) :=
    hg.comp (contDiff_id.sub contDiff_const)
  have hsupport : HasCompactSupport (fun t ↦ boundarySolution g t x) :=
    hc.comp_homeomorph (Homeomorph.subRight x)
  rw [transform_deriv_of_hasCompactSupport hs hsupport,
    transform_boundarySolution hzero hx, boundarySolution_initial hzero hx, sub_zero]

/-- The transformed solution solves the spatial resolvent ODE with coefficient `s`.
This verifies the equation underlying the Laplace representation. -/
theorem hasDerivAt_transformed_boundarySolution (g : ℝ → ℂ) (s : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ exp (-s * y) * transform g s)
      (-s * (exp (-s * x) * transform g s)) x := by
  convert ((((hasDerivAt_id x).ofReal_comp).const_mul (-s)).cexp.const_mul (transform g s)) using 1
  · ext y
    simp only [id_eq]
    ring
  · simp only [id_eq, ofReal_one]
    ring

/-- Laplace inversion reconstructs the solution to the zero-initial-data
transport problem from its boundary signal. Smooth compact support supplies absolute
convergence, for every real abscissa `a`. -/
theorem boundarySolution_laplace_representation {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hzero : ∀ t ≤ 0, g t = 0) (a : ℝ) {t x : ℝ} (ht : 0 < t) (hx : 0 ≤ x) :
    boundarySolution g t x = exp ((a : ℂ) * t) * ∫ ξ : ℝ, exp ((2 * Real.pi * ξ * t : ℝ) * I) *
      (exp (-((a : ℂ) + (2 * Real.pi * ξ : ℝ) * I) * x) *
      transform g ((a : ℂ) + (2 * Real.pi * ξ : ℝ) * I)) := by
  have hs : ContDiff ℝ ∞ (fun τ ↦ boundarySolution g τ x) :=
    hg.comp (contDiff_id.sub contDiff_const)
  have hsupport : HasCompactSupport (fun τ ↦ boundarySolution g τ x) :=
    hc.comp_homeomorph (Homeomorph.subRight x)
  have hz : ∀ τ ≤ 0, boundarySolution g τ x = 0 :=
    fun τ hτ ↦ hzero (τ - x) (sub_nonpos.mpr (hτ.trans hx))
  have hi := inversion_of_contDiff_hasCompactSupport hs hsupport hz a ht
  simpa only [transform_boundarySolution hzero hx, smul_eq_mul] using hi

end PDE.Hyperbolic.Transport
