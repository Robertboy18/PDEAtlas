/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.MixedDerivatives

/-!
# Mixed derivatives of the axisymmetric elliptic equation

For the radial operator `∂ᵣ² + (3 / r) ∂ᵣ + ∂𝓏²`, multiplication by `r`
removes the singular coefficient. Differentiating this multiplied equation gives
principal mixed derivatives and the two lower-order Leibniz terms. The proofs use
only the local equation and the one-variable regularity displayed in each statement;
they do not divide by the radius or assume an already differentiated equation.
-/

@[expose] public section

open Filter
open scoped Topology
open PDE.Analysis (derivX derivY)

namespace SobolevSpace.Weighted

/-- Differentiating the radial elliptic row produces exactly the four terms
from the radial equation: two principal terms with a radial multiplier and the two
lower-order Leibniz terms with coefficient equal to the radial derivative
count.  The elliptic identity is required only in a neighborhood of the
evaluation point; no differentiated identity is assumed.
-/
theorem mixedIteratedDeriv2D_radialEllipticRow_expansion
    (q ell : ℕ) (psi omega : ℝ → ℝ → ℝ) (r z : ℝ)
    (hrow : ∀ᶠ rho in nhds r, ∀ xi,
      3 * derivX psi rho xi +
          rho * derivX (derivX psi) rho xi =
        -(rho * omega rho xi +
          rho * derivY (derivY psi) rho xi))
    (homegaZ : ∀ rho, ContDiffAt ℝ ell (omega rho) z)
    (hpsiZZZ : ∀ rho, ContDiffAt ℝ ell
      (derivY (derivY psi) rho) z)
    (homegaR : ContDiffAt ℝ (q + 1)
      (fun rho ↦ iteratedDeriv ell (omega rho) z) r)
    (hpsiZZR : ContDiffAt ℝ (q + 1)
      (fun rho ↦ iteratedDeriv ell
        (derivY (derivY psi) rho) z) r) :
    mixedIteratedDeriv2D (q + 1) ell
        (fun rho xi ↦ 3 * derivX psi rho xi +
          rho * derivX (derivX psi) rho xi) r z =
      -(r * mixedIteratedDeriv2D (q + 1) ell omega r z) -
        (q + 1 : ℝ) * mixedIteratedDeriv2D q ell omega r z -
        r * mixedIteratedDeriv2D (q + 1) (ell + 2) psi r z -
        (q + 1 : ℝ) * mixedIteratedDeriv2D q (ell + 2) psi r z := by
  let psiZZ : ℝ → ℝ → ℝ :=
    derivY (derivY psi)
  let omegaR : ℝ → ℝ → ℝ := fun rho xi ↦ rho * omega rho xi
  let psiZZR : ℝ → ℝ → ℝ := fun rho xi ↦ rho * psiZZ rho xi
  have hmixed :
      mixedIteratedDeriv2D (q + 1) ell
          (fun rho xi ↦ 3 * derivX psi rho xi +
            rho * derivX (derivX psi) rho xi) r z =
        mixedIteratedDeriv2D (q + 1) ell
          (fun rho xi ↦ -(omegaR rho xi + psiZZR rho xi)) r z := by
    simp only [mixedIteratedDeriv2D]
    apply Filter.EventuallyEq.iteratedDeriv_eq (q + 1)
    filter_upwards [hrow] with rho hrho
    apply Filter.EventuallyEq.iteratedDeriv_eq ell
    filter_upwards [] with xi
    simpa [omegaR, psiZZR, psiZZ] using hrho xi
  have homegaRZ : ∀ rho, ContDiffAt ℝ ell (omegaR rho) z := by
    intro rho
    simpa [omegaR] using contDiffAt_const.mul (homegaZ rho)
  have hpsiZZRZ : ∀ rho, ContDiffAt ℝ ell (psiZZR rho) z := by
    intro rho
    simpa [psiZZR, psiZZ] using contDiffAt_const.mul (hpsiZZZ rho)
  have homegaRR : ContDiffAt ℝ (q + 1)
      (fun rho ↦ iteratedDeriv ell (omegaR rho) z) r := by
    have heq : (fun rho ↦ iteratedDeriv ell (omegaR rho) z) =
        fun rho ↦ rho * iteratedDeriv ell (omega rho) z := by
      funext rho
      exact iteratedDeriv_const_mul_field rho (omega rho)
    rw [heq]
    exact contDiffAt_id.mul homegaR
  have hpsiZZRR : ContDiffAt ℝ (q + 1)
      (fun rho ↦ iteratedDeriv ell (psiZZR rho) z) r := by
    have heq : (fun rho ↦ iteratedDeriv ell (psiZZR rho) z) =
        fun rho ↦ rho * iteratedDeriv ell (psiZZ rho) z := by
      funext rho
      exact iteratedDeriv_const_mul_field rho (psiZZ rho)
    rw [heq]
    exact contDiffAt_id.mul (by simpa only [psiZZ] using hpsiZZR)
  rw [hmixed, mixedIteratedDeriv2D_neg]
  rw [mixedIteratedDeriv2D_add (q + 1) ell omegaR psiZZR r z
    homegaRZ hpsiZZRZ homegaRR hpsiZZRR]
  rw [mixedIteratedDeriv2D_radial_mul_succ q ell omega r z homegaR]
  have hpsiProduct := mixedIteratedDeriv2D_radial_mul_succ
    q ell psiZZ r z (by simpa only [psiZZ] using hpsiZZR)
  rw [show mixedIteratedDeriv2D (q + 1) ell psiZZR r z =
      r * mixedIteratedDeriv2D (q + 1) ell psiZZ r z +
        (q + 1 : ℝ) * mixedIteratedDeriv2D q ell psiZZ r z by
    simpa [psiZZR] using hpsiProduct]
  rw [mixedIteratedDeriv2D_axial_two (q + 1) ell psi r z,
    mixedIteratedDeriv2D_axial_two q ell psi r z]
  ring

/-- Endpoint of the differentiated radial elliptic row when the multi-index
contains no radial derivative.  Exactly the two multiplier terms remain.
Only the axial slices at the fixed radius `r` need the displayed regularity.
-/
theorem mixedIteratedDeriv2D_radialEllipticRow_expansion_zeroRadial
    (ell : ℕ) (psi omega : ℝ → ℝ → ℝ) (r z : ℝ)
    (hrow : ∀ xi,
      3 * derivX psi r xi +
          r * derivX (derivX psi) r xi =
        -(r * omega r xi +
          r * derivY (derivY psi) r xi))
    (homegaZ : ContDiffAt ℝ ell (omega r) z)
    (hpsiZZZ : ContDiffAt ℝ ell
      (derivY (derivY psi) r) z) :
    mixedIteratedDeriv2D 0 ell
        (fun rho xi ↦ 3 * derivX psi rho xi +
          rho * derivX (derivX psi) rho xi) r z =
      -(r * mixedIteratedDeriv2D 0 ell omega r z) -
        r * mixedIteratedDeriv2D 0 (ell + 2) psi r z := by
  let psiZZ : ℝ → ℝ → ℝ :=
    derivY (derivY psi)
  let omegaR : ℝ → ℝ → ℝ := fun rho xi ↦ rho * omega rho xi
  let psiZZR : ℝ → ℝ → ℝ := fun rho xi ↦ rho * psiZZ rho xi
  have hmixed :
      mixedIteratedDeriv2D 0 ell
          (fun rho xi ↦ 3 * derivX psi rho xi +
            rho * derivX (derivX psi) rho xi) r z =
        mixedIteratedDeriv2D 0 ell
          (fun rho xi ↦ -(omegaR rho xi + psiZZR rho xi)) r z := by
    simp only [mixedIteratedDeriv2D, iteratedDeriv_zero]
    apply Filter.EventuallyEq.iteratedDeriv_eq ell
    filter_upwards [] with xi
    simpa [omegaR, psiZZR, psiZZ] using hrow xi
  have homegaRZ : ContDiffAt ℝ ell (omegaR r) z := by
    simpa [omegaR] using contDiffAt_const.mul homegaZ
  have hpsiZZRZ : ContDiffAt ℝ ell (psiZZR r) z := by
    simpa [psiZZR, psiZZ] using contDiffAt_const.mul hpsiZZZ
  rw [hmixed, mixedIteratedDeriv2D_neg]
  rw [mixedIteratedDeriv2D_add_zero ell omegaR psiZZR r z
    homegaRZ hpsiZZRZ]
  rw [mixedIteratedDeriv2D_radial_mul_zero ell omega r z]
  rw [show mixedIteratedDeriv2D 0 ell psiZZR r z =
      r * mixedIteratedDeriv2D 0 ell psiZZ r z by
    simpa [psiZZR] using mixedIteratedDeriv2D_radial_mul_zero ell psiZZ r z]
  rw [mixedIteratedDeriv2D_axial_two 0 ell psi r z]
  ring


end SobolevSpace.Weighted
