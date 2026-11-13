/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Derivative of the forward polar chart

Mathlib provides the derivative of `(r, θ) ↦ (r cos θ, r sin θ)`. Inverting
that linear map gives the derivative of the forward polar chart. We write the
inverse matrix explicitly and use Mathlib's inverse-chart theorem to justify
it on the chart's source. The invertible derivative also proves C² regularity
of the forward chart. The factors `1 / r` explain why the origin is excluded.
-/

@[expose] public section

noncomputable section

open scoped Matrix

namespace PDE.FDeriv

/--
Forward derivative of `polarCoord`, derived from mathlib's derivative of the
inverse chart.

Given `fderivPolarCoordSymm p` as a continuous linear equivalence `E`, the
forward chart has derivative `E.symm` by `OpenPartialHomeomorph.hasFDerivAt_symm`.
-/
theorem polarCoord_hasFDerivAt_of_symm_fderiv_equiv
    {p : ℝ × ℝ} (hp : p ∈ polarCoord.target)
    (E : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hE : (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) = fderivPolarCoordSymm p) :
    HasFDerivAt (fun q : ℝ × ℝ ↦ polarCoord q)
      (E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (polarCoord.symm p) := by
  have hsymm0 : HasFDerivAt (fun q : ℝ × ℝ ↦ polarCoord.symm q)
      (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    change HasFDerivAt (polarCoord.symm : ℝ × ℝ → ℝ × ℝ)
      (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p
    rw [hE]
    exact hasFDerivAt_polarCoord_symm p
  have hback : polarCoord (polarCoord.symm p) = p := polarCoord.right_inv hp
  have hsymm : HasFDerivAt (fun q : ℝ × ℝ ↦ polarCoord.symm q)
      (E : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
      (polarCoord.symm.symm (polarCoord.symm p)) := by
    rw [show polarCoord.symm.symm (polarCoord.symm p) = p by simpa using hback]
    exact hsymm0
  have ha : polarCoord.symm p ∈ polarCoord.source := polarCoord.map_target hp
  have h :=
    (polarCoord.symm).hasFDerivAt_symm (f' := E) (a := polarCoord.symm p) ha hsymm
  change HasFDerivAt (fun q : ℝ × ℝ ↦ polarCoord q)
      (E.symm : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (polarCoord.symm p)
  exact h

/--
Explicit inverse of `fderivPolarCoordSymm`.

For `p = (r, θ)`, mathlib proves that the inverse polar chart has derivative

`(δr,δθ) ↦ (cos θ δr - r sin θ δθ, sin θ δr + r cos θ δθ)`.

Away from `r = 0`, the inverse matrix is

`(δR,δZ) ↦ (cos θ δR + sin θ δZ,
             -sin θ/r δR + cos θ/r δZ)`.
-/
def polarCoordForwardFDeriv (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![Real.cos p.2, Real.sin p.2;
       -(p.1)⁻¹ * Real.sin p.2, (p.1)⁻¹ * Real.cos p.2]).toContinuousLinearMap

/-- For `r ≠ 0` the explicit matrix `polarCoordForwardFDeriv p` inverts
`fderivPolarCoordSymm p` on the left. The computation reduces to `cos² θ + sin² θ = 1`
after clearing the factor `r`. -/
theorem polarCoordForwardFDeriv_leftInverse
    (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    Function.LeftInverse (polarCoordForwardFDeriv p) (fderivPolarCoordSymm p) := by
  intro v
  unfold polarCoordForwardFDeriv fderivPolarCoordSymm
  ext <;> simp only [neg_mul, LinearMap.coe_toContinuousLinearMap',
    Matrix.toLin_finTwoProd_apply]
  · calc
      Real.cos p.2 * (Real.cos p.2 * v.1 + -(p.1 * Real.sin p.2 * v.2)) +
          Real.sin p.2 * (Real.sin p.2 * v.1 + p.1 * Real.cos p.2 * v.2)
          = v.1 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
      _ = v.1 := by rw [Real.cos_sq_add_sin_sq]; ring
  · field_simp [hp]
    calc
      -(Real.sin p.2 * (Real.cos p.2 * v.1 + -(p.1 * Real.sin p.2 * v.2))) +
          Real.cos p.2 * (Real.sin p.2 * v.1 + p.1 * Real.cos p.2 * v.2)
          = p.1 * v.2 * (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) := by ring
      _ = p.1 * v.2 := by rw [Real.sin_sq_add_cos_sq]; ring

/-- For `r ≠ 0` the explicit matrix `polarCoordForwardFDeriv p` inverts
`fderivPolarCoordSymm p` on the right as well, so the two maps are mutually inverse. -/
theorem polarCoordForwardFDeriv_rightInverse
    (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    Function.RightInverse (polarCoordForwardFDeriv p) (fderivPolarCoordSymm p) := by
  intro v
  unfold polarCoordForwardFDeriv fderivPolarCoordSymm
  ext <;> simp
  · field_simp [hp]
    calc
      Real.cos p.2 * (Real.cos p.2 * v.1 + Real.sin p.2 * v.2) +
          -(Real.sin p.2 * (-(v.1 * Real.sin p.2) + Real.cos p.2 * v.2))
          = v.1 * (Real.cos p.2 ^ 2 + Real.sin p.2 ^ 2) := by ring
      _ = v.1 := by rw [Real.cos_sq_add_sin_sq]; ring
  · field_simp [hp]
    calc
      Real.sin p.2 * (Real.cos p.2 * v.1 + Real.sin p.2 * v.2) +
          Real.cos p.2 * (-(Real.sin p.2 * v.1) + Real.cos p.2 * v.2)
          = v.2 * (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) := by ring
      _ = v.2 := by rw [Real.sin_sq_add_cos_sq]; ring

/-- Linear equivalence form of the inverse polar-chart derivative away from `r = 0`. -/
def polarCoordSymmFDerivLinearEquiv
    (p : ℝ × ℝ) (hp : p.1 ≠ 0) : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  LinearEquiv.mk (fderivPolarCoordSymm p).toLinearMap (polarCoordForwardFDeriv p)
    (polarCoordForwardFDeriv_leftInverse p hp)
    (polarCoordForwardFDeriv_rightInverse p hp)

/--
Continuous linear equivalence form of the inverse polar-chart derivative away
from `r = 0`.
-/
def polarCoordSymmFDerivEquiv
    (p : ℝ × ℝ) (hp : p.1 ≠ 0) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.mk (polarCoordSymmFDerivLinearEquiv p hp)
    (fderivPolarCoordSymm p).continuous
    (polarCoordForwardFDeriv p).continuous

/-- The forward map of `polarCoordSymmFDerivEquiv` is `fderivPolarCoordSymm p`. -/
@[simp] theorem polarCoordSymmFDerivEquiv_coe
    (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    (polarCoordSymmFDerivEquiv p hp : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) =
      fderivPolarCoordSymm p := rfl

/-- The inverse of `polarCoordSymmFDerivEquiv` is the explicit matrix
`polarCoordForwardFDeriv p`. -/
@[simp] theorem polarCoordSymmFDerivEquiv_symm_coe
    (p : ℝ × ℝ) (hp : p.1 ≠ 0) :
    ((polarCoordSymmFDerivEquiv p hp).symm :
        (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) =
      polarCoordForwardFDeriv p := by
  ext <;> rfl

/-- Derivative of the forward polar chart at `polarCoord.symm p`, for `p = (r, θ)` in
the chart's target (so `r > 0`): it is the explicit inverse matrix
`polarCoordForwardFDeriv p`. This discharges the hypothesis `hpolar` of
`profileFromPolar_hasFDerivAt`. -/
theorem polarCoord_hasFDerivAt_symm_point
    {p : ℝ × ℝ} (hp_target : p ∈ polarCoord.target) :
    HasFDerivAt (fun q : ℝ × ℝ ↦ polarCoord q)
      (polarCoordForwardFDeriv p) (polarCoord.symm p) := by
  have hp_nonzero : p.1 ≠ 0 := ne_of_gt hp_target.1
  simpa using
    polarCoord_hasFDerivAt_of_symm_fderiv_equiv hp_target
      (polarCoordSymmFDerivEquiv p hp_nonzero)
      (polarCoordSymmFDerivEquiv_coe p hp_nonzero)

private theorem contDiff_two_polarCoord_symm : ContDiff ℝ 2 polarCoord.symm := by
  change ContDiff ℝ 2
    (fun p : ℝ × ℝ ↦ (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
  fun_prop

/-- The forward polar chart is C² on its source by the inverse-Jacobian theorem. -/
theorem contDiffAt_two_polarCoord
    {x : ℝ × ℝ} (hx : x ∈ polarCoord.source) : ContDiffAt ℝ 2 polarCoord x := by
  let p := polarCoord x
  have hp : p ∈ polarCoord.target := polarCoord.map_source hx
  have hr : p.1 ≠ 0 := ne_of_gt hp.1
  have hderiv : HasFDerivAt (polarCoord.symm : (ℝ × ℝ) → ℝ × ℝ)
      (polarCoordSymmFDerivEquiv p hr : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) p := by
    rw [polarCoordSymmFDerivEquiv_coe]
    exact hasFDerivAt_polarCoord_symm p
  exact (polarCoord.symm).contDiffAt_symm hx hderiv
    contDiff_two_polarCoord_symm.contDiffAt

end PDE.FDeriv
