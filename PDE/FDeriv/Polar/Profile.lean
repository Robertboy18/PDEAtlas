/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import PDE.Common.Euclidean.HalfSpace
public import PDE.CoordinateSystems.Polar
public import PDE.FDeriv.Operators
public import PDE.FDeriv.Polar.Chart
public import PDE.FDeriv.Axisymmetric.Profile
public import PDE.Common.Euclidean.SpaceTime.Scalar

/-!
# Polar formulas on the meridian plane

A scalar formula in polar coordinates becomes a function on the meridian plane by
composing with Mathlib's `polarCoord`. The chain-rule results here identify its
Fréchet and coordinate derivatives. The chart's domain matters: a round trip through
`polarCoord.symm` is justified only inside the chart's target.

The meridian coordinates `meridianR`, `meridianZ` come from `PDE.CoordinateSystems.Axisymmetric`,
the derivative of the forward polar chart from `PDE.FDeriv.Polar.Chart`, and the coordinate
derivative operators from `PDE.FDeriv.Axisymmetric.Profile`.

## Main results

* `polarCoord_source_polarizes` and `coordinateClosedHalfSpace_nonaxis_polarizes` represent
  points in the polar chart, including every point with positive radial coordinate.
* `profileFromPolar_hasFDerivAt` gives the chain rule for a scalar polar formula.
* `profileDR_profileFromPolar_eq` and `profileDZ_profileFromPolar_eq` specialize it to
  the radial and axial derivatives.
* `contDiffAt_profileFromPolar_rpow_mul`: a homogeneous profile `r^m f(β)` with `C²` angular
  factor `f` is `C²` at every point of the chart, for any real exponent `m`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 7.1, (7.1)-(7.2).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

open PDE.CoordinateSystems (planarPolarPoint)

noncomputable section

open scoped Matrix

open PDE.CoordinateSystems (meridianR meridianZ)
open PDE.Common (coordinateClosedHalfSpace)
open PDE.Common (pointPairEquiv)

namespace PDE.FDeriv

/-- `meridianR` of a polar point is `ρ cos θ`. -/
@[simp] theorem meridianR_polarPoint (ρ θ : ℝ) :
    meridianR (planarPolarPoint ρ θ) = ρ * Real.cos θ := by
  simp [meridianR]

/-- `meridianZ` of a polar point is `ρ sin θ`. -/
@[simp] theorem meridianZ_polarPoint (ρ θ : ℝ) :
    meridianZ (planarPolarPoint ρ θ) = ρ * Real.sin θ := by
  simp [meridianZ]

/-- The `(R,Z)` pair associated to a profile-plane point. -/
def pointPair (x : (ℝ^2)) : ℝ × ℝ :=
  (meridianR x, meridianZ x)

/-- `pointPair` as a continuous linear map. -/
def pointPairLinearMap : (ℝ^2) →L[ℝ] ℝ × ℝ :=
  ContinuousLinearMap.prod
    (EuclideanSpace.proj (0 : Fin 2) : (ℝ^2) →L[ℝ] ℝ)
    (EuclideanSpace.proj (1 : Fin 2) : (ℝ^2) →L[ℝ] ℝ)

/-- `pointPair` coincides, as a function, with the continuous linear map
`pointPairLinearMap`. -/
theorem pointPair_eq_pointPairLinearMap :
    pointPair = pointPairLinearMap := by
  funext x
  rfl

/-- The bundled coordinate equivalence has the existing coordinate-pair formula. -/
theorem pointPair_eq_pointPairEquiv :
    pointPair = pointPairEquiv := rfl

/-- The radius returned by the polar chart is the Euclidean norm, including at zero. -/
theorem polarCoord_pointPair_fst (x : ℝ^2) :
    (polarCoord (pointPair x)).1 = ‖x‖ := by
  have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  change Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2) = ‖x‖
  rw [← hnorm, Real.sqrt_sq (norm_nonneg x)]

/-- `pointPair` is linear, so it is its own Fréchet derivative at every point. -/
theorem pointPair_hasFDerivAt (x : (ℝ^2)) :
    HasFDerivAt pointPair pointPairLinearMap x := by
  rw [pointPair_eq_pointPairLinearMap]
  exact pointPairLinearMap.hasFDerivAt

/-- The coordinate pair of a polar point is `(ρ cos θ, ρ sin θ)`. -/
@[simp] theorem pointPair_polarPoint (ρ θ : ℝ) :
    pointPair (planarPolarPoint ρ θ) = (ρ * Real.cos θ, ρ * Real.sin θ) := by
  simp [pointPair]

/-- Read through `pointPair`, `planarPolarPoint` is Mathlib's inverse chart `polarCoord.symm`.
This holds for every `(ρ, θ)`, not only for pairs in the chart's target. -/
theorem pointPair_polarPoint_eq_polarCoord_symm (ρ θ : ℝ) :
    pointPair (planarPolarPoint ρ θ) = polarCoord.symm (ρ, θ) := by
  rw [pointPair_polarPoint, polarCoord_symm_apply]

/-- Two profile-plane points are equal if their `(R,Z)` coordinate pairs agree. -/
theorem point_eq_of_pointPair_eq {x y : (ℝ^2)} (h : pointPair x = pointPair y) :
    x = y := by
  ext i
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/--
Every point whose `(R,Z)` pair lies in mathlib's polar-coordinate source is
represented by some polar point in the target chart.
-/
theorem polarCoord_source_polarizes
    (x : (ℝ^2)) (hx : pointPair x ∈ polarCoord.source) :
    ∃ ρ θ : ℝ,
      (ρ, θ) ∈ polarCoord.target ∧ ρ ≠ 0 ∧ planarPolarPoint ρ θ = x := by
  let p := polarCoord (pointPair x)
  have hp_target : p ∈ polarCoord.target := polarCoord.map_source hx
  refine ⟨p.1, p.2, hp_target, ?_, ?_⟩
  · exact ne_of_gt hp_target.1
  · apply point_eq_of_pointPair_eq
    rw [pointPair_polarPoint_eq_polarCoord_symm]
    exact polarCoord.left_inv hx

/--
A point with positive radial coordinate lies in Mathlib's polar-coordinate source.
-/
theorem positive_meridianR_mem_polarCoord_source
    {x : (ℝ^2)} (hx : 0 < meridianR x) :
    pointPair x ∈ polarCoord.source := by
  left
  simpa [pointPair, meridianR] using hx

/--
Every non-axis point in the closed right half-plane has polar coordinates in
mathlib's target chart.
-/
theorem coordinateClosedHalfSpace_nonaxis_polarizes
    {x : (ℝ^2)} (hphys : x ∈ coordinateClosedHalfSpace 0) (haxis : meridianR x ≠ 0) :
    ∃ ρ θ : ℝ,
      (ρ, θ) ∈ polarCoord.target ∧ ρ ≠ 0 ∧ planarPolarPoint ρ θ = x := by
  have hpos : 0 < meridianR x := lt_of_le_of_ne' hphys haxis
  exact polarCoord_source_polarizes x (positive_meridianR_mem_polarCoord_source hpos)

/--
Turn a scalar polar formula into a profile on the `(R,Z)` plane using Mathlib's
polar-coordinate chart.

The profile operators act on this composition; their chain rules require
differentiability of both the polar formula and the chart at the chosen point.
-/
def profileFromPolar (F : ℝ → ℝ → ℝ) : (ℝ^2 → ℝ) :=
  fun x ↦
    let p := polarCoord (pointPair x)
    F p.1 p.2

/--
Chain rule for a polar scalar formula viewed as a profile.

If `F` has derivative `F'` at `polarCoord (pointPair x)` and the forward polar
chart has derivative `P'` at `pointPair x`, then `profileFromPolar F` has
derivative `(F'.comp P').comp pointPairLinearMap` at `x`.
-/
theorem profileFromPolar_hasFDerivAt
    (F : ℝ → ℝ → ℝ) (x : (ℝ^2))
    {F' : ℝ × ℝ →L[ℝ] ℝ} {P' : ℝ × ℝ →L[ℝ] ℝ × ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ ↦ F p.1 p.2) F'
      (polarCoord (pointPair x)))
    (hpolar : HasFDerivAt (fun q : ℝ × ℝ ↦ polarCoord q) P' (pointPair x)) :
    HasFDerivAt (profileFromPolar F)
      ((F'.comp P').comp pointPairLinearMap) x := by
  have hchart :
      HasFDerivAt (fun y : (ℝ^2) ↦ polarCoord (pointPair y))
        (P'.comp pointPairLinearMap) x := by
    simpa [Function.comp_def] using hpolar.comp x (pointPair_hasFDerivAt x)
  have h := hF.comp x hchart
  change HasFDerivAt
    (fun y : (ℝ^2) ↦ F (polarCoord (pointPair y)).1 (polarCoord (pointPair y)).2)
    ((F'.comp P').comp pointPairLinearMap) x
  exact h

/--
Coordinate form of `profileFromPolar_hasFDerivAt`: the partial derivative
`∂[i]` of a polar-generated profile, which is what `profileDR` and `profileDZ` use.
-/
theorem partialDeriv_profileFromPolar_eq
    (F : ℝ → ℝ → ℝ) (x : (ℝ^2)) (i : Fin 2)
    {F' : ℝ × ℝ →L[ℝ] ℝ} {P' : ℝ × ℝ →L[ℝ] ℝ × ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ ↦ F p.1 p.2) F'
      (polarCoord (pointPair x)))
    (hpolar : HasFDerivAt (fun q : ℝ × ℝ ↦ polarCoord q) P' (pointPair x)) :
    (∂[i] (profileFromPolar F)) x =
      ((F'.comp P').comp pointPairLinearMap)
        (EuclideanSpace.single i (1 : ℝ)) := by
  unfold partialDeriv
  rw [(profileFromPolar_hasFDerivAt F x hF hpolar).fderiv]

/-- Evaluating a polar-generated profile at `planarPolarPoint ρ θ` returns `F ρ θ`. The
hypothesis `(ρ, θ) ∈ polarCoord.target` is what makes the chart round-trip; outside the
target `polarCoord (polarCoord.symm (ρ, θ))` need not be `(ρ, θ)`. -/
theorem profileFromPolar_polarPoint
    (F : ℝ → ℝ → ℝ) {ρ θ : ℝ} (h : (ρ, θ) ∈ polarCoord.target) :
    profileFromPolar F (planarPolarPoint ρ θ) = F ρ θ := by
  unfold profileFromPolar
  rw [pointPair_polarPoint_eq_polarCoord_symm]
  have hright := polarCoord.right_inv h
  rw [hright]

/--
`∂R` of a polar-generated profile, reduced to the Fréchet derivatives of the
polar scalar formula and the forward polar chart.
-/
theorem profileDR_profileFromPolar_eq
    (F : ℝ → ℝ → ℝ) (x : (ℝ^2))
    {F' : ℝ × ℝ →L[ℝ] ℝ} {P' : ℝ × ℝ →L[ℝ] ℝ × ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ ↦ F p.1 p.2) F'
      (polarCoord (pointPair x)))
    (hpolar : HasFDerivAt (fun q : ℝ × ℝ ↦ polarCoord q) P' (pointPair x)) :
    profileDR (profileFromPolar F) x =
      ((F'.comp P').comp pointPairLinearMap)
        (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) := by
  exact partialDeriv_profileFromPolar_eq F x (0 : Fin 2) hF hpolar

/--
`∂Z` of a polar-generated profile, reduced to the Fréchet derivatives of the
polar scalar formula and the forward polar chart.
-/
theorem profileDZ_profileFromPolar_eq
    (F : ℝ → ℝ → ℝ) (x : (ℝ^2))
    {F' : ℝ × ℝ →L[ℝ] ℝ} {P' : ℝ × ℝ →L[ℝ] ℝ × ℝ}
    (hF : HasFDerivAt (fun p : ℝ × ℝ ↦ F p.1 p.2) F'
      (polarCoord (pointPair x)))
    (hpolar : HasFDerivAt (fun q : ℝ × ℝ ↦ polarCoord q) P' (pointPair x)) :
    profileDZ (profileFromPolar F) x =
      ((F'.comp P').comp pointPairLinearMap)
        (EuclideanSpace.single (1 : Fin 2) (1 : ℝ)) := by
  exact partialDeriv_profileFromPolar_eq F x (1 : Fin 2) hF hpolar

/-- A scalar polar formula `C²` near the chart parameters gives a `C²` Cartesian
profile at each point of the chart. No regularity outside that neighborhood is needed. -/
theorem contDiffAt_profileFromPolar
    (F : ℝ → ℝ → ℝ) {x : ℝ^2} (hx : pointPair x ∈ polarCoord.source)
    (hF : ContDiffAt ℝ 2 (fun q : ℝ × ℝ ↦ F q.1 q.2) (polarCoord (pointPair x))) :
    ContDiffAt ℝ 2 (profileFromPolar F) x := by
  have hpair : ContDiffAt ℝ 2 pointPair x := by
    rw [pointPair_eq_pointPairLinearMap]
    exact pointPairLinearMap.contDiff.contDiffAt
  change ContDiffAt ℝ 2
    (fun y : ℝ^2 ↦ F (polarCoord (pointPair y)).1 (polarCoord (pointPair y)).2) x
  exact hF.comp x ((contDiffAt_two_polarCoord hx).comp x hpair)

/-- A C² angular function gives a C² homogeneous Cartesian profile at every
point of the polar chart; the radial exponent need not be an integer. -/
theorem contDiffAt_profileFromPolar_rpow_mul
    (m : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {x : ℝ^2} (hx : pointPair x ∈ polarCoord.source) :
    ContDiffAt ℝ 2 (profileFromPolar (fun r β ↦ r ^ m * f β)) x := by
  let p := polarCoord (pointPair x)
  have hp : p ∈ polarCoord.target := polarCoord.map_source hx
  have hradial : ContDiffAt ℝ 2 (fun q : ℝ × ℝ ↦ q.1 ^ m) p :=
    (Real.contDiffAt_rpow_const_of_ne (ne_of_gt hp.1)).comp p
      contDiff_fst.contDiffAt
  have hangular : ContDiffAt ℝ 2 (fun q : ℝ × ℝ ↦ f q.2) p :=
    (hf.comp contDiff_snd).contDiffAt
  exact contDiffAt_profileFromPolar _ hx (hradial.mul hangular)

/-- Local scalar regularity suffices for a radially cut off homogeneous profile
at any point of the polar chart. -/
theorem contDiffAt_profileFromPolar_cutoff_rpow_mul
    (m : ℝ) {χ f : ℝ → ℝ} {x : ℝ^2}
    (hx : pointPair x ∈ polarCoord.source)
    (hχ : ContDiffAt ℝ 2 χ (polarCoord (pointPair x)).1)
    (hf : ContDiffAt ℝ 2 f (polarCoord (pointPair x)).2) :
    ContDiffAt ℝ 2 (profileFromPolar (fun r β ↦ χ r * (r ^ m * f β))) x := by
  have hp := polarCoord.map_source hx
  have hpow : ContDiffAt ℝ 2 (fun r : ℝ ↦ r ^ m) (polarCoord (pointPair x)).1 :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hp.1)
  apply contDiffAt_profileFromPolar _ hx
  exact (hχ.comp _ contDiffAt_fst).mul
    ((hpow.comp _ contDiffAt_fst).mul (hf.comp _ contDiffAt_snd))

/-- A polar formula vanishing at angles zero and pi vanishes on the horizontal
axis, including the origin and the branch cut of the chart. -/
theorem profileFromPolar_horizontal_axis
    (F : ℝ → ℝ → ℝ) (hzero : ∀ r, F r 0 = 0)
    (hpi : ∀ r, F r Real.pi = 0) {x : ℝ^2} (hx : x 1 = 0) :
    profileFromPolar F x = 0 := by
  change F (Real.sqrt ((x 0) ^ 2 + (x 1) ^ 2))
    (Complex.arg (Complex.equivRealProd.symm (x 0, x 1))) = 0
  simp only [Complex.equivRealProd_symm_apply, hx, Complex.ofReal_zero,
    zero_mul, add_zero]
  by_cases hnonneg : 0 ≤ x 0
  · rw [Complex.arg_ofReal_of_nonneg hnonneg]
    exact hzero _
  · rw [Complex.arg_ofReal_of_neg (lt_of_not_ge hnonneg)]
    exact hpi _

/-- Cartesian derivatives of a homogeneous polar field. The two components are
the rotation of its radial and angular derivatives; the chart target ensures
that the reconstructed field uses the specified angle. -/
theorem partialDeriv_profileFromPolar_rpow_mul
    (m : ℝ) {f : ℝ → ℝ} {r β : ℝ}
    (hf : DifferentiableAt ℝ f β) (hp : (r, β) ∈ polarCoord.target) :
    (∂[0] (profileFromPolar (fun s θ ↦ s ^ m * f θ))) (planarPolarPoint r β) =
        r ^ (m - 1) * (m * f β * Real.cos β - deriv f β * Real.sin β) ∧
      (∂[1] (profileFromPolar (fun s θ ↦ s ^ m * f θ))) (planarPolarPoint r β) =
        r ^ (m - 1) * (m * f β * Real.sin β + deriv f β * Real.cos β) := by
  have hr : 0 < r := hp.1
  have hround : polarCoord (pointPair (planarPolarPoint r β)) = (r, β) := by
    rw [pointPair_polarPoint_eq_polarCoord_symm]
    exact polarCoord.right_inv hp
  have hF := ((hasFDerivAt_fst (𝕜 := ℝ) (p := (r, β))).rpow_const
    (p := m) (Or.inl hr.ne')).mul
      (hf.hasDerivAt.comp_hasFDerivAt (r, β) (hasFDerivAt_snd (𝕜 := ℝ)))
  have hpolar := polarCoord_hasFDerivAt_symm_point hp
  rw [← pointPair_polarPoint_eq_polarCoord_symm r β] at hpolar
  let F' : ℝ × ℝ →L[ℝ] ℝ :=
    r ^ m • (deriv f β • ContinuousLinearMap.snd ℝ ℝ ℝ) +
      f β • ((m * r ^ (m - 1)) • ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hF' : HasFDerivAt (fun q : ℝ × ℝ ↦ q.1 ^ m * f q.2) F'
      (polarCoord (pointPair (planarPolarPoint r β))) := by
    rw [hround]
    exact hF
  have hzero := partialDeriv_profileFromPolar_eq
    (fun s θ ↦ s ^ m * f θ) (planarPolarPoint r β) 0 hF' hpolar
  have hone := partialDeriv_profileFromPolar_eq
    (fun s θ ↦ s ^ m * f θ) (planarPolarPoint r β) 1 hF' hpolar
  have hpow : r ^ m = r ^ (m - 1) * r := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hr.ne' (m - 1)
  constructor
  · rw [hzero]
    simp [F', polarCoordForwardFDeriv, pointPairLinearMap,
      Matrix.toLin_finTwoProd_apply, hpow]
    field_simp [hr.ne']
    ring
  · rw [hone]
    simp [F', polarCoordForwardFDeriv, pointPairLinearMap,
      Matrix.toLin_finTwoProd_apply, hpow]
    field_simp [hr.ne']
    ring

open scoped Gradient in
/-- The squared Cartesian gradient norm of a homogeneous polar field retains
both angular terms exactly. It is also the squared stream-velocity norm. -/
theorem norm_gradient_profileFromPolar_rpow_mul_sq
    (m : ℝ) {f : ℝ → ℝ} {r β : ℝ}
    (hf : DifferentiableAt ℝ f β) (hp : (r, β) ∈ polarCoord.target) :
    ‖∇ (profileFromPolar (fun s θ ↦ s ^ m * f θ)) (planarPolarPoint r β)‖ ^ 2 =
      (r ^ (m - 1)) ^ 2 * ((m * f β) ^ 2 + (deriv f β) ^ 2) := by
  obtain ⟨hx, hy⟩ := partialDeriv_profileFromPolar_rpow_mul m hf hp
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
    gradient_apply_eq_partialDeriv, gradient_apply_eq_partialDeriv, hx, hy]
  calc
    _ = (r ^ (m - 1)) ^ 2 * ((m * f β) ^ 2 + (deriv f β) ^ 2) *
        (Real.cos β ^ 2 + Real.sin β ^ 2) := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]

open scoped Gradient in
/-- Sup bounds for the angular value and derivative give a uniform Cartesian
velocity bound. The exponent and both budgets can be replaced independently. -/
theorem norm_gradient_profileFromPolar_rpow_mul_le
    (m : ℝ) {f : ℝ → ℝ} {r β F D : ℝ}
    (hf : DifferentiableAt ℝ f β) (hp : (r, β) ∈ polarCoord.target)
    (hF : 0 ≤ F) (hD : 0 ≤ D) (hvalue : |f β| ≤ F) (hderiv : |deriv f β| ≤ D) :
    ‖∇ (profileFromPolar (fun s θ ↦ s ^ m * f θ)) (planarPolarPoint r β)‖ ≤
      r ^ (m - 1) * Real.sqrt ((m * F) ^ 2 + D ^ 2) := by
  have hr : 0 < r := hp.1
  have hvalueSq : (f β) ^ 2 ≤ F ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hF).mpr hvalue
  have hderivSq : (deriv f β) ^ 2 ≤ D ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).mpr hderiv
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_gradient_profileFromPolar_rpow_mul_sq m hf hp,
    mul_pow (r ^ (m - 1)) (Real.sqrt ((m * F) ^ 2 + D ^ 2)) 2,
    Real.sq_sqrt (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (by simpa only [mul_pow] using
      mul_le_mul_of_nonneg_left hvalueSq (sq_nonneg m)) hderivSq) (sq_nonneg _)

open scoped Gradient Topology in
/-- A streamfunction with radial exponent `2 + α`, `α < 0`, has sublinear
velocity along every ray of the polar chart. This includes the nonintegrable
far-field vorticity modes `r^α g₁(β)` of Chen and Hou, Part I, Section 7.1, (7.1)-(7.2). -/
theorem tendsto_norm_gradient_profileFromPolar_rpow_div_radius
    {α β : ℝ} (hα : α < 0) (hβ : β ∈ Set.Ioo (-Real.pi) Real.pi)
    {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f β) :
    Filter.Tendsto
      (fun r : ℝ ↦
        ‖∇ (profileFromPolar (fun s θ ↦ s ^ (2 + α) * f θ)) (planarPolarPoint r β)‖ / r)
      Filter.atTop (𝓝 0) := by
  let C := Real.sqrt (((2 + α) * |f β|) ^ 2 + |deriv f β| ^ 2)
  have hdecay : Filter.Tendsto (fun r : ℝ ↦ r ^ α * C) Filter.atTop (𝓝 0) := by
    simpa only [neg_neg, zero_mul] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hα)).mul_const C
  apply squeeze_zero' _ _ hdecay
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_nonneg (norm_nonneg _) hr.le
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
    have hbound := norm_gradient_profileFromPolar_rpow_mul_le (2 + α) hf
      (show (r, β) ∈ polarCoord.target from ⟨hr, hβ⟩)
      (abs_nonneg (f β)) (abs_nonneg (deriv f β)) (le_refl _) (le_refl _)
    have hpow : r ^ ((2 + α) - 1) = r ^ α * r := by
      simpa only [show (2 + α) - 1 = α + 1 by ring] using Real.rpow_add_one hr.ne' α
    calc
      _ ≤ (r ^ ((2 + α) - 1) * C) / r := div_le_div_of_nonneg_right hbound hr.le
      _ = r ^ α * C := by
        rw [hpow]
        field_simp [hr.ne']

open scoped Gradient Topology in
/-- Uniform angular budgets give uniform sublinear velocity on any sector in
the polar chart. The sector may include the physical boundary rays. -/
theorem eventually_norm_gradient_profileFromPolar_div_radius_lt
    {α F D : ℝ} (hα : α < 0) (hF : 0 ≤ F) (hD : 0 ≤ D)
    {S : Set ℝ} (hS : S ⊆ Set.Ioo (-Real.pi) Real.pi) {f : ℝ → ℝ}
    (hf : ∀ β ∈ S, DifferentiableAt ℝ f β)
    (hvalue : ∀ β ∈ S, |f β| ≤ F) (hderiv : ∀ β ∈ S, |deriv f β| ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in Filter.atTop, ∀ β ∈ S,
      ‖∇ (profileFromPolar (fun s θ ↦ s ^ (2 + α) * f θ)) (planarPolarPoint r β)‖ / r < ε := by
  let C := Real.sqrt (((2 + α) * F) ^ 2 + D ^ 2)
  have hdecay : Filter.Tendsto (fun r : ℝ ↦ r ^ α * C) Filter.atTop (𝓝 0) := by
    simpa only [neg_neg, zero_mul] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hα)).mul_const C
  filter_upwards [hdecay.eventually (gt_mem_nhds hε),
    Filter.eventually_gt_atTop (0 : ℝ)] with r hsmall hr
  intro β hβ
  have hbound := norm_gradient_profileFromPolar_rpow_mul_le (2 + α) (hf β hβ)
    (show (r, β) ∈ polarCoord.target from ⟨hr, hS hβ⟩)
    hF hD (hvalue β hβ) (hderiv β hβ)
  have hpow : r ^ ((2 + α) - 1) = r ^ α * r := by
    simpa only [show (2 + α) - 1 = α + 1 by ring] using Real.rpow_add_one hr.ne' α
  calc
    _ ≤ (r ^ ((2 + α) - 1) * C) / r := div_le_div_of_nonneg_right hbound hr.le
    _ = r ^ α * C := by rw [hpow]; field_simp [hr.ne']
    _ < ε := hsmall

end PDE.FDeriv
