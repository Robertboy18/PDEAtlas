/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Polar.BoundaryRegularity
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# The Euclidean Laplacian in planar polar coordinates

Writing a planar field `u` in polar variables, `u(r cos β, r sin β)`, its Euclidean Laplacian
becomes `uᵣᵣ + r⁻¹ uᵣ + r⁻² u_ββ` away from the origin. We prove that identity for
the coordinate derivatives `∂[i]`. The polar map `planarPolarMap` sends the parameter point
`p = (r, β)` to `(r cos β, r sin β)`, with signed radius in coordinate zero and angle in
coordinate one, and the chain rule for `partialDeriv` is applied twice to express the second
radial and angular derivatives of the pullback in terms of the Cartesian Hessian. The coordinate
derivatives of the polar map itself, the partial derivatives of `r cos β` and `r sin β` in `r` and
`β`, are closed-form calculations checked by the CAS.

The polar expression is stated in two forms: `planarPolarLaplacianParam` acts on functions of the
parameter plane `ℝ^2`, while `planarPolarLaplacian` (from `PDE.CoordinateSystems.Polar`) acts on
curried profiles `ℝ → ℝ → ℝ` using one-variable derivatives. Both are total expressions because
division by `r` is total in Lean; the comparison with the Euclidean Laplacian needs `r ≠ 0` and
`C²` regularity of the Cartesian field at the image point.

## Main results

* `planarPolarLaplacianParam_comp_planarPolarMap`: for `p 0 ≠ 0`, the polar Laplacian of the
  pullback `u ∘ planarPolarMap` at `p` equals `laplacian u (planarPolarMap p)`.
* `planarPolarLaplacianParam_uncurry`: the parameter-plane and curried polar Laplacians agree on
  uncurried `C²` profiles.
* `laplacian_eq_planarPolarLaplacian_of_pullback`: if the pullback of `u` agrees near `p` with a
  curried profile `v`, the Euclidean Laplacian of `u` at `planarPolarMap p` is the polar Laplacian
  of `v` at `(p 0, p 1)`. This is the form used to transfer radial or separated ansätze to
  Cartesian PDE statements.
* `neg_laplacian_profileFromPolar_rpow_add_two_mul`: if a `C²` angular factor solves
  `-f'' - (2 + α)² f = g`, the Cartesian field with polar form `r^(2+α) f(β)` solves the
  Poisson equation `-Δu = r^α g(β)` on the chart.

The identity is classical. Its radial specialisation `Δu = u'' + (n - 1) u' / r` is the starting
point for the fundamental solution of Laplace's equation in Evans, §2.2.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.1, (5)-(6), pp. 21-22.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian coordinateLine)

noncomputable section

namespace EuclideanLaplacian

open PDE.CoordinateSystems

/-- The polar Laplacian of a scalar function on the two-dimensional parameter plane.

Lean's division is total, so this expression has a value at `p 0 = 0`; the classical polar
Laplacian interpretation and the Cartesian comparison theorem below require `p 0 ≠ 0`. -/
def planarPolarLaplacianParam (u : ℝ^2 → ℝ) (p : ℝ^2) : ℝ :=
  (∂[0] (fun q ↦ (∂[0] u) q)) p +
    (1 / p 0) * (∂[0] u) p +
      (1 / (p 0) ^ 2) * (∂[1] (fun q ↦ (∂[1] u) q)) p

@[simp]
private theorem partialDeriv_zero_radius_mul_cos (p : ℝ^2) :
    (∂[0] (fun q : ℝ^2 ↦ q 0 * Real.cos (q 1))) p = Real.cos (p 1) := by
  cas

@[simp]
private theorem partialDeriv_one_radius_mul_cos (p : ℝ^2) :
    (∂[1] (fun q : ℝ^2 ↦ q 0 * Real.cos (q 1))) p =
      -p 0 * Real.sin (p 1) := by
  cas

@[simp]
private theorem partialDeriv_zero_radius_mul_sin (p : ℝ^2) :
    (∂[0] (fun q : ℝ^2 ↦ q 0 * Real.sin (q 1))) p = Real.sin (p 1) := by
  cas

@[simp]
private theorem partialDeriv_one_radius_mul_sin (p : ℝ^2) :
    (∂[1] (fun q : ℝ^2 ↦ q 0 * Real.sin (q 1))) p =
      p 0 * Real.cos (p 1) := by
  cas

@[simp]
private theorem partialDeriv_zero_cos_coordinate_one (p : ℝ^2) :
    (∂[0] (fun q : ℝ^2 ↦ Real.cos (q 1))) p = 0 := by
  cas

@[simp]
private theorem partialDeriv_zero_sin_coordinate_one (p : ℝ^2) :
    (∂[0] (fun q : ℝ^2 ↦ Real.sin (q 1))) p = 0 := by
  cas

private theorem partialDeriv_one_neg_radius_mul_sin (p : ℝ^2) :
    (∂[1] (fun q : ℝ^2 ↦ -q 0 * Real.sin (q 1))) p =
      -p 0 * Real.cos (p 1) := by
  cas

/-- Radial derivative of a Cartesian scalar field pulled back to polar parameters. -/
theorem partialDeriv_zero_comp_planarPolarMap
    (u : ℝ^2 → ℝ) (p : ℝ^2)
    (hu : DifferentiableAt ℝ u (planarPolarMap p)) :
    (∂[0] (fun q ↦ u (planarPolarMap q))) p =
      (∂[0] u) (planarPolarMap p) * Real.cos (p 1) +
        (∂[1] u) (planarPolarMap p) * Real.sin (p 1) := by
  rw [PDE.partialDeriv_comp 0 u planarPolarMap p
    hu
    ((contDiff_planarPolarMap.differentiable (by norm_num)).differentiableAt)]
  simp [Fin.sum_univ_two]

/-- Second radial derivative of a Cartesian scalar field pulled back to polar parameters. -/
theorem secondPartialDeriv_zero_comp_planarPolarMap
    (u : ℝ^2 → ℝ) (p : ℝ^2)
    (hu : ContDiffAt ℝ 2 u (planarPolarMap p)) :
    (∂[0] (fun q ↦ (∂[0] (fun y ↦ u (planarPolarMap y))) q)) p =
      (∂[0] (fun x ↦ (∂[0] u) x)) (planarPolarMap p) *
          Real.cos (p 1) ^ 2 +
        (∂[1] (fun x ↦ (∂[0] u) x)) (planarPolarMap p) *
          Real.sin (p 1) * Real.cos (p 1) +
        (∂[0] (fun x ↦ (∂[1] u) x)) (planarPolarMap p) *
          Real.cos (p 1) * Real.sin (p 1) +
        (∂[1] (fun x ↦ (∂[1] u) x)) (planarPolarMap p) *
          Real.sin (p 1) ^ 2 := by
  have h := PDE.partialDeriv_partialDeriv_comp_at 0 0 u planarPolarMap p hu
    ((contDiff_planarPolarMap.of_le (WithTop.coe_le_coe.mpr le_top)) :
      ContDiff ℝ 2 planarPolarMap).contDiffAt
  rw [h]
  simp only [Fin.sum_univ_two, planarPolarMap_zero, planarPolarMap_one,
    partialDeriv_zero_radius_mul_cos, partialDeriv_zero_radius_mul_sin,
    partialDeriv_zero_cos_coordinate_one, partialDeriv_zero_sin_coordinate_one,
    mul_zero, add_zero]
  ring

/-- Second angular derivative of a Cartesian scalar field pulled back to polar parameters. -/
theorem secondPartialDeriv_one_comp_planarPolarMap
    (u : ℝ^2 → ℝ) (p : ℝ^2)
    (hu : ContDiffAt ℝ 2 u (planarPolarMap p)) :
    (∂[1] (fun q ↦ (∂[1] (fun y ↦ u (planarPolarMap y))) q)) p =
      (∂[0] (fun x ↦ (∂[0] u) x)) (planarPolarMap p) *
          (p 0) ^ 2 * Real.sin (p 1) ^ 2 -
        (∂[1] (fun x ↦ (∂[0] u) x)) (planarPolarMap p) *
          (p 0) ^ 2 * Real.sin (p 1) * Real.cos (p 1) -
        (∂[0] (fun x ↦ (∂[1] u) x)) (planarPolarMap p) *
          (p 0) ^ 2 * Real.sin (p 1) * Real.cos (p 1) +
        (∂[1] (fun x ↦ (∂[1] u) x)) (planarPolarMap p) *
          (p 0) ^ 2 * Real.cos (p 1) ^ 2 -
        (∂[0] u) (planarPolarMap p) * p 0 * Real.cos (p 1) -
        (∂[1] u) (planarPolarMap p) * p 0 * Real.sin (p 1) := by
  have h := PDE.partialDeriv_partialDeriv_comp_at 1 1 u planarPolarMap p hu
    ((contDiff_planarPolarMap.of_le (WithTop.coe_le_coe.mpr le_top)) :
      ContDiff ℝ 2 planarPolarMap).contDiffAt
  rw [h]
  simp only [Fin.sum_univ_two, planarPolarMap_zero, planarPolarMap_one,
    partialDeriv_one_radius_mul_cos, partialDeriv_one_radius_mul_sin,
    partialDeriv_one_neg_radius_mul_sin]
  ring

/-- Away from the coordinate singularity `r = 0`, the polar Laplacian of a Cartesian field's
pullback equals its Euclidean Laplacian. -/
theorem planarPolarLaplacianParam_comp_planarPolarMap
    (u : ℝ^2 → ℝ) (p : ℝ^2)
    (hu : ContDiffAt ℝ 2 u (planarPolarMap p)) (hr : p 0 ≠ 0) :
    planarPolarLaplacianParam (fun q ↦ u (planarPolarMap q)) p =
      laplacian u (planarPolarMap p) := by
  rw [planarPolarLaplacianParam]
  rw [secondPartialDeriv_zero_comp_planarPolarMap u p hu]
  rw [partialDeriv_zero_comp_planarPolarMap u p
    (hu.differentiableAt (by norm_num))]
  rw [secondPartialDeriv_one_comp_planarPolarMap u p hu]
  rw [laplacian, Fin.sum_univ_two]
  field_simp [hr]
  have htrig : Real.cos (p 1) ^ 2 + Real.sin (p 1) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (p 1)]
  ring_nf
  linear_combination
    ((∂[0] (fun x ↦ (∂[0] u) x)) (planarPolarMap p) * p 0 +
      (∂[1] (fun x ↦ (∂[1] u) x)) (planarPolarMap p) * p 0) * htrig

/-- Coordinate-zero differentiation of an uncurried two-variable function is radial
differentiation. -/
theorem partialDeriv_zero_uncurry
    (v : ℝ → ℝ → ℝ) (p : ℝ^2)
    (hv : DifferentiableAt ℝ (fun q ↦ v (q 0) (q 1)) p) :
    (∂[0] (fun q : ℝ^2 ↦ v (q 0) (q 1))) p =
      deriv (fun r ↦ v r (p 1)) (p 0) := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine 0 p hv]
  congr 1
  funext r
  simp [coordinateLine]

/-- Coordinate-one differentiation of an uncurried two-variable function is angular
differentiation. -/
theorem partialDeriv_one_uncurry
    (v : ℝ → ℝ → ℝ) (p : ℝ^2)
    (hv : DifferentiableAt ℝ (fun q ↦ v (q 0) (q 1)) p) :
    (∂[1] (fun q : ℝ^2 ↦ v (q 0) (q 1))) p =
      deriv (v (p 0)) (p 1) := by
  rw [PDE.partialDeriv_eq_deriv_coordinateLine 1 p hv]
  congr 1
  funext β
  simp [coordinateLine]

/-- Repeating coordinate-zero differentiation of an uncurried function gives its second radial
derivative. -/
theorem secondPartialDeriv_zero_uncurry
    (v : ℝ → ℝ → ℝ) (p : ℝ^2)
    (hv : ContDiffAt ℝ 2 (fun q : ℝ^2 ↦ v (q 0) (q 1)) p) :
    (∂[0] (fun q ↦ (∂[0] (fun y : ℝ^2 ↦ v (y 0) (y 1))) q)) p =
      deriv (deriv (fun r ↦ v r (p 1))) (p 0) := by
  have h := PDE.iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at
    (n := 2) 0 2 hv
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  simpa [Function.iterate_succ_apply, Function.comp_def, coordinateLine] using h

/-- Repeating coordinate-one differentiation of an uncurried function gives its second angular
derivative. -/
theorem secondPartialDeriv_one_uncurry
    (v : ℝ → ℝ → ℝ) (p : ℝ^2)
    (hv : ContDiffAt ℝ 2 (fun q : ℝ^2 ↦ v (q 0) (q 1)) p) :
    (∂[1] (fun q ↦ (∂[1] (fun y : ℝ^2 ↦ v (y 0) (y 1))) q)) p =
      deriv (deriv (v (p 0))) (p 1) := by
  have h := PDE.iterate_partialDeriv_eq_iteratedDeriv_coordinateLine_at
    (n := 2) 1 2 hv
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  simpa [Function.iterate_succ_apply, Function.comp_def, coordinateLine] using h

/-- The parameter-plane and curried definitions of the planar polar Laplacian agree for `C²`
functions. -/
theorem planarPolarLaplacianParam_uncurry
    (v : ℝ → ℝ → ℝ) (p : ℝ^2)
    (hv : ContDiffAt ℝ 2 (fun q : ℝ^2 ↦ v (q 0) (q 1)) p) :
    planarPolarLaplacianParam (fun q ↦ v (q 0) (q 1)) p =
      planarPolarLaplacian v (p 0) (p 1) := by
  rw [planarPolarLaplacianParam, planarPolarLaplacian]
  rw [secondPartialDeriv_zero_uncurry v p hv]
  rw [partialDeriv_zero_uncurry v p
    (hv.differentiableAt (by norm_num))]
  rw [secondPartialDeriv_one_uncurry v p hv]
  rw [radialLaplacian]
  norm_num

/-- The parameter-plane polar Laplacian depends only on the germ of the function at the
evaluation point. -/
theorem planarPolarLaplacianParam_congr_nhds
    {u v : ℝ^2 → ℝ} {p : ℝ^2} (h : u =ᶠ[nhds p] v) :
    planarPolarLaplacianParam u p = planarPolarLaplacianParam v p := by
  unfold planarPolarLaplacianParam
  rw [PDE.partialDeriv_second_congr_nhds 0 h]
  rw [PDE.partialDeriv_congr_nhds 0 h]
  rw [PDE.partialDeriv_second_congr_nhds 1 h]

/-- A `C²` Cartesian field whose polar pullback agrees locally with a curried profile has
Euclidean Laplacian equal to the profile's polar Laplacian. -/
theorem laplacian_eq_planarPolarLaplacian_of_pullback
    (u : ℝ^2 → ℝ) (v : ℝ → ℝ → ℝ) (p : ℝ^2)
    (hu : ContDiffAt ℝ 2 u (planarPolarMap p))
    (hv : ContDiffAt ℝ 2 (fun q : ℝ^2 ↦ v (q 0) (q 1)) p)
    (hr : p 0 ≠ 0)
    (hpullback : (fun q ↦ u (planarPolarMap q)) =ᶠ[nhds p]
      fun q ↦ v (q 0) (q 1)) :
    laplacian u (planarPolarMap p) = planarPolarLaplacian v (p 0) (p 1) := by
  calc
    laplacian u (planarPolarMap p) =
        planarPolarLaplacianParam (fun q ↦ u (planarPolarMap q)) p :=
      (planarPolarLaplacianParam_comp_planarPolarMap u p hu hr).symm
    _ = planarPolarLaplacianParam (fun q ↦ v (q 0) (q 1)) p :=
      planarPolarLaplacianParam_congr_nhds hpullback
    _ = planarPolarLaplacian v (p 0) (p 1) :=
      planarPolarLaplacianParam_uncurry v p hv

/-- A polar formula `C²` near the chart parameters reconstructs a Cartesian field
whose Laplacian is its polar Laplacian. Chart regularity supplies the Cartesian
regularity, so the application need only check the scalar formula. -/
theorem laplacian_profileFromPolar
    (F : ℝ → ℝ → ℝ) {p : ℝ^2}
    (hp : PDE.FDeriv.pointPair p ∈ polarCoord.target)
    (hF : ContDiffAt ℝ 2 (fun q : ℝ × ℝ ↦ F q.1 q.2) (PDE.FDeriv.pointPair p)) :
    laplacian (PDE.FDeriv.profileFromPolar F) (planarPolarMap p) =
      planarPolarLaplacian F (p 0) (p 1) := by
  have hr : 0 < p 0 := hp.1
  have hsource : PDE.FDeriv.pointPair (planarPolarMap p) ∈ polarCoord.source := by
    change PDE.FDeriv.pointPair (planarPolarPoint (p 0) (p 1)) ∈ polarCoord.source
    rw [PDE.FDeriv.pointPair_polarPoint_eq_polarCoord_symm]
    exact polarCoord.map_target hp
  have hpair : ContDiff ℝ 2 PDE.FDeriv.pointPair := by
    rw [PDE.FDeriv.pointPair_eq_pointPairLinearMap]
    exact PDE.FDeriv.pointPairLinearMap.contDiff
  have hroundtrip : polarCoord (PDE.FDeriv.pointPair (planarPolarMap p)) =
      PDE.FDeriv.pointPair p := by
    change polarCoord (PDE.FDeriv.pointPair (planarPolarPoint (p 0) (p 1))) = _
    rw [PDE.FDeriv.pointPair_polarPoint_eq_polarCoord_symm]
    exact polarCoord.right_inv hp
  have hF' : ContDiffAt ℝ 2 (fun q : ℝ × ℝ ↦ F q.1 q.2)
      (polarCoord (PDE.FDeriv.pointPair (planarPolarMap p))) := by
    rw [hroundtrip]
    exact hF
  have hu : ContDiffAt ℝ 2 (PDE.FDeriv.profileFromPolar F) (planarPolarMap p) := by
    exact PDE.FDeriv.contDiffAt_profileFromPolar F hsource hF'
  have hparam : ContDiffAt ℝ 2 (fun q : ℝ^2 ↦ F (q 0) (q 1)) p := by
    simpa only [Function.comp_def, PDE.FDeriv.pointPair,
      meridianR, meridianZ] using hF.comp p hpair.contDiffAt
  have htarget : ∀ᶠ q in nhds p, PDE.FDeriv.pointPair q ∈ polarCoord.target :=
    (PDE.FDeriv.pointPairLinearMap.continuous.tendsto p).eventually
      (polarCoord.open_target.mem_nhds hp)
  have hpullback : (fun q ↦ PDE.FDeriv.profileFromPolar F (planarPolarMap q)) =ᶠ[nhds p]
      fun q ↦ F (q 0) (q 1) := by
    filter_upwards [htarget] with q hq
    exact PDE.FDeriv.profileFromPolar_polarPoint F hq
  exact laplacian_eq_planarPolarLaplacian_of_pullback
    (PDE.FDeriv.profileFromPolar F) F p hu hparam hr.ne' hpullback

/-- The reconstructed homogeneous Cartesian field satisfies the actual
Poisson equation on the chart whenever its angular factor solves the ODE. -/
theorem neg_laplacian_profileFromPolar_rpow_add_two_mul
    (α : ℝ) {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hangular : ∀ β, -deriv (deriv f) β - (2 + α) ^ 2 * f β = g β)
    {p : ℝ^2} (hp : PDE.FDeriv.pointPair p ∈ polarCoord.target) :
    -PDE.laplacian (PDE.FDeriv.profileFromPolar (fun r β ↦ r ^ (2 + α) * f β))
      (planarPolarMap p) = (p 0) ^ α * g (p 1) := by
  have hr : 0 < p 0 := hp.1
  have hpow : ContDiffAt ℝ 2 (fun r : ℝ ↦ r ^ (2 + α)) (p 0) :=
    Real.contDiffAt_rpow_const_of_ne hr.ne'
  have hF : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ ↦ q.1 ^ (2 + α) * f q.2) (PDE.FDeriv.pointPair p) := by
    simpa only [Function.comp_def] using
      (hpow.comp (PDE.FDeriv.pointPair p) contDiffAt_fst).mul
        (hf.contDiffAt.comp (PDE.FDeriv.pointPair p) contDiffAt_snd)
  rw [laplacian_profileFromPolar _ hp hF]
  exact neg_planarPolarLaplacian_rpow_add_two_mul_eq f g α (p 0) (p 1) hr
    (hangular (p 1))

/-- The source correction introduced by cutting off the homogeneous streamfunction
`rᵐ f(β)`. It is added to the near-field source before Poisson inversion. -/
def polarCutoffCommutator (χ f : ℝ → ℝ) (m : ℝ) : ℝ^2 → ℝ :=
  PDE.FDeriv.profileFromPolar (fun r β ↦
    r ^ m * f β * radialLaplacian 2 χ r +
      2 * m * r ^ (m - 1) * deriv χ r * f β)

/-- The radial factor of the cutoff commutator for the homogeneous exponent `m`. -/
def polarCutoffRadialFactor (χ : ℝ → ℝ) (m r : ℝ) : ℝ :=
  r ^ m * radialLaplacian 2 χ r + 2 * m * r ^ (m - 1) * deriv χ r

/-- The angular factor separates from both radial cutoff terms. -/
theorem polarCutoffCommutator_eq_radial_mul (χ f : ℝ → ℝ) (m : ℝ) :
    polarCutoffCommutator χ f m = PDE.FDeriv.profileFromPolar
      (fun r β ↦ polarCutoffRadialFactor χ m r * f β) := by
  funext x
  unfold polarCutoffCommutator polarCutoffRadialFactor PDE.FDeriv.profileFromPolar
  ring

/-- A locally constant cutoff has zero commutator near the origin. -/
theorem polarCutoffRadialFactor_zero_near_zero
    {χ : ℝ → ℝ} {c : ℝ} (hflat : χ =ᶠ[nhds 0] fun _ ↦ c) (m : ℝ) :
    polarCutoffRadialFactor χ m =ᶠ[nhds 0] fun _ ↦ 0 := by
  have hfirst : deriv χ =ᶠ[nhds 0] fun _ ↦ 0 := by simpa using hflat.deriv
  have hsecond : deriv (deriv χ) =ᶠ[nhds 0] fun _ ↦ 0 := by
    simpa using hflat.deriv.deriv
  filter_upwards [hfirst, hsecond] with r hr hr'
  simp [polarCutoffRadialFactor, radialLaplacian, hr, hr']

/-- Local constancy at the origin removes any singular real powers from the
radial commutator. Only `C²` regularity of the cutoff is needed for continuity. -/
theorem continuous_polarCutoffRadialFactor
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) {c : ℝ}
    (hflat : χ =ᶠ[nhds 0] fun _ ↦ c) (m : ℝ) :
    Continuous (polarCutoffRadialFactor χ m) := by
  have hfirst : ContDiff ℝ 1 (deriv χ) := hχ.deriv'
  have hsecond : Continuous (deriv (deriv χ)) := hfirst.continuous_deriv (by norm_num)
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    exact continuousAt_const.congr_of_eventuallyEq
      (polarCutoffRadialFactor_zero_near_zero hflat m)
  · have hpow : ContinuousAt (fun s : ℝ ↦ s ^ m) r :=
      (Real.contDiffAt_rpow_const_of_ne hr : ContDiffAt ℝ 2 (fun s : ℝ ↦ s ^ m) r).continuousAt
    have hpow' : ContinuousAt (fun s : ℝ ↦ s ^ (m - 1)) r :=
      (Real.contDiffAt_rpow_const_of_ne hr :
        ContDiffAt ℝ 2 (fun s : ℝ ↦ s ^ (m - 1)) r).continuousAt
    have hlap : ContinuousAt (radialLaplacian 2 χ) r :=
      hsecond.continuousAt.add
        ((continuousAt_const.div continuousAt_id hr).mul hfirst.continuous.continuousAt)
    exact (hpow.mul hlap).add
      ((continuousAt_const.mul hpow').mul hfirst.continuous.continuousAt)

/-- A cutoff constant near the origin and matching angular endpoint values
give a globally continuous Cartesian commutator, including its branch cut. -/
theorem continuous_polarCutoffCommutator
    {χ f : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hf : ContinuousOn f (Set.Icc (-Real.pi) Real.pi))
    (hend : f (-Real.pi) = f Real.pi) {c : ℝ}
    (hflat : χ =ᶠ[nhds 0] fun _ ↦ c) (m : ℝ) :
    Continuous (polarCutoffCommutator χ f m) := by
  rw [polarCutoffCommutator_eq_radial_mul]
  exact PDE.FDeriv.continuous_profileFromPolar_mul_of_zero_near_zero
    (continuous_polarCutoffRadialFactor hχ hflat m) hf hend
    (polarCutoffRadialFactor_zero_near_zero hflat m)

/-- A locally constant `C⁴` cutoff gives a globally `C²` radial commutator
factor; the zero germ removes the possible real-power singularity. -/
theorem contDiff_polarCutoffRadialFactor
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 4 χ) {c : ℝ}
    (hflat : χ =ᶠ[nhds 0] fun _ ↦ c) (m : ℝ) :
    ContDiff ℝ 2 (polarCutoffRadialFactor χ m) := by
  have hfirst : ContDiff ℝ 3 (deriv χ) := hχ.deriv'
  have hsecond : ContDiff ℝ 2 (deriv (deriv χ)) := hfirst.deriv'
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    exact contDiffAt_const.congr_of_eventuallyEq
      (polarCutoffRadialFactor_zero_near_zero hflat m)
  · have hlap : ContDiffAt ℝ 2 (radialLaplacian 2 χ) r :=
      hsecond.contDiffAt.add ((contDiffAt_const.div contDiffAt_id hr).mul
        (hfirst.of_le (by norm_num)).contDiffAt)
    have hpow : ContDiffAt ℝ 2 (fun s : ℝ ↦ s ^ m) r :=
      Real.contDiffAt_rpow_const_of_ne hr
    have hpow' : ContDiffAt ℝ 2 (fun s : ℝ ↦ s ^ (m - 1)) r :=
      Real.contDiffAt_rpow_const_of_ne hr
    exact (hpow.mul hlap).add
      ((contDiffAt_const.mul hpow').mul (hfirst.of_le (by norm_num)).contDiffAt)

/-- The compact commutator is `C²` within the entire closed physical half-plane.
The unused negative angular values need no compatibility condition. -/
theorem contDiffOn_polarCutoffCommutator_closed_upper
    {χ f : ℝ → ℝ} (hχ : ContDiff ℝ 4 χ) (hf : ContDiff ℝ 2 f) {c : ℝ}
    (hflat : χ =ᶠ[nhds 0] fun _ ↦ c) (m : ℝ) :
    ContDiffOn ℝ 2 (polarCutoffCommutator χ f m)
      (PDE.Common.coordinateClosedHalfSpace (1 : Fin 2)) := by
  rw [polarCutoffCommutator_eq_radial_mul]
  exact PDE.FDeriv.contDiffOn_profileFromPolar_mul_closed_upper
    (contDiff_polarCutoffRadialFactor hχ hflat m) hf
    (polarCutoffRadialFactor_zero_near_zero hflat m)

/-- The cutoff commutator is locally `C²` on the polar chart when the cutoff
is locally `C⁴` and the angular factor is locally `C²`. -/
theorem contDiffAt_polarCutoffCommutator
    (m : ℝ) {χ f : ℝ → ℝ} {x : ℝ^2}
    (hx : PDE.FDeriv.pointPair x ∈ polarCoord.source)
    (hχ : ContDiffAt ℝ 4 χ (polarCoord (PDE.FDeriv.pointPair x)).1)
    (hf : ContDiffAt ℝ 2 f (polarCoord (PDE.FDeriv.pointPair x)).2) :
    ContDiffAt ℝ 2 (polarCutoffCommutator χ f m) x := by
  let p := polarCoord (PDE.FDeriv.pointPair x)
  have hr : p.1 ≠ 0 := ne_of_gt (polarCoord.map_source hx).1
  have hfirst : ContDiffAt ℝ 3 (deriv χ) p.1 := hχ.derivWithin (by norm_num)
  have hsecond : ContDiffAt ℝ 2 (deriv (deriv χ)) p.1 :=
    hfirst.derivWithin (by norm_num)
  have hlap : ContDiffAt ℝ 2 (radialLaplacian 2 χ) p.1 := by
    change ContDiffAt ℝ 2 (fun r ↦ deriv (deriv χ) r + (2 - 1) / r * deriv χ r) p.1
    exact hsecond.add ((contDiffAt_const.div contDiffAt_id hr).mul
      (hfirst.of_le (by norm_num)))
  have hpow : ContDiffAt ℝ 2 (fun r : ℝ ↦ r ^ m) p.1 :=
    Real.contDiffAt_rpow_const_of_ne hr
  have hpow' : ContDiffAt ℝ 2 (fun r : ℝ ↦ r ^ (m - 1)) p.1 :=
    Real.contDiffAt_rpow_const_of_ne hr
  apply PDE.FDeriv.contDiffAt_profileFromPolar _ hx
  exact (((hpow.comp p contDiffAt_fst).mul (hf.comp p contDiffAt_snd)).mul
    (hlap.comp p contDiffAt_fst)).add
      (((contDiffAt_const.mul (hpow'.comp p contDiffAt_fst)).mul
        ((hfirst.of_le (by norm_num)).comp p contDiffAt_fst)).mul
          (hf.comp p contDiffAt_snd))

/-- A radial cutoff constant beyond a finite radius has a compactly supported
commutator. No decay of the homogeneous angular mode is needed. -/
theorem hasCompactSupport_polarCutoffCommutator
    (χ f : ℝ → ℝ) (m : ℝ) {R c : ℝ}
    (hχ : ∀ r, R < r → χ r = c) :
    HasCompactSupport (polarCutoffCommutator χ f m) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ^2) (max R 0 + 1))
  intro x hx
  have hlarge : max R 0 + 1 < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  have hR : R < ‖x‖ := by linarith [le_max_left R 0]
  have hconstant : χ =ᶠ[nhds ‖x‖] fun _ ↦ c := by
    filter_upwards [eventually_gt_nhds hR] with r hr
    exact hχ r hr
  have hfirst : deriv χ ‖x‖ = 0 := by simpa using hconstant.deriv_eq
  have hsecond : deriv (deriv χ) ‖x‖ = 0 := by simpa using hconstant.deriv.deriv_eq
  have hlap : radialLaplacian 2 χ ‖x‖ = 0 := by
    simp [radialLaplacian, hfirst, hsecond]
  simp only [polarCutoffCommutator, PDE.FDeriv.profileFromPolar,
    PDE.FDeriv.polarCoord_pointPair_fst, hfirst, hlap, mul_zero, zero_mul, add_zero]

/-- Cutting off a homogeneous Cartesian streamfunction retains the prescribed
far-field source and gives the explicit radial commutator. This is the source
that must be added to the compact near-field inversion. -/
theorem neg_laplacian_profileFromPolar_cutoff_rpow_add_two_mul
    (α : ℝ) {χ f g : ℝ → ℝ}
    {p : ℝ^2} (hp : PDE.FDeriv.pointPair p ∈ polarCoord.target)
    (hf : ContDiffAt ℝ 2 f (p 1))
    (hχ : ContDiffAt ℝ 2 χ (p 0))
    (hangular : -deriv (deriv f) (p 1) - (2 + α) ^ 2 * f (p 1) = g (p 1)) :
    -laplacian (PDE.FDeriv.profileFromPolar
      (fun r β ↦ χ r * (r ^ (2 + α) * f β))) (planarPolarMap p) =
        χ (p 0) * (p 0) ^ α * g (p 1) -
          polarCutoffCommutator χ f (2 + α) (planarPolarMap p) := by
  have hr : 0 < p 0 := hp.1
  have hpow : ContDiffAt ℝ 2 (fun r : ℝ ↦ r ^ (2 + α)) (p 0) :=
    Real.contDiffAt_rpow_const_of_ne hr.ne'
  have hF : ContDiffAt ℝ 2
      (fun q : ℝ × ℝ ↦ χ q.1 * (q.1 ^ (2 + α) * f q.2))
      (PDE.FDeriv.pointPair p) := by
    simpa only [Function.comp_def] using
      (hχ.comp (PDE.FDeriv.pointPair p) contDiffAt_fst).mul
        ((hpow.comp (PDE.FDeriv.pointPair p) contDiffAt_fst).mul
          (hf.comp (PDE.FDeriv.pointPair p) contDiffAt_snd))
  rw [laplacian_profileFromPolar _ hp hF]
  have hcomm : polarCutoffCommutator χ f (2 + α) (planarPolarMap p) =
      (p 0) ^ (2 + α) * f (p 1) * radialLaplacian 2 χ (p 0) +
        2 * (2 + α) * (p 0) ^ (2 + α - 1) * deriv χ (p 0) * f (p 1) :=
    PDE.FDeriv.profileFromPolar_polarPoint _ hp
  rw [neg_planarPolarLaplacian_cutoff_rpow_mul_eq χ f g (2 + α) (p 0) (p 1) hr hχ hangular,
    hcomm, show 2 + α - 2 = α by ring]
  ring

/-- The cutoff Poisson identity at a Cartesian point in the polar chart,
with the regularity assumptions evaluated at its chart parameters. -/
theorem neg_laplacian_profileFromPolar_cutoff_rpow_add_two_mul_of_source
    (α : ℝ) {χ f g : ℝ → ℝ} {x : ℝ^2}
    (hx : PDE.FDeriv.pointPair x ∈ polarCoord.source)
    (hf : ContDiffAt ℝ 2 f (polarCoord (PDE.FDeriv.pointPair x)).2)
    (hχ : ContDiffAt ℝ 2 χ (polarCoord (PDE.FDeriv.pointPair x)).1)
    (hangular : -deriv (deriv f) (polarCoord (PDE.FDeriv.pointPair x)).2 -
      (2 + α) ^ 2 * f (polarCoord (PDE.FDeriv.pointPair x)).2 =
        g (polarCoord (PDE.FDeriv.pointPair x)).2) :
    -laplacian (PDE.FDeriv.profileFromPolar
      (fun r β ↦ χ r * (r ^ (2 + α) * f β))) x =
        χ (polarCoord (PDE.FDeriv.pointPair x)).1 *
          (polarCoord (PDE.FDeriv.pointPair x)).1 ^ α *
            g (polarCoord (PDE.FDeriv.pointPair x)).2 - polarCutoffCommutator χ f (2 + α) x := by
  let p : ℝ^2 := EuclideanSpace.single 0 (polarCoord (PDE.FDeriv.pointPair x)).1 +
    EuclideanSpace.single 1 (polarCoord (PDE.FDeriv.pointPair x)).2
  have hp : PDE.FDeriv.pointPair p ∈ polarCoord.target := by
    simpa [p, PDE.FDeriv.pointPair, meridianR, meridianZ] using polarCoord.map_source hx
  have hpzero : p 0 = (polarCoord (PDE.FDeriv.pointPair x)).1 := by simp [p]
  have hpone : p 1 = (polarCoord (PDE.FDeriv.pointPair x)).2 := by simp [p]
  have hxparam : planarPolarMap p = x := by
    apply PDE.FDeriv.point_eq_of_pointPair_eq
    change PDE.FDeriv.pointPair (planarPolarPoint (p 0) (p 1)) = PDE.FDeriv.pointPair x
    rw [hpzero, hpone, PDE.FDeriv.pointPair_polarPoint_eq_polarCoord_symm]
    exact polarCoord.left_inv hx
  have h := neg_laplacian_profileFromPolar_cutoff_rpow_add_two_mul α hp
    (by simpa only [hpone] using hf) (by simpa only [hpzero] using hχ)
    (by simpa only [hpone] using hangular)
  simpa only [hxparam, hpzero, hpone] using h

end EuclideanLaplacian

end
