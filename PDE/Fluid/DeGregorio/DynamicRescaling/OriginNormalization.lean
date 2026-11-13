/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.DynamicRescaling
import PDE.Analysis.Calculus.SpaceTimeScalar
import CAS.ExactTactic

/-!
# Origin normalization for the rescaled De Gregorio equation

For `a = 1`, a sufficiently regular solution with `ω(0,t) = u(0,t) = 0` satisfies
`∂t ω_x(0,t) = (cω(t) - cl(t)) ω_x(0,t)`. Equal total scaling rates therefore preserve
the origin slope. Subtracting a fixed profile preserves zero perturbation slope when
the initial slopes match.

The slope ODE is derived from the rescaled transport equation by spatial
differentiation and symmetry of the second Fréchet derivative. Joint `C²` regularity
is required only at the origin at each admitted time; the velocity needs spatial `C²`
regularity there. Derivatives at time endpoints concern the given total extensions,
as in `HasClassicalRegularityOn`.

## References

* J. Chen, T. Y. Hou, and D. Huang, "On the finite time blowup of the De Gregorio model for the 3D
  Euler equations", *Comm. Pure Appl. Math.* 74 (2021), no. 6, 1282-1350; numbering of
  arXiv:1905.06387v3, Section 4, (4.1)-(4.3), p. 15, and Section 4.1.3, p. 18.
  <https://doi.org/10.1002/cpa.21991>
  <https://arxiv.org/abs/1905.06387v3>
-/

@[expose] public section

noncomputable section

open Set
open scoped Topology

namespace DeGregorio

variable {fields : Fields} {spatialRate vorticityRate : ℝ → ℝ} {times : Set ℝ}

/-- At a common zero of vorticity and velocity, the origin slope evolves by the
difference of the total scaling rates. The advection parameter is `a = 1`. -/
theorem hasDerivAt_origin_slope
    (htransport : SatisfiesRescaledTransportEquationOn 1 fields
      spatialRate vorticityRate times)
    {t : ℝ} (ht : t ∈ times)
    (hω : ContDiffAt ℝ 2 (Function.uncurry fields.vorticity) (0, t))
    (hu : ContDiffAt ℝ 2 (fun x ↦ fields.velocity x t) 0)
    (hωzero : fields.vorticity 0 t = 0) (huzero : fields.velocity 0 t = 0) :
    HasDerivAt (fun s ↦ deriv (fun x ↦ fields.vorticity x s) 0)
      ((vorticityRate t - spatialRate t) * deriv (fun x ↦ fields.vorticity x t) 0) t := by
  have hωspace : ContDiffAt ℝ 2 (fun x ↦ fields.vorticity x t) 0 :=
    hω.comp 0 (contDiffAt_id.prodMk contDiffAt_const)
  have hωx := (hωspace.differentiableAt two_ne_zero).hasDerivAt
  have hωxx :=
    ((hωspace.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  have hux := (hu.differentiableAt two_ne_zero).hasDerivAt
  have huxx :=
    ((hu.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasDerivAt
  have hproduction :=
    (((hasDerivAt_const 0 (vorticityRate t)).add huxx).mul hωx).sub
      ((((hasDerivAt_id 0).const_mul (spatialRate t)).add hux).mul hωxx)
  have hequation : (fun x ↦ deriv (fields.vorticity x) t) =
      fun x ↦ (vorticityRate t + deriv (fun y ↦ fields.velocity y t) x) *
        fields.vorticity x t -
        (spatialRate t * x + fields.velocity x t) *
          deriv (fun y ↦ fields.vorticity y t) x := by
    funext x
    simpa only [one_mul] using eq_sub_of_add_eq (htransport (x := x) ht)
  have hslope := PDE.Analysis.Calculus.hasDerivAt_spatial_deriv hω
  apply hslope.congr_deriv
  rw [hequation]
  refine hproduction.deriv.trans ?_
  simp only [Pi.add_apply, id_eq, hωzero, huzero, mul_zero, zero_mul, add_zero, zero_add,
    mul_one]
  cas

/-- Equal total scaling rates make the origin slope stationary, as in paper (4.3). -/
theorem hasDerivAt_origin_slope_zero
    {rate : ℝ → ℝ}
    (htransport : SatisfiesRescaledTransportEquationOn 1 fields rate rate times)
    {t : ℝ} (ht : t ∈ times)
    (hω : ContDiffAt ℝ 2 (Function.uncurry fields.vorticity) (0, t))
    (hu : ContDiffAt ℝ 2 (fun x ↦ fields.velocity x t) 0)
    (hωzero : fields.vorticity 0 t = 0) (huzero : fields.velocity 0 t = 0) :
    HasDerivAt (fun s ↦ deriv (fun x ↦ fields.vorticity x s) 0) 0 t := by
  simpa only [sub_self, zero_mul] using
    hasDerivAt_origin_slope htransport ht hω hu hωzero huzero

/-- Under equal total rates, the origin slope agrees at the endpoints of every
closed time interval on which the origin regularity and normalization hold. -/
theorem origin_slope_eq
    {rate : ℝ → ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (htransport : SatisfiesRescaledTransportEquationOn 1 fields rate rate (Icc t₀ t₁))
    (hω : ∀ s ∈ Icc t₀ t₁, ContDiffAt ℝ 2 (Function.uncurry fields.vorticity) (0, s))
    (hu : ∀ s ∈ Icc t₀ t₁, ContDiffAt ℝ 2 (fun x ↦ fields.velocity x s) 0)
    (hωzero : ∀ s ∈ Icc t₀ t₁, fields.vorticity 0 s = 0)
    (huzero : ∀ s ∈ Icc t₀ t₁, fields.velocity 0 s = 0) :
    deriv (fun x ↦ fields.vorticity x t₁) 0 =
      deriv (fun x ↦ fields.vorticity x t₀) 0 := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (hs : s ∈ uIcc t₀ t₁) ↦
      hasDerivAt_origin_slope_zero htransport (uIcc_of_le ht ▸ hs)
        (hω s (uIcc_of_le ht ▸ hs)) (hu s (uIcc_of_le ht ▸ hs))
        (hωzero s (uIcc_of_le ht ▸ hs)) (huzero s (uIcc_of_le ht ▸ hs)))
    (intervalIntegrable_const (c := (0 : ℝ)))
  exact sub_eq_zero.mp (by simpa using hftc.symm)

/-- Under equal rates, if the perturbation `ω(·, t₀) - ω̄` has zero slope at the origin,
so does `ω(·, t₁) - ω̄`. The profile `ω̄` is fixed and differentiable at `0`. -/
theorem perturbation_origin_slope_eq_zero
    {rate : ℝ → ℝ} {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (htransport : SatisfiesRescaledTransportEquationOn 1 fields rate rate (Icc t₀ t₁))
    (hω : ∀ s ∈ Icc t₀ t₁, ContDiffAt ℝ 2 (Function.uncurry fields.vorticity) (0, s))
    (hu : ∀ s ∈ Icc t₀ t₁, ContDiffAt ℝ 2 (fun x ↦ fields.velocity x s) 0)
    (hωzero : ∀ s ∈ Icc t₀ t₁, fields.vorticity 0 s = 0)
    (huzero : ∀ s ∈ Icc t₀ t₁, fields.velocity 0 s = 0)
    {omegaBar : ℝ → ℝ} (hbar : DifferentiableAt ℝ omegaBar 0)
    (hinitial : deriv (fun x ↦ fields.vorticity x t₀ - omegaBar x) 0 = 0) :
    deriv (fun x ↦ fields.vorticity x t₁ - omegaBar x) 0 = 0 := by
  have hω₀ : DifferentiableAt ℝ (fun x ↦ fields.vorticity x t₀) 0 :=
    ((hω t₀ (left_mem_Icc.mpr ht)).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt two_ne_zero
  have hω₁ : DifferentiableAt ℝ (fun x ↦ fields.vorticity x t₁) 0 :=
    ((hω t₁ (right_mem_Icc.mpr ht)).comp 0
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt two_ne_zero
  rw [deriv_fun_sub hω₁ hbar, origin_slope_eq ht htransport hω hu hωzero huzero]
  simpa only [deriv_fun_sub hω₀ hbar] using hinitial

end DeGregorio
