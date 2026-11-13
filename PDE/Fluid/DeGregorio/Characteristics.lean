/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Model
import PDE.Representations.Similarity.Dynamic

/-!
# Vorticity along a De Gregorio characteristic

A path with velocity `a u` turns the transport equation into the scalar stretching
ODE `dω/dt = u_x ω`. An integrating factor then gives the vorticity along the path.
In particular, a particle carries zero vorticity precisely when it started with zero
vorticity, and nonzero vorticity keeps its sign.

The fields and the path are given. The statements take a primitive of the stretching
coefficient `s ↦ u_x(X(s), s)` as an explicit hypothesis, so no integrability condition
on that coefficient is needed.
-/

@[expose] public section

noncomputable section

open Set
open PDE.Representations.Similarity

namespace DeGregorio

variable {a : ℝ} {fields : Fields} {times : Set ℝ} {path : ℝ → ℝ}

/-- The material derivative along a path with velocity `a u` is the stretching term
of the De Gregorio transport equation. -/
theorem hasDerivAt_vorticity_characteristic
    (hregularity : HasClassicalRegularityOn fields times)
    (htransport : SatisfiesTransportEquationOn a fields times)
    {t : ℝ} (ht : t ∈ times)
    (hpath : HasDerivAt path (a * fields.velocity (path t) t) t) :
    HasDerivAt (fun s ↦ fields.vorticity (path s) s)
      (deriv (fun x ↦ fields.velocity x t) (path t) * fields.vorticity (path t) t) t := by
  have hω := hregularity.vorticity_differentiableAt (x := path t) ht
  have hcurve : HasDerivAt (fun s ↦ (path s, s))
      (a * fields.velocity (path t) t, 1) t :=
    hpath.prodMk (hasDerivAt_id t)
  have hcomp : HasDerivAt (fun s ↦ fields.vorticity (path s) s)
      (fderiv ℝ (Function.uncurry fields.vorticity) (path t, t)
        (a * fields.velocity (path t) t, 1)) t :=
    hω.hasFDerivAt.comp_hasDerivAt (f := fun s ↦ (path s, s)) t hcurve
  apply hcomp.congr_deriv
  rw [fderiv_uncurry_apply_prod fields.vorticity (path t)
    (a * fields.velocity (path t) t) t 1 hω]
  simpa only [fderiv_eq_smul_deriv, smul_eq_mul, one_mul, add_comm] using htransport ht

/-- Multiplication by the inverse stretching factor makes vorticity stationary
along a characteristic. -/
theorem hasDerivAt_vorticity_integratingFactor
    (hregularity : HasClassicalRegularityOn fields times)
    (htransport : SatisfiesTransportEquationOn a fields times)
    {t : ℝ} (ht : t ∈ times)
    (hpath : HasDerivAt path (a * fields.velocity (path t) t) t)
    {primitive : ℝ → ℝ}
    (hprimitive : HasDerivAt primitive
      (deriv (fun x ↦ fields.velocity x t) (path t)) t) :
    HasDerivAt (fun s ↦ fields.vorticity (path s) s * Real.exp (-primitive s)) 0 t := by
  convert (hasDerivAt_vorticity_characteristic hregularity htransport ht hpath).mul
    hprimitive.neg.exp using 1
  ring

/-- The characteristic formula on a closed time interval. The exponential is always
positive, so stretching changes magnitude but cannot create a new zero or change sign. -/
theorem vorticity_characteristic_eq
    {t₀ t : ℝ} (ht : t₀ ≤ t)
    (hregularity : HasClassicalRegularityOn fields (Icc t₀ t))
    (htransport : SatisfiesTransportEquationOn a fields (Icc t₀ t))
    (hpath : ∀ s ∈ Icc t₀ t, HasDerivAt path (a * fields.velocity (path s) s) s)
    {primitive : ℝ → ℝ}
    (hprimitive : ∀ s ∈ Icc t₀ t, HasDerivAt primitive
      (deriv (fun x ↦ fields.velocity x s) (path s)) s) :
    fields.vorticity (path t) t =
      fields.vorticity (path t₀) t₀ * Real.exp (primitive t - primitive t₀) := by
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (hs : s ∈ uIcc t₀ t) ↦
      hasDerivAt_vorticity_integratingFactor hregularity htransport
        (uIcc_of_le ht ▸ hs) (hpath s (uIcc_of_le ht ▸ hs))
        (hprimitive s (uIcc_of_le ht ▸ hs)))
    (intervalIntegrable_const (c := (0 : ℝ)))
  have hconstant :
      fields.vorticity (path t) t * Real.exp (-primitive t) =
        fields.vorticity (path t₀) t₀ * Real.exp (-primitive t₀) :=
    sub_eq_zero.mp (by simpa using hftc.symm)
  calc
    _ = (fields.vorticity (path t) t * Real.exp (-primitive t)) *
        Real.exp (primitive t) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = (fields.vorticity (path t₀) t₀ * Real.exp (-primitive t₀)) *
        Real.exp (primitive t) := by rw [hconstant]
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- Zero vorticity is preserved in both directions along a characteristic. -/
theorem vorticity_characteristic_eq_zero_iff
    {t₀ t : ℝ} (ht : t₀ ≤ t)
    (hregularity : HasClassicalRegularityOn fields (Icc t₀ t))
    (htransport : SatisfiesTransportEquationOn a fields (Icc t₀ t))
    (hpath : ∀ s ∈ Icc t₀ t, HasDerivAt path (a * fields.velocity (path s) s) s)
    {primitive : ℝ → ℝ}
    (hprimitive : ∀ s ∈ Icc t₀ t, HasDerivAt primitive
      (deriv (fun x ↦ fields.velocity x s) (path s)) s) :
    fields.vorticity (path t) t = 0 ↔ fields.vorticity (path t₀) t₀ = 0 := by
  rw [vorticity_characteristic_eq ht hregularity htransport hpath hprimitive,
    mul_eq_zero]
  simp only [Real.exp_ne_zero, or_false]

/-- Positive vorticity keeps its sign along the characteristic. -/
theorem vorticity_characteristic_pos_iff
    {t₀ t : ℝ} (ht : t₀ ≤ t)
    (hregularity : HasClassicalRegularityOn fields (Icc t₀ t))
    (htransport : SatisfiesTransportEquationOn a fields (Icc t₀ t))
    (hpath : ∀ s ∈ Icc t₀ t, HasDerivAt path (a * fields.velocity (path s) s) s)
    {primitive : ℝ → ℝ}
    (hprimitive : ∀ s ∈ Icc t₀ t, HasDerivAt primitive
      (deriv (fun x ↦ fields.velocity x s) (path s)) s) :
    0 < fields.vorticity (path t) t ↔ 0 < fields.vorticity (path t₀) t₀ := by
  rw [vorticity_characteristic_eq ht hregularity htransport hpath hprimitive]
  exact mul_pos_iff_of_pos_right (Real.exp_pos _)

/-- Negative vorticity keeps its sign along the characteristic. -/
theorem vorticity_characteristic_neg_iff
    {t₀ t : ℝ} (ht : t₀ ≤ t)
    (hregularity : HasClassicalRegularityOn fields (Icc t₀ t))
    (htransport : SatisfiesTransportEquationOn a fields (Icc t₀ t))
    (hpath : ∀ s ∈ Icc t₀ t, HasDerivAt path (a * fields.velocity (path s) s) s)
    {primitive : ℝ → ℝ}
    (hprimitive : ∀ s ∈ Icc t₀ t, HasDerivAt primitive
      (deriv (fun x ↦ fields.velocity x s) (path s)) s) :
    fields.vorticity (path t) t < 0 ↔ fields.vorticity (path t₀) t₀ < 0 := by
  rw [vorticity_characteristic_eq ht hregularity htransport hpath hprimitive]
  simpa only [zero_mul] using
    (mul_lt_mul_iff_left₀ (Real.exp_pos (primitive t - primitive t₀)) :
      fields.vorticity (path t₀) t₀ * Real.exp (primitive t - primitive t₀) <
        0 * Real.exp (primitive t - primitive t₀) ↔ fields.vorticity (path t₀) t₀ < 0)

end DeGregorio
