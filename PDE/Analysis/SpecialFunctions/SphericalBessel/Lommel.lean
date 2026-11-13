/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Lommel's integral for spherical Bessel functions

The functions `f r = j_l (α r)` and `g r = j_l (β r)` satisfy
`(r ^ 2 f')' = (l (l + 1) - α ^ 2 r ^ 2) f` and the same equation with `β`, so the weighted
Wronskian `W r = r ^ 2 (f g' - f' g)` has
derivative `(α ^ 2 - β ^ 2) r ^ 2 f g`. Integrating from `0` gives Lommel's formula
`(α ^ 2 - β ^ 2) ∫_0^R r ^ 2 j_l (α r) j_l (β r) dr = R ^ 2 (β j_l (α R) j_l' (β R) -
α j_l' (α R) j_l (β R))`. In particular the functions `r ↦ j_l (α r)` with `α ^ 2` distinct
and a common homogeneous boundary condition at `R` are orthogonal in `L²(r ^ 2 dr)`. For
`α = β` the function `(r / 2) ((α ^ 2 r ^ 2 - l (l + 1)) f ^ 2 + r ^ 2 f' ^ 2 + r f f')` is a
primitive of `α ^ 2 r ^ 2 f ^ 2`, which gives the normalization integral.

## Main results

* `hasDerivAt_sphericalBesselJ_wronskian_comp_mul`: the derivative of `W`.
* `integral_sq_mul_sphericalBesselJ_mul_sphericalBesselJ`: Lommel's formula.
* `integral_sq_mul_sphericalBesselJ_mul_sphericalBesselJ_eq_zero`: the orthogonality it gives.
* `integral_sq_mul_sphericalBesselJ_sq`: the normalization integral
  `α ^ 2 ∫_0^R r ^ 2 j_l (α r) ^ 2 dr` in terms of `j_l (α R)` and `j_l' (α R)`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open Set

/-- `r ↦ j_l (a r)` has derivative `a j_l' (a r)`. -/
theorem hasDerivAt_sphericalBesselJ_comp_mul (l : ℕ) (a r : ℝ) :
    HasDerivAt (fun s ↦ sphericalBesselJ l (a * s)) (a * deriv (sphericalBesselJ l) (a * r)) r := by
  have h := ((differentiable_sphericalBesselJ l) (a * r)).hasDerivAt.comp r
    ((hasDerivAt_id' r).const_mul a)
  refine h.congr_deriv ?_
  ring

/-- `r ↦ j_l' (a r)` has derivative `a j_l'' (a r)`. -/
theorem hasDerivAt_deriv_sphericalBesselJ_comp_mul (l : ℕ) (a r : ℝ) :
    HasDerivAt (fun s ↦ deriv (sphericalBesselJ l) (a * s))
      (a * deriv (deriv (sphericalBesselJ l)) (a * r)) r := by
  have h := (hasDerivAt_deriv_sphericalBesselJ l (a * r)).comp r ((hasDerivAt_id' r).const_mul a)
  refine h.congr_deriv ?_
  ring

/-- The weighted Wronskian of `r ↦ j_l (α r)` and `r ↦ j_l (β r)` has derivative
`(α ^ 2 - β ^ 2) r ^ 2 j_l (α r) j_l (β r)`. -/
theorem hasDerivAt_sphericalBesselJ_wronskian_comp_mul (l : ℕ) (α β r : ℝ) :
    HasDerivAt (fun s ↦ s ^ 2 * (sphericalBesselJ l (α * s) *
        (β * deriv (sphericalBesselJ l) (β * s)) -
        α * deriv (sphericalBesselJ l) (α * s) * sphericalBesselJ l (β * s)))
      ((α ^ 2 - β ^ 2) * (r ^ 2 * sphericalBesselJ l (α * r) * sphericalBesselJ l (β * r))) r := by
  have hf := hasDerivAt_sphericalBesselJ_comp_mul l α r
  have hf' := (hasDerivAt_deriv_sphericalBesselJ_comp_mul l α r).const_mul α
  have hg := hasDerivAt_sphericalBesselJ_comp_mul l β r
  have hg' := (hasDerivAt_deriv_sphericalBesselJ_comp_mul l β r).const_mul β
  have h := (hasDerivAt_pow 2 r).mul ((hf.mul hg').sub (hf'.mul hg))
  refine h.congr_deriv ?_
  have hα := sphericalBesselJ_ode l (α * r)
  have hβ := sphericalBesselJ_ode l (β * r)
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.sub_apply, Pi.mul_apply]
  linear_combination sphericalBesselJ l (α * r) * hβ - sphericalBesselJ l (β * r) * hα

/-- **Lommel's integral**: `(α ^ 2 - β ^ 2) ∫_0^R r ^ 2 j_l (α r) j_l (β r) dr =
R ^ 2 (β j_l (α R) j_l' (β R) - α j_l' (α R) j_l (β R))`. -/
theorem integral_sq_mul_sphericalBesselJ_mul_sphericalBesselJ (l : ℕ) (α β R : ℝ) :
    (α ^ 2 - β ^ 2) * ∫ r in (0 : ℝ)..R,
        r ^ 2 * sphericalBesselJ l (α * r) * sphericalBesselJ l (β * r) =
      R ^ 2 * (β * sphericalBesselJ l (α * R) * deriv (sphericalBesselJ l) (β * R) -
        α * deriv (sphericalBesselJ l) (α * R) * sphericalBesselJ l (β * R)) := by
  have hcont : Continuous fun r : ℝ ↦
      (α ^ 2 - β ^ 2) * (r ^ 2 * sphericalBesselJ l (α * r) * sphericalBesselJ l (β * r)) := by
    have := continuous_sphericalBesselJ l
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ ↦ hasDerivAt_sphericalBesselJ_wronskian_comp_mul l α β r)
    (hcont.intervalIntegrable 0 R)
  rw [intervalIntegral.integral_const_mul] at h
  rw [h]
  ring

/-- Orthogonality: if `α ^ 2 ≠ β ^ 2` and `β j_l (α R) j_l' (β R) = α j_l' (α R) j_l (β R)`,
for instance when both `α R` and `β R` are zeros of `j_l`, then
`∫_0^R r ^ 2 j_l (α r) j_l (β r) dr = 0`. -/
theorem integral_sq_mul_sphericalBesselJ_mul_sphericalBesselJ_eq_zero {l : ℕ} {α β R : ℝ}
    (hαβ : α ^ 2 ≠ β ^ 2)
    (hR : β * sphericalBesselJ l (α * R) * deriv (sphericalBesselJ l) (β * R) =
      α * deriv (sphericalBesselJ l) (α * R) * sphericalBesselJ l (β * R)) :
    ∫ r in (0 : ℝ)..R, r ^ 2 * sphericalBesselJ l (α * r) * sphericalBesselJ l (β * r) = 0 := by
  have h := integral_sq_mul_sphericalBesselJ_mul_sphericalBesselJ l α β R
  rw [hR, sub_self, mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hαβ)

/-- The primitive of `α ^ 2 r ^ 2 j_l (α r) ^ 2`. -/
theorem hasDerivAt_sphericalBesselJ_norm_primitive (l : ℕ) (α r : ℝ) :
    HasDerivAt (fun s ↦ s / 2 * ((α ^ 2 * s ^ 2 - l * (l + 1)) * sphericalBesselJ l (α * s) ^ 2 +
        α ^ 2 * s ^ 2 * deriv (sphericalBesselJ l) (α * s) ^ 2 +
        α * s * sphericalBesselJ l (α * s) * deriv (sphericalBesselJ l) (α * s)))
      (α ^ 2 * (r ^ 2 * sphericalBesselJ l (α * r) ^ 2)) r := by
  have hf := hasDerivAt_sphericalBesselJ_comp_mul l α r
  have hf' := hasDerivAt_deriv_sphericalBesselJ_comp_mul l α r
  have hid := hasDerivAt_id' r
  have hsq := hasDerivAt_pow 2 r
  have h := (hid.div_const 2).mul (((((hsq.const_mul (α ^ 2)).sub_const ((l : ℝ) * (l + 1))).mul
    (hf.pow 2)).add ((hsq.const_mul (α ^ 2)).mul (hf'.pow 2))).add
    (((hid.const_mul α).mul hf).mul hf'))
  refine h.congr_deriv ?_
  have hα := sphericalBesselJ_ode l (α * r)
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.add_apply, Pi.mul_apply,
    Pi.pow_apply]
  linear_combination (α * r * deriv (sphericalBesselJ l) (α * r) +
    sphericalBesselJ l (α * r) / 2) * hα

/-- **Normalization integral**: `α ^ 2 ∫_0^R r ^ 2 j_l (α r) ^ 2 dr =
(R / 2) ((α ^ 2 R ^ 2 - l (l + 1)) j_l (α R) ^ 2 + α ^ 2 R ^ 2 j_l' (α R) ^ 2 +
α R j_l (α R) j_l' (α R))`. -/
theorem integral_sq_mul_sphericalBesselJ_sq (l : ℕ) (α R : ℝ) :
    α ^ 2 * ∫ r in (0 : ℝ)..R, r ^ 2 * sphericalBesselJ l (α * r) ^ 2 =
      R / 2 * ((α ^ 2 * R ^ 2 - l * (l + 1)) * sphericalBesselJ l (α * R) ^ 2 +
        α ^ 2 * R ^ 2 * deriv (sphericalBesselJ l) (α * R) ^ 2 +
        α * R * sphericalBesselJ l (α * R) * deriv (sphericalBesselJ l) (α * R)) := by
  have hcont : Continuous fun r : ℝ ↦ α ^ 2 * (r ^ 2 * sphericalBesselJ l (α * r) ^ 2) := by
    have := continuous_sphericalBesselJ l
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ ↦ hasDerivAt_sphericalBesselJ_norm_primitive l α r) (hcont.intervalIntegrable 0 R)
  rw [intervalIntegral.integral_const_mul] at h
  rw [h]
  ring

end PDE.Analysis.SpecialFunctions
