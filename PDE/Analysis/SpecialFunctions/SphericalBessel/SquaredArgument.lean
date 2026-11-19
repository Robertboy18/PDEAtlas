/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The reduced spherical Bessel functions in the squared variable

The reduced spherical Bessel function `g_l x = j_l x / x ^ l` is even, and
`reducedSphericalBesselJSq l` is the entire function `G_l` with `g_l x = G_l (x ^ 2)`. In the
squared variable the relations `g_l' = -x g_{l+1}` and `g_l = (2l + 3) g_{l+1} - x ^ 2 g_{l+2}`
become

`G_l' = -G_{l+1} / 2`  and  `G_l t = (2l + 3) G_{l+1} t - t G_{l+2} t`

at every real `t`. They hold for `t > 0` by the substitution `x = √t`, and everywhere by the
identity theorem for analytic functions. Together they give the reduced Bessel equation
`4 t G_l'' + (4l + 6) G_l' + G_l = 0`, the form used for fields `G_l (κ² ‖x‖²) q(x)` with a
homogeneous polynomial `q`.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.SpecialFunctions

open Filter Set
open scoped Topology

/-- `G_l t = g_l (√t)` for `t ≥ 0`. -/
theorem reducedSphericalBesselJSq_eq_sqrt (l : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    reducedSphericalBesselJSq l t = reducedSphericalBesselJ l (Real.sqrt t) := by
  rw [reducedSphericalBesselJ_eq_sq, Real.sq_sqrt ht]

private theorem hasDerivAt_reducedSphericalBesselJSq_of_pos (l : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (reducedSphericalBesselJSq l) (-reducedSphericalBesselJSq (l + 1) t / 2) t := by
  have hs := Real.hasDerivAt_sqrt ht.ne'
  have hg := (hasDerivAt_reducedSphericalBesselJ l (Real.sqrt t)).comp t hs
  have hev : reducedSphericalBesselJSq l =ᶠ[𝓝 t] reducedSphericalBesselJ l ∘ Real.sqrt := by
    filter_upwards [lt_mem_nhds ht] with u hu
    exact reducedSphericalBesselJSq_eq_sqrt l hu.le
  refine (hg.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [reducedSphericalBesselJSq_eq_sqrt (l + 1) ht.le]
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  field_simp

/-- `G_l` has derivative `-G_{l+1} / 2` everywhere. -/
theorem deriv_reducedSphericalBesselJSq (l : ℕ) :
    deriv (reducedSphericalBesselJSq l) = fun t ↦ -reducedSphericalBesselJSq (l + 1) t / 2 := by
  refine AnalyticOnNhd.eq_of_eventuallyEq (z₀ := (1 : ℝ))
    (analyticOnNhd_reducedSphericalBesselJSq l).deriv ?_ ?_
  · exact ((analyticOnNhd_reducedSphericalBesselJSq (l + 1)).neg).div_const
  · filter_upwards [lt_mem_nhds one_pos] with t ht
    exact (hasDerivAt_reducedSphericalBesselJSq_of_pos l ht).deriv

/-- `G_l' = -G_{l+1} / 2` at every real point. -/
theorem hasDerivAt_reducedSphericalBesselJSq (l : ℕ) (t : ℝ) :
    HasDerivAt (reducedSphericalBesselJSq l) (-reducedSphericalBesselJSq (l + 1) t / 2) t := by
  have h := ((contDiff_reducedSphericalBesselJSq l (n := 1)).differentiable one_ne_zero
    t).hasDerivAt
  rwa [deriv_reducedSphericalBesselJSq] at h

/-- The three-term relation `G_l t = (2l + 3) G_{l+1} t - t G_{l+2} t` at every real `t`. -/
theorem reducedSphericalBesselJSq_eq_sub (l : ℕ) (t : ℝ) :
    reducedSphericalBesselJSq l t = (2 * l + 3) * reducedSphericalBesselJSq (l + 1) t -
      t * reducedSphericalBesselJSq (l + 2) t := by
  have h := AnalyticOnNhd.eq_of_eventuallyEq (z₀ := (1 : ℝ))
    (f := reducedSphericalBesselJSq l)
    (g := fun t ↦ (2 * l + 3) * reducedSphericalBesselJSq (l + 1) t -
      t * reducedSphericalBesselJSq (l + 2) t)
    (analyticOnNhd_reducedSphericalBesselJSq l)
    ((analyticOnNhd_const.mul (analyticOnNhd_reducedSphericalBesselJSq (l + 1))).sub
      (analyticOnNhd_id.mul (analyticOnNhd_reducedSphericalBesselJSq (l + 2)))) ?_
  · exact congrFun h t
  · filter_upwards [lt_mem_nhds one_pos] with u hu
    simp only [reducedSphericalBesselJSq_eq_sqrt _ hu.le]
    rw [reducedSphericalBesselJ_eq_sub l (Real.sqrt u), Real.sq_sqrt hu.le]

/-- The second derivative `G_l'' = G_{l+2} / 4`. -/
theorem deriv_deriv_reducedSphericalBesselJSq (l : ℕ) :
    deriv (deriv (reducedSphericalBesselJSq l)) =
      fun t ↦ reducedSphericalBesselJSq (l + 2) t / 4 := by
  funext t
  rw [deriv_reducedSphericalBesselJSq]
  have h : HasDerivAt (fun t ↦ -reducedSphericalBesselJSq (l + 1) t / 2)
      (-(-reducedSphericalBesselJSq (l + 2) t / 2) / 2) t :=
    ((hasDerivAt_reducedSphericalBesselJSq (l + 1) t).neg).div_const 2
  rw [h.deriv]
  ring

/-- The reduced Bessel equation in the squared variable,
`4 t G_l'' + (4l + 6) G_l' + G_l = 0`, at every real `t`. -/
theorem reducedSphericalBesselJSq_ode (l : ℕ) (t : ℝ) :
    4 * t * deriv (deriv (reducedSphericalBesselJSq l)) t +
        (4 * l + 6) * deriv (reducedSphericalBesselJSq l) t +
      reducedSphericalBesselJSq l t = 0 := by
  rw [deriv_deriv_reducedSphericalBesselJSq, deriv_reducedSphericalBesselJSq,
    reducedSphericalBesselJSq_eq_sub l t]
  ring

end PDE.Analysis.SpecialFunctions
