/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.Regularity
public import PDE.Parabolic.Heat.MeanValue.Closure
public import PDE.Parabolic.Heat.MeanValue.Terminal

/-!
# The local C² in space, C¹ in time heat-ball formula

Continuous spatial derivatives through order two and a continuous first time
derivative give the heat-ball mean value on an open spatial domain and the
half-open time interval `(0, T]`. The time derivative at the terminal endpoint
is taken within that interval. The heat equation is only required at interior
times; the terminal identity follows by continuity.

The integral is over the closed heat ball. `closure_heatBall_eq_insert_pole`
identifies this set with the weak kernel superlevel, including its pole. This
is the closed region in Evans's mean-value theorem, §2.3.2. No mixed
derivative, second time derivative, smooth extension, or boundary regularity of
the spatial domain is assumed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.3.2, Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime time)

namespace HeatEquation

open MeasureTheory Set
open PDE.Common
open scoped Topology

variable {n : ℕ}

/-- The local heat-ball identity from C² spatial and C¹ temporal data.
The conclusion includes integrability, and permits the pole at the terminal
time. The spatial domain may be any open set. -/
theorem heatBall_meanValue_of_space_time_derivatives
    (hn : 0 < n) {U : Set (ℝ^n)} (hU : IsOpen U) {T : ℝ}
    {u : ℝ^n → ℝ → ℝ}
    {Dx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ} {Dt : ℝ^n × ℝ → ℝ}
    {Dxx : ℝ^n × ℝ → ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ}
    (huContinuous : ContinuousOn (Function.uncurry u) (U ×ˢ Ioc 0 T))
    (hDx : ContinuousOn Dx (U ×ˢ Ioc 0 T))
    (hDt : ContinuousOn Dt (U ×ˢ Ioc 0 T))
    (hDxx : ContinuousOn Dxx (U ×ˢ Ioc 0 T))
    (hspace : ∀ p ∈ U ×ˢ Ioc 0 T, HasFDerivAt (fun y ↦ u y p.2) (Dx p) p.1)
    (htime : ∀ p ∈ U ×ˢ Ioc 0 T, HasDerivWithinAt (u p.1) (Dt p) (Ioc 0 T) p.2)
    (hhessian : ∀ p ∈ U ×ˢ Ioc 0 T,
      HasFDerivAt (fun y ↦ Dx (y, p.2)) (Dxx p) p.1)
    (hcaloric : ∀ y ∈ U, ∀ s ∈ Ioo 0 T, heatParabolicOperator u y s = 0)
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r)
    (hclosure : closure (heatBall x t r) ⊆
      {p | spatialPart p ∈ U ∧ time p ∈ Ioc 0 T}) :
    IntegrableOn (fun p ↦ heatBallWeight x t p * spaceTimeUncurry u p)
        (closure (heatBall x t r)) ∧
      (∫ p in closure (heatBall x t r), heatBallWeight x t p * spaceTimeUncurry u p) =
        4 * r ^ n * u x t := by
  let O := {p : SpaceTime n | spatialPart p ∈ U ∧ time p ∈ Ioo 0 T}
  have hO : IsOpen O :=
    (hU.prod isOpen_Ioo).preimage (spaceTimeContinuousLinearEquiv n).continuous
  have hcontinuous : ContinuousOn (spaceTimeUncurry u)
      {p | spatialPart p ∈ U ∧ time p ∈ Ioc 0 T} :=
    huContinuous.comp (spaceTimeContinuousLinearEquiv n).continuous.continuousOn
      (fun _ hp ↦ hp)
  have hproduct := PDE.Analysis.contDiffOn_one_of_space_time_derivatives
    hU hDx hDt hspace htime
  rw [interior_Ioc] at hproduct
  have hjoint : ContDiffOn ℝ 1 (spaceTimeUncurry u) O :=
    hproduct.comp (spaceTimeContinuousLinearEquiv n).contDiff.contDiffOn (fun _ hp ↦ hp)
  have hslices (s : ℝ) (hs : s ∈ Ioo 0 T) :
      ContDiffOn ℝ 2 (fun y ↦ spaceTimeUncurry u (timeSpaceCons s y)) U := by
    simpa only [spaceTimeUncurry, spatialPart_timeSpaceCons, time, timeSpaceCons_zero] using
      PDE.Analysis.contDiffOn_two_slice_of_space_derivatives hU hDxx hspace hhessian
        (Ioo_subset_Ioc_self hs)
  have hnative (p : SpaceTime n) (hp : spatialPart p ∈ U) (ht : time p ∈ Ioo 0 T) :
      heatOperator (spaceTimeUncurry u) p = 0 := by
    have hdiff : DifferentiableAt ℝ (spaceTimeUncurry u) p :=
      ((hjoint p ⟨hp, ht⟩).contDiffAt (hO.mem_nhds ⟨hp, ht⟩)).differentiableAt
        (by norm_num)
    have hbridge := heatParabolicOperator_eq_heatOperator (spaceTimeUncurry u)
      (spatialPart p) (time p) (by simpa only [time, timeSpaceCons_spatialPart] using hdiff)
    have hbridge' : heatParabolicOperator u (spatialPart p) (time p) =
        heatOperator (spaceTimeUncurry u) p := by
      simpa only [spaceTimeUncurry, spatialPart_timeSpaceCons, time, timeSpaceCons_zero,
        timeSpaceCons_spatialPart] using hbridge
    exact hbridge'.symm.trans (hcaloric (spatialPart p) hp (time p) ht)
  have hae : closure (heatBall x t r) =ᵐ[volume] heatBall x t r :=
    closure_ae_eq_of_null_frontier (volume_frontier_heatBall hr)
  refine ⟨?_, ?_⟩
  · rw [integrableOn_congr_set_ae hae]
    exact integrableOn_heatBallWeight_mul hn hr (hcontinuous.mono hclosure)
  · rw [setIntegral_congr_set hae]
    simpa only [spaceTimeUncurry, spatialPart_timeSpaceCons, time, timeSpaceCons_zero] using
      heatBall_meanValue_on_cylinder hn hU hcontinuous hjoint hslices hnative x t hr hclosure

end HeatEquation
