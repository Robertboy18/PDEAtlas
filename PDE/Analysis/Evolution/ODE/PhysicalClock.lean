/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Positive clocks and finite lifetime

A clock with positive derivative is strictly increasing on a convex time domain.
If a continuous strictly increasing clock on `[t₀, ∞)` converges to a finite
lifetime `T`, its image is `[clock t₀, T)`. For a continuous rate `r` that is
positive on `(0, ∞)` and integrable, the clock `t ↦ ∫₀ᵗ r` is of this kind, with
image `[0, ∫₀^∞ r)`.

A clock `T` with a positive strict derivative `r` at every time is inverted by
`Function.invFun T`: the inverse recovers every time, the range of `T` is open, the inverse has
strict derivative `(r τ)⁻¹` at `T τ`, and it is `C¹` on the range when `r` is continuous. These
are the inverse clocks of the dynamic rescalings, whose physical time is the integral of a
positive amplitude.

## Main results

* `strictMonoOn_physicalTime_of_hasDerivAt_pos`, `image_Ici_eq_Ico_of_strictMonoOn_tendsto`.
* `strictMonoOn_physicalTimeIntegral`, `image_physicalTimeIntegral_Ici`: the integral clock and
  its finite lifetime.
* `leftInverse_invFun_of_hasDerivAt_pos`, `hasStrictDerivAt_invFun_of_hasStrictDerivAt_pos`,
  `isOpen_range_of_hasStrictDerivAt_pos`, `contDiffOn_invFun_of_hasStrictDerivAt_pos`: the
  inverse clock.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE.Analysis.Evolution.ODE

/-- A physical-time clock with a positive rate is strictly increasing on any
convex rescaled-time domain where its differential law holds.

Consequently the clock is injective there and
`StrictMonoOn.orderIso` supplies an order isomorphism from `rescaledTimes` to
its physical-time image. -/
theorem strictMonoOn_physicalTime_of_hasDerivAt_pos
    (physicalTime clockRate : ℝ → ℝ) (rescaledTimes : Set ℝ)
    (hconvex : Convex ℝ rescaledTimes)
    (hclock : ∀ τ ∈ rescaledTimes,
      HasDerivAt physicalTime (clockRate τ) τ)
    (hclockRate : ∀ τ ∈ interior rescaledTimes, 0 < clockRate τ) :
    StrictMonoOn physicalTime rescaledTimes := by
  apply strictMonoOn_of_deriv_pos hconvex
  · intro τ hτ
    exact (hclock τ hτ).continuousAt.continuousWithinAt
  · intro τ hτ
    rw [(hclock τ (interior_subset hτ)).deriv]
    exact hclockRate τ hτ

/-- A continuous strictly increasing clock on a forward half-line whose
values converge to a finite lifetime parametrizes exactly the half-open
interval from its initial value to that lifetime.

In particular, the limiting lifetime is never attained at a finite rescaled
time. -/
theorem image_Ici_eq_Ico_of_strictMonoOn_tendsto
    (physicalTime : ℝ → ℝ) (initialTime lifetime : ℝ)
    (hcontinuous : ContinuousOn physicalTime (Set.Ici initialTime))
    (hmono : StrictMonoOn physicalTime (Set.Ici initialTime))
    (hlifetime : Filter.Tendsto physicalTime Filter.atTop (nhds lifetime)) :
    physicalTime '' Set.Ici initialTime =
      Set.Ico (physicalTime initialTime) lifetime := by
  apply Set.Subset.antisymm
  · rintro _ ⟨time, htime, rfl⟩
    have hinitialMem : initialTime ∈ Set.Ici initialTime := by simp
    have hlower : physicalTime initialTime ≤ physicalTime time :=
      hmono.monotoneOn hinitialMem htime htime
    refine ⟨hlower, ?_⟩
    have htimeGe : initialTime ≤ time := htime
    have hnextMem : time + 1 ∈ Set.Ici initialTime := by
      exact htimeGe.trans (by linarith)
    have hnext : physicalTime time < physicalTime (time + 1) :=
      hmono htime hnextMem (by linarith)
    have hnextLifetime : physicalTime (time + 1) ≤ lifetime := by
      apply ge_of_tendsto hlifetime
      filter_upwards [Filter.eventually_ge_atTop (time + 1)] with later hlater
      exact hmono.monotoneOn hnextMem
        (hnextMem.trans hlater) hlater
    exact hnext.trans_le hnextLifetime
  · intro value hvalue
    have heventuallyAbove :
        ∀ᶠ time in Filter.atTop, value < physicalTime time :=
      (tendsto_order.1 hlifetime).1 value hvalue.2
    obtain ⟨time, htimeInitial, hvalueTime⟩ :=
      ((Filter.eventually_ge_atTop initialTime).and
        heventuallyAbove).exists
    have hcontinuousIcc :
        ContinuousOn physicalTime (Set.Icc initialTime time) :=
      hcontinuous.mono Set.Icc_subset_Ici_self
    have hmonoIcc :
        MonotoneOn physicalTime (Set.Icc initialTime time) :=
      hmono.monotoneOn.mono Set.Icc_subset_Ici_self
    have hvalueIcc :
        value ∈ Set.Icc (physicalTime initialTime) (physicalTime time) :=
      ⟨hvalue.1, hvalueTime.le⟩
    rw [← hcontinuousIcc.image_Icc_of_monotoneOn htimeInitial hmonoIcc]
      at hvalueIcc
    exact Set.image_mono Set.Icc_subset_Ici_self hvalueIcc

/-- The accumulated clock of a continuous rate that is positive after the initial
time is strictly increasing on the closed half-line `[0, ∞)`. -/
theorem strictMonoOn_physicalTimeIntegral
    (clockRate : ℝ → ℝ)
    (hcontinuous : Continuous clockRate)
    (hpositive : ∀ time ∈ Set.Ioi (0 : ℝ), 0 < clockRate time) :
    StrictMonoOn (fun time ↦ ∫ s in (0 : ℝ)..time, clockRate s) (Set.Ici (0 : ℝ)) := by
  apply strictMonoOn_physicalTime_of_hasDerivAt_pos
    (fun time ↦ ∫ s in (0 : ℝ)..time, clockRate s) clockRate (Set.Ici (0 : ℝ)) (convex_Ici 0)
  · intro time _htime
    exact intervalIntegral.integral_hasDerivAt_right
      (hcontinuous.intervalIntegrable _ _)
      hcontinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hcontinuous.continuousAt
  · simpa only [interior_Ici] using hpositive

/-- A continuous positive integrable clock rate parametrizes exactly the
half-open physical-time interval before its total lifetime. -/
theorem image_physicalTimeIntegral_Ici
    (clockRate : ℝ → ℝ)
    (hcontinuous : Continuous clockRate)
    (hpositive : ∀ time ∈ Set.Ioi (0 : ℝ), 0 < clockRate time)
    (hintegrable : MeasureTheory.IntegrableOn clockRate (Set.Ioi (0 : ℝ))) :
    (fun time ↦ ∫ s in (0 : ℝ)..time, clockRate s) '' Set.Ici (0 : ℝ) =
      Set.Ico 0 (∫ s in Set.Ioi (0 : ℝ), clockRate s) := by
  let physicalTime := fun time : ℝ ↦
    ∫ s in (0 : ℝ)..time, clockRate s
  have hmono : StrictMonoOn physicalTime (Set.Ici (0 : ℝ)) :=
    strictMonoOn_physicalTimeIntegral clockRate hcontinuous hpositive
  have himage := image_Ici_eq_Ico_of_strictMonoOn_tendsto
    physicalTime 0 (∫ s in Set.Ioi (0 : ℝ), clockRate s)
    ((intervalIntegral.differentiable_integral_of_continuous hcontinuous).continuous.continuousOn)
    hmono (intervalIntegral_tendsto_integral_Ioi 0 hintegrable tendsto_id)
  simpa [physicalTime] using himage

section Inverse

variable {T r : ℝ → ℝ}

/-- A clock with a positive derivative at every time is recovered by its chosen inverse
`Function.invFun T`. -/
theorem leftInverse_invFun_of_hasDerivAt_pos (hT : ∀ τ, HasDerivAt T (r τ) τ)
    (hr : ∀ τ, 0 < r τ) : Function.LeftInverse (Function.invFun T) T :=
  Function.leftInverse_invFun (strictMono_of_hasDerivAt_pos hT hr).injective

/-- The chosen inverse of a clock with positive strict derivative `r` has strict derivative
`(r τ)⁻¹` at `T τ`. -/
theorem hasStrictDerivAt_invFun_of_hasStrictDerivAt_pos (hT : ∀ τ, HasStrictDerivAt T (r τ) τ)
    (hr : ∀ τ, 0 < r τ) (τ : ℝ) : HasStrictDerivAt (Function.invFun T) (r τ)⁻¹ (T τ) :=
  (hT τ).to_local_left_inverse (hr τ).ne' (Eventually.of_forall
    (leftInverse_invFun_of_hasDerivAt_pos (fun s ↦ (hT s).hasDerivAt) hr))

/-- The range of a clock with positive strict derivative at every time is open. -/
theorem isOpen_range_of_hasStrictDerivAt_pos (hT : ∀ τ, HasStrictDerivAt T (r τ) τ)
    (hr : ∀ τ, 0 < r τ) : IsOpen (range T) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨τ, rfl⟩
  rw [← (hT τ).map_nhds_eq (hr τ).ne']
  exact Filter.mem_map.2 (Filter.univ_mem' fun s ↦ mem_range_self s)

/-- With a continuous positive rate, the chosen inverse of the clock is continuously
differentiable on the range of the clock. -/
theorem contDiffOn_invFun_of_hasStrictDerivAt_pos (hT : ∀ τ, HasStrictDerivAt T (r τ) τ)
    (hr : ∀ τ, 0 < r τ) (hrc : Continuous r) :
    ContDiffOn ℝ 1 (Function.invFun T) (range T) := by
  have hinv := leftInverse_invFun_of_hasDerivAt_pos (fun s ↦ (hT s).hasDerivAt) hr
  have hderiv := hasStrictDerivAt_invFun_of_hasStrictDerivAt_pos hT hr
  have hdiff : DifferentiableOn ℝ (Function.invFun T) (range T) := by
    rintro _ ⟨τ, rfl⟩
    exact (hderiv τ).hasDerivAt.differentiableAt.differentiableWithinAt
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
    contDiffOn_succ_iff_deriv_of_isOpen (isOpen_range_of_hasStrictDerivAt_pos hT hr)]
  refine ⟨hdiff, by simp, ?_⟩
  rw [contDiffOn_zero]
  refine ((hrc.comp_continuousOn hdiff.continuousOn).inv₀ fun t _ ↦ (hr _).ne').congr ?_
  rintro _ ⟨τ, rfl⟩
  rw [(hderiv τ).hasDerivAt.deriv]
  simp only [Pi.inv_apply, Function.comp_apply, hinv τ]

end Inverse

end PDE.Analysis.Evolution.ODE
