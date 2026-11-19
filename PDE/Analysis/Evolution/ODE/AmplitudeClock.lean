/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import PDE.Analysis.Evolution.Core.Gronwall
public import PDE.Analysis.Evolution.ODE.PhysicalClock
import Mathlib.Analysis.Calculus.LHopital
import CAS.ExactTactic

/-!
# Amplitude growth and exponential clock tails

For an amplitude satisfying `sU' = -cU * sU` with positive initial value
and `cU ≤ -gamma`, a weighted monotonicity argument gives positivity and
exponential growth. The resulting exponential majorant bounds the remaining
integral of a reciprocal clock.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open PDE.Analysis.Evolution
open scoped Topology

namespace PDE.Analysis.Evolution.ODE

/-- Positive initial amplitude stays positive when the rate has a constant upper bound.
No continuity or integrability of `cU` is required. The weighted amplitude
`sU(t) * exp ((1 - gamma) * t)` has strictly positive derivative at each positive level,
so it cannot reach half its initial value. -/
theorem amplitude_scale_pos
    (sU cU : ℝ → ℝ) (gamma : ℝ) (hsU0 : 0 < sU 0)
    (hscale : ∀ x ∈ Ici (0 : ℝ), HasDerivAt sU (-cU x * sU x) x)
    (hrate : ∀ x ∈ Ici (0 : ℝ), cU x ≤ -gamma)
    {t : ℝ} (ht : 0 ≤ t) : 0 < sU t := by
  let e := fun x : ℝ ↦ -(sU x * Real.exp ((1 - gamma) * x))
  have he (x : ℝ) (hx : 0 ≤ x) : HasDerivAt e
      ((cU x + gamma - 1) * (sU x * Real.exp ((1 - gamma) * x))) x := by
    have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp ((1 - gamma) * y))
        ((1 - gamma) * Real.exp ((1 - gamma) * x)) x := by
      cas
    exact ((hscale x hx).mul hexp).neg.congr_deriv (by cas)
  have hcont : ContinuousOn e (Icc 0 t) :=
    fun x hx ↦ (he x hx.1).continuousAt.continuousWithinAt
  have hlevel : e 0 < -(sU 0 / 2) := by
    simp only [e, mul_zero, Real.exp_zero, mul_one]
    linarith only [hsU0]
  have hbarrier : ∀ x ∈ Icc 0 t, e x = -(sU 0 / 2) → deriv e x < 0 := by
    intro x hx hxlevel
    have hw : sU x * Real.exp ((1 - gamma) * x) = sU 0 / 2 := by
      dsimp only [e] at hxlevel
      linarith only [hxlevel]
    rw [(he x hx.1).deriv, hw]
    have hc : cU x + gamma - 1 < 0 := by
      have hxrate := hrate x hx.1
      linarith only [hxrate]
    exact mul_neg_of_neg_of_pos hc (half_pos hsU0)
  have hstrict := strict_sublevel_invariant_of_deriv_neg_on_boundary
    hcont hlevel hbarrier t ⟨ht, le_rfl⟩
  have hweighted : 0 < sU t * Real.exp ((1 - gamma) * t) := by
    dsimp only [e] at hstrict
    linarith only [hstrict, hsU0]
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp hweighted

/-- A uniformly negative amplitude rate forces exponential growth of the
amplitude scale.  The proof applies monotonicity to
`sU(t) * exp (-gamma * t)`.
-/
theorem amplitude_scale_lower_bound
    (sU cU : ℝ → ℝ) (gamma t : ℝ)
    (ht : 0 ≤ t)
    (hscale : ∀ x ∈ Ici (0 : ℝ), HasDerivAt sU (-cU x * sU x) x)
    (hscaleNonneg : ∀ x ∈ Ici (0 : ℝ), 0 ≤ sU x)
    (hrate : ∀ x ∈ Ici (0 : ℝ), cU x ≤ -gamma) :
    sU 0 * Real.exp (gamma * t) ≤ sU t := by
  let weightedScale := fun x : ℝ ↦ sU x * Real.exp (-gamma * x)
  have hweightedDeriv (x : ℝ) (hx : x ∈ Ici (0 : ℝ)) :
      HasDerivAt weightedScale
        ((-cU x * sU x) * Real.exp (-gamma * x) +
          sU x * ((-gamma) * Real.exp (-gamma * x))) x := by
    have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp (-gamma * y))
        ((-gamma) * Real.exp (-gamma * x)) x := by
      cas
    exact (hscale x hx).mul hexp
  have hcontinuous : ContinuousOn weightedScale (Ici (0 : ℝ)) :=
    fun x hx ↦ (hweightedDeriv x hx).continuousAt.continuousWithinAt
  have hdifferentiable : DifferentiableOn ℝ weightedScale (interior (Ici (0 : ℝ))) :=
    fun x hx ↦ (hweightedDeriv x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn weightedScale (Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ)) hcontinuous hdifferentiable
    intro x hx
    rw [(hweightedDeriv x (interior_subset hx)).deriv]
    have hrate' := hrate x (interior_subset hx)
    have hsU := hscaleNonneg x (interior_subset hx)
    have hcoefficient : 0 ≤ -cU x - gamma := by linarith
    calc
      0 ≤ (-cU x - gamma) * sU x * Real.exp (-gamma * x) :=
        mul_nonneg (mul_nonneg hcoefficient hsU) (Real.exp_pos _).le
      _ = (-cU x * sU x) * Real.exp (-gamma * x) +
          sU x * ((-gamma) * Real.exp (-gamma * x)) := by ring
  have hcomparison := hmono (by simp) ht ht
  dsimp [weightedScale] at hcomparison
  simp only [mul_zero, Real.exp_zero, mul_one] at hcomparison
  have hexpPos : 0 < Real.exp (gamma * t) := Real.exp_pos _
  have hexpCancel : Real.exp (-gamma * t) * Real.exp (gamma * t) = 1 := by
    cas
  calc
    sU 0 * Real.exp (gamma * t) ≤
        (sU t * Real.exp (-gamma * t)) * Real.exp (gamma * t) :=
      mul_le_mul_of_nonneg_right hcomparison hexpPos.le
    _ = sU t := by
      rw [mul_assoc, hexpCancel, mul_one]

/-- A positive amplitude with uniformly negative logarithmic rate grows without bound.
This conclusion uses the ODE only on the forward time half-line. -/
theorem amplitude_scale_tendsto_atTop
    (sU cU : ℝ → ℝ) (gamma : ℝ) (hsU0 : 0 < sU 0)
    (hscale : ∀ x ∈ Ici (0 : ℝ), HasDerivAt sU (-cU x * sU x) x)
    (hrate : ∀ x ∈ Ici (0 : ℝ), cU x ≤ -gamma) (hgamma : 0 < gamma) :
    Tendsto sU atTop atTop := by
  have hlower : Tendsto (fun t : ℝ ↦ sU 0 * Real.exp (gamma * t)) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hgamma)).const_mul_atTop hsU0
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact amplitude_scale_lower_bound sU cU gamma t ht hscale
    (fun x hx ↦ (amplitude_scale_pos sU cU gamma hsU0 hscale hrate hx).le) hrate

/-- If a vanishing scale is also the derivative of a clock, its logarithmic rate
fixes the scale relative to the remaining clock time. A rate limit suffices;
no integrability assumption on the rate error is needed. -/
theorem scale_div_remainingTime_tendsto
    {scale clock rate : ℝ → ℝ} {lifetime c : ℝ}
    (hscale : ∀ᶠ t in atTop, HasDerivAt scale (rate t * scale t) t)
    (hclock : ∀ᶠ t in atTop, HasDerivAt clock (scale t) t)
    (hne : ∀ᶠ t in atTop, scale t ≠ 0)
    (hzero : Tendsto scale atTop (𝓝 0))
    (htime : Tendsto clock atTop (𝓝 lifetime))
    (hrate : Tendsto rate atTop (𝓝 c)) :
    Tendsto (fun t ↦ scale t / (lifetime - clock t)) atTop (𝓝 (-c)) := by
  have hremaining : Tendsto (fun t ↦ lifetime - clock t) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := lifetime)).sub htime
  have hderiv : ∀ᶠ t in atTop,
      HasDerivAt (fun s ↦ lifetime - clock s) (-scale t) t :=
    hclock.mono fun _ ht ↦ ht.const_sub lifetime
  have hderiv_ne : ∀ᶠ t in atTop, -scale t ≠ 0 :=
    hne.mono fun _ ht ↦ neg_ne_zero.mpr ht
  have hquot : Tendsto (fun t ↦ rate t * scale t / -scale t) atTop (𝓝 (-c)) := by
    apply hrate.neg.congr'
    filter_upwards [hne] with t ht
    simp only [div_neg, mul_div_cancel_right₀ _ ht]
  exact HasDerivAt.lhopital_zero_atTop hscale hderiv hderiv_ne hzero hremaining hquot

/-- An integrable nonnegative clock rate bounded by `A exp (-gamma s)` on `(t, ∞)` has
tail `∫ₜ^∞` at most `A exp (-gamma t) / gamma` when `gamma > 0`.
-/
theorem physical_clock_tail_le
    (reciprocalScale : ℝ → ℝ) (amplitude gamma t : ℝ)
    (hgamma : 0 < gamma)
    (hintegrable : IntegrableOn reciprocalScale (Ioi t))
    (hbound : ∀ s ∈ Ioi t,
      0 ≤ reciprocalScale s ∧
        reciprocalScale s ≤ amplitude * Real.exp (-gamma * s)) :
    (∫ s in Ioi t, reciprocalScale s) ≤
      amplitude * Real.exp (-gamma * t) / gamma := by
  have hexpIntegrable :
      IntegrableOn (fun s : ℝ ↦ amplitude * Real.exp (-gamma * s))
        (Ioi t) := by
    exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hgamma) t).const_mul _
  calc
    (∫ s in Ioi t, reciprocalScale s) ≤
        ∫ s in Ioi t, amplitude * Real.exp (-gamma * s) :=
      setIntegral_mono_on hintegrable hexpIntegrable measurableSet_Ioi
        (fun s hs ↦ (hbound s hs).2)
    _ = amplitude * (∫ s in Ioi t, Real.exp (-gamma * s)) := by
      rw [integral_const_mul]
    _ = amplitude * Real.exp (-gamma * t) / gamma := by
      rw [show (fun s : ℝ ↦ Real.exp (-gamma * s)) =
          fun s : ℝ ↦ Real.exp ((-gamma) * s) by funext s; ring]
      rw [integral_exp_mul_Ioi (neg_lt_zero.mpr hgamma)]
      field_simp [hgamma.ne']

/-- A continuous positive integrable clock approaches its finite lifetime
from below: `∫₀ᵗ r → ∫₀^∞ r` as `t → ∞`, with values in `[0, ∫₀^∞ r)`. The limit is
`MeasureTheory.intervalIntegral_tendsto_integral_Ioi` and the range is
`image_physicalTimeIntegral_Ici`.
-/
theorem tendsto_physical_clock_atTop_nhdsWithin_Iio
    (reciprocalScale : ℝ → ℝ)
    (hcontinuous : Continuous reciprocalScale)
    (hpositive : ∀ t ∈ Ioi (0 : ℝ), 0 < reciprocalScale t)
    (hintegrable : IntegrableOn reciprocalScale (Ioi (0 : ℝ))) :
    Filter.Tendsto
      (fun t ↦ ∫ s in (0 : ℝ)..t, reciprocalScale s)
      Filter.atTop
      (𝓝[<] (∫ s in Ioi (0 : ℝ), reciprocalScale s)) := by
  refine tendsto_nhdsWithin_iff.mpr
    ⟨intervalIntegral_tendsto_integral_Ioi 0 hintegrable Filter.tendsto_id, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  have hmem : (∫ s in (0 : ℝ)..t, reciprocalScale s) ∈
      Ico 0 (∫ s in Ioi (0 : ℝ), reciprocalScale s) := by
    rw [← PDE.Analysis.Evolution.ODE.image_physicalTimeIntegral_Ici reciprocalScale hcontinuous
      hpositive hintegrable]
    exact ⟨t, ht, rfl⟩
  exact hmem.2

end PDE.Analysis.Evolution.ODE
