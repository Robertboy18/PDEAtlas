/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Concrete
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback

import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Reflection
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Tails.Fast
import CAS.ExactTactic

/-!
# Axis tails at the prescribed sections

The scalar tail through one lifts to the incoming axis of the fixed concrete
flux. The outgoing tail is the time reversal and coordinate reflection of the
shifted incoming axis at the opposite speed. Its shifted axis equation is proved
before reflection. Both cutoff terms remain in the flux throughout.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

open Filter Set PDE.Analysis
open scoped Topology

/-- Fixed thresholds and a signed gate away from the central interval admit
axis tails at both section-one endpoints for small signed speeds. Their equations
use ordinary derivatives on closed half-lines. The scalar parameter need only be
nonnegative; in particular this applies to every fixed `0 < δ < 1/4` physical flux. -/
theorem exists_prescribed_clock_axis_tails {δ A B μ : ℝ} {b : ℝ → ℝ} (hδ : 0 ≤ δ) (hA : 1 ≤ A ^ 2)
    (hAB : A ^ 2 < B ^ 2) (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10)) (hμ : |μ| < 1 / 20000) :
    let f : ℝ^3 → ℝ^3 := concreteGatedFlux δ (clockFeedback A B) b
    ∃ qin qout : ℝ → ℝ^3,
      qin 0 = !₂[0, 0, 1] ∧ qout 0 = !₂[1, 2000000 * μ, 0] ∧
      (∀ t, qin t = !₂[0, 0, qin t 2] ∧
        qout t = !₂[qout t 0, 2000000 * μ, 0]) ∧
      (∀ t ≤ 0, qin t 2 ∈ Ioc 0 1 ∧
        HasDerivAt qin (f (qin t) - μ • qin t) t) ∧
      (∀ t ≥ 0, qout t 0 ∈ Ioc 0 1 ∧
        HasDerivAt qout (f (qout t) - μ • qout t) t) ∧
      Tendsto qin atBot (𝓝 0) ∧ Tendsto (deriv qin) atBot (𝓝 0) ∧
      Tendsto qout atTop (𝓝 !₂[0, 2000000 * μ, 0]) ∧
      Tendsto (deriv qout) atTop (𝓝 0) ∧
      f 0 = 0 ∧
      f !₂[0, 2000000 * μ, 0] - μ • !₂[0, 2000000 * μ, 0] = 0 := by
  intro f
  let a : ℝ := 2000000 * μ
  obtain ⟨hμlo, hμhi⟩ := abs_lt.mp hμ
  have ha : |a| ≤ 100 :=
    abs_le.mpr ⟨show -100 ≤ 2000000 * μ by linarith, show 2000000 * μ ≤ 100 by linarith⟩
  have hbzero {c : ℝ} (hc : |c| ≤ 100) : b c = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
    absurd ((hbsupp h).1.trans (abs_le.mp hc).2) (by norm_num)
  have hkzero : fastLogCosh δ 0 = 0 := by simp [fastLogCosh]
  have hφzero : clockFeedback A B 0 = 0 :=
    clockFeedback_eq_zero_of_abs_le_one hA hAB (by cas)
  have hgzero : MiddleClock.g 0 = 0 := by rw [MiddleClock.g_of_abs_le (by norm_num)]; norm_num
  have hga : MiddleClock.g a = μ * a := by rw [MiddleClock.g_of_abs_le ha]; simp only [a]; ring
  have hgaNeg : MiddleClock.g (-a) = (-μ) * (-a) := by rw [MiddleClock.g_neg, hga]; ring
  -- Both cutoff products vanish through their feedback factors on this band.
  have haxis (ν c s : ℝ) (hc : |c| ≤ 100) (hgc : MiddleClock.g c = ν * c) (hs : |s| ≤ 1) :
      f !₂[0, c, s] - ν • !₂[0, c, s] =
        !₂[0, 0, fastLogCosh δ s - ν * s] := by
    have hφs := clockFeedback_eq_zero_of_abs_le_one hA hAB hs
    have hbc := hbzero hc
    ext i
    fin_cases i <;> simp [f, concreteGatedFlux, GatedFlux.flux, hkzero, hφzero, hφs, hbc, hgc]
  obtain ⟨z, hz0, hzC2, hz, hzlim, hzdlim⟩ :=
    exists_fastLogCosh_tail_at_one (δ := δ) (μ := μ) hδ (by cas)
  obtain ⟨v, hv0, hvC2, hv, hvlim, hvdlim⟩ :=
    exists_fastLogCosh_tail_at_one (δ := δ) (μ := -μ) hδ (by cas)
  let e : ℝ^3 := !₂[0, 0, 1]
  let qin : ℝ → ℝ^3 := fun t ↦ z t • e
  let r : ℝ → ℝ^3 := fun t ↦ !₂[0, -a, 0] + v t • e
  let qout : ℝ → ℝ^3 := fun t ↦ GatedFlux.reversal (r (-t))
  have hqin (t : ℝ) : qin t = !₂[0, 0, z t] := by
    ext i
    fin_cases i <;> simp [qin, e]
  have hr (t : ℝ) : r t = !₂[0, -a, v t] := by
    ext i
    fin_cases i <;> simp [r, e]
  have hqout (t : ℝ) : qout t = !₂[v (-t), a, 0] := by
    simp [qout, hr, GatedFlux.reversal_apply]
  have hzDiff : Differentiable ℝ z := hzC2.differentiable (by simp)
  have hvDiff : Differentiable ℝ v := hvC2.differentiable (by simp)
  have hqinD (t : ℝ) : HasDerivAt qin (deriv z t • e) t := (hzDiff t).hasDerivAt.smul_const e
  have hrD (t : ℝ) : HasDerivAt r (deriv v t • e) t :=
    ((hvDiff t).hasDerivAt.smul_const e).const_add !₂[0, -a, 0]
  have hqinODE (t : ℝ) (ht : t ≤ 0) :
      HasDerivAt qin (f (qin t) - μ • qin t) t := by
    have hsmall : |z t| ≤ 1 := abs_le.mpr ⟨by linarith [(hz t ht).1.1], (hz t ht).1.2⟩
    apply (hqinD t).congr_deriv
    rw [(hz t ht).2.deriv, hqin t,
      haxis μ 0 (z t) (by cas) (by simpa using hgzero) hsmall]
    ext i
    fin_cases i <;> simp [e]
  -- The shifted incoming curve solves the same flux at speed -μ before reversal.
  have hrODE (t : ℝ) (ht : t ≤ 0) :
      HasDerivAt r (f (r t) - (-μ) • r t) t := by
    have hsmall : |v t| ≤ 1 := abs_le.mpr ⟨by linarith [(hv t ht).1.1], (hv t ht).1.2⟩
    apply (hrD t).congr_deriv
    rw [(hv t ht).2.deriv, hr t,
      haxis (-μ) (-a) (v t) (by simpa only [abs_neg] using ha) hgaNeg hsmall]
    ext i
    fin_cases i <;> simp [e]
  have hqoutD (t : ℝ) :
      HasDerivAt qout (-GatedFlux.reversal (deriv r (-t))) t := by
    have htime : HasDerivAt (fun s ↦ r (-s)) (-deriv r (-t)) t := by
      simpa only [Function.comp_def, neg_smul, one_smul] using
        (hrD (-t)).differentiableAt.hasDerivAt.scomp t (hasDerivAt_id t).neg
    have hR : HasDerivAt qout (GatedFlux.reversal (-deriv r (-t))) t :=
      GatedFlux.reversal.hasFDerivAt.comp_hasDerivAt t htime
    simpa only [map_neg] using hR
  have hqoutODE (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt qout (f (qout t) - μ • qout t) t := by
    apply (hqoutD t).congr_deriv
    rw [(hrODE (-t) (neg_nonpos.mpr ht)).deriv]
    exact (GatedFlux.flux_sub_smul_reversal (fastLogCosh δ) MiddleClock.g
      cutoff (clockFeedback A B) b MiddleClock.g_neg μ (r (-t))).symm
  have hqinlim : Tendsto qin atBot (𝓝 0) := by
    simpa only [zero_smul] using hzlim.smul_const e
  have hrlim : Tendsto r atBot (𝓝 !₂[0, -a, 0]) := by
    simpa only [zero_smul, add_zero] using (hvlim.smul_const e).const_add (!₂[0, -a, 0] : ℝ^3)
  have hqoutlim : Tendsto qout atTop (𝓝 !₂[0, a, 0]) := by
    have h := (GatedFlux.reversal.continuous.tendsto (!₂[0, -a, 0] : ℝ^3)).comp
      (hrlim.comp tendsto_neg_atTop_atBot)
    simpa [qout, Function.comp_def, GatedFlux.reversal_apply] using h
  have hqindlim : Tendsto (deriv qin) atBot (𝓝 0) := by
    rw [funext fun t ↦ (hqinD t).deriv]
    simpa only [zero_smul] using hzdlim.smul_const e
  have hrdlim : Tendsto (deriv r) atBot (𝓝 0) := by
    rw [funext fun t ↦ (hrD t).deriv]
    simpa only [zero_smul] using hvdlim.smul_const e
  have hqoutdlim : Tendsto (deriv qout) atTop (𝓝 0) := by
    rw [funext fun t ↦ (hqoutD t).deriv]
    simpa only [Function.comp_def, map_zero, neg_zero] using
      ((GatedFlux.reversal.continuous.tendsto (0 : ℝ^3)).comp
        (hrdlim.comp tendsto_neg_atTop_atBot)).neg
  have hzeroVec : (!₂[0, 0, 0] : ℝ^3) = 0 := by
    ext i
    fin_cases i <;> rfl
  refine ⟨qin, qout, by simpa only [hz0] using hqin 0, by simpa only [neg_zero, hv0] using hqout 0,
    fun t ↦ by simp [hqin, hqout, a],
    fun t ht ↦ ⟨by simpa [hqin] using (hz t ht).1, hqinODE t ht⟩,
    fun t ht ↦ ⟨by simpa [hqout] using (hv (-t) (neg_nonpos.mpr ht)).1, hqoutODE t ht⟩,
    hqinlim, hqindlim, hqoutlim, hqoutdlim, ?_, ?_⟩
  · simpa [hkzero, hzeroVec] using haxis μ 0 0 (by norm_num) (by simpa using hgzero) (by norm_num)
  · simpa [hkzero, hzeroVec] using haxis μ a 0 ha hga (by norm_num)

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
