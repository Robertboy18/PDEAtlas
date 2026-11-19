/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.Congruence
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Concrete
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Feedback
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve

import CAS.ExactTactic
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Endpoint spectra for a corrected prescribed-clock flux

A correction supported away from the central axis leaves the prescribed endpoint
spectra unchanged. Their ordering excludes the Lax inequalities at small positive
speeds. The final theorem uses a supplied family of viscous profiles to
obtain arbitrarily small nonzero jumps.
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System

namespace ViscousProfile.ReverseProfile

private theorem add_correction_eventuallyEq {f P : ℝ^3 → ℝ^3} {x : ℝ^3} (hx : x ∉ tsupport P) :
    f + P =ᶠ[𝓝 x] f := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  change f y + P y = f y
  change P y = 0 at hy
  rw [hy, add_zero]

private theorem concreteGatedFlux_eventuallyEq_zero_gate {δ a : ℝ} {φ b : ℝ → ℝ}
    (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10)) (ha : |a| ≤ 100) :
    concreteGatedFlux δ φ b =ᶠ[𝓝 (!₂[0, a, 0] : ℝ^3)] concreteGatedFlux δ φ 0 := by
  have hbzero {s : ℝ} (hs : |s| ≤ 100) : s ∉ tsupport b := by
    intro hsupp
    have hlo := (hbsupp hsupp).1
    have hhi := (abs_le.mp hs).2
    linarith
  have hpos : b =ᶠ[𝓝 a] 0 := notMem_tsupport_iff_eventuallyEq.mp (hbzero ha)
  have hneg : b =ᶠ[𝓝 (-a)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (hbzero (by simpa only [abs_neg] using ha))
  have hcoord : ContinuousAt (fun x : ℝ^3 ↦ x 1) (!₂[0, a, 0] : ℝ^3) :=
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (2 : ENNReal) (!₂[0, a, 0] : ℝ^3) (1 : Fin 3)).continuousAt
  filter_upwards [hcoord.eventually hpos, hcoord.neg.eventually hneg] with x hx hnx
  change b (x 1) = 0 at hx
  change b (-x 1) = 0 at hnx
  ext i
  fin_cases i <;> simp [concreteGatedFlux, GatedFlux.flux, hx, hnx]

/-- On the central axis, the gated eigenbasis gives the complete ordered
spectrum after any correction supported away from the state. -/
theorem corrected_prescribed_clock_center_spectrum {δ A B a : ℝ} {b : ℝ → ℝ} {P : ℝ^3 → ℝ^3}
    (hA : 1 ≤ A ^ 2) (hAB : A ^ 2 < B ^ 2) (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10))
    (ha : |a| ≤ 100) (hP : (!₂[0, a, 0] : ℝ^3) ∉ tsupport P) :
    let seed := concreteGatedFlux δ (clockFeedback A B) b
    fderiv ℝ (seed + P) !₂[0, a, 0] = fderiv ℝ seed !₂[0, a, 0] ∧
      IsStrictlyHyperbolicAt (seed + P) !₂[0, a, 0] ∧
      (fun k ↦ characteristicSpeed (seed + P) k !₂[0, a, 0]) =
        ![-2, (1 / 1000000) * a, 2] := by
  let seed := concreteGatedFlux δ (clockFeedback A B) b
  let ungated := concreteGatedFlux δ (clockFeedback A B) 0
  have hφzero : clockFeedback A B 0 = 0 :=
    clockFeedback_eq_zero_of_abs_le_one hA hAB (by cas)
  have hk0 : deriv (fastLogCosh δ) 0 = 2 := by simp [deriv_fastLogCosh]
  have hmiddle : GatedFlux.middleSpeed MiddleClock.g cutoff
      (clockFeedback A B) !₂[0, a, 0] = (1 / 1000000) * a := by
    simp [GatedFlux.middleSpeed, hφzero, MiddleClock.deriv_g, MiddleClock.slope_of_abs_le ha]
  have hk := (contDiff_fastLogCosh δ).differentiable (by simp)
  have hg := MiddleClock.contDiff_g.differentiable (by simp)
  have hC := contDiff_cutoff.differentiable (by simp)
  have hφ := (contDiff_clockFeedback A B).differentiable (by simp)
  have hb0 : Differentiable ℝ (0 : ℝ → ℝ) :=
    (contDiff_const : ContDiff ℝ ∞ (0 : ℝ → ℝ)).differentiable (by simp)
  have hleft : ∀ s : ℝ, s ≤ 100 → cutoff s = 1 := fun _ hs ↦ cutoff_of_le hs
  have hright : ∀ s : ℝ, 205 ≤ s → cutoff s = 0 := fun _ hs ↦ cutoff_of_ge hs
  have hsupport : tsupport (0 : ℝ → ℝ) ⊆ Ioo (205 : ℝ) 206 := by simp
  have hlow : -deriv (fastLogCosh δ) ((!₂[0, a, 0] : ℝ^3) 0) <
      GatedFlux.middleSpeed MiddleClock.g cutoff (clockFeedback A B) !₂[0, a, 0] := by
    change -deriv (fastLogCosh δ) 0 < _
    rw [hk0, hmiddle]
    have hbound := (abs_le.mp ha).1
    linarith
  have hhigh : GatedFlux.middleSpeed MiddleClock.g cutoff (clockFeedback A B) !₂[0, a, 0] <
        deriv (fastLogCosh δ) ((!₂[0, a, 0] : ℝ^3) 2) := by
    change _ < deriv (fastLogCosh δ) 0
    rw [hk0, hmiddle]
    have hbound := (abs_le.mp ha).2
    linarith
  have hhyper : IsStrictlyHyperbolicAt ungated !₂[0, a, 0] :=
    GatedFlux.isStrictlyHyperbolicAt hk hg hC hφ hb0
      (by cas : (0 : ℝ) < 100) (by cas : (100 : ℝ) < 205) hleft hright hsupport hlow hhigh
  have hspectrum : (fun k ↦ characteristicSpeed ungated k !₂[0, a, 0]) =
      ![-2, (1 / 1000000) * a, 2] := by
    have h := GatedFlux.characteristicSpeed_eq hk hg hC hφ hb0
      (by cas : (0 : ℝ) < 100) (by cas : (100 : ℝ) < 205) hleft hright hsupport hlow hhigh
    simpa [ungated, concreteGatedFlux, GatedFlux.speed, hk0, hmiddle] using h
  have hseed : seed =ᶠ[𝓝 (!₂[0, a, 0] : ℝ^3)] ungated :=
    concreteGatedFlux_eventuallyEq_zero_gate hbsupp ha
  have hcorrection : seed + P =ᶠ[𝓝 (!₂[0, a, 0] : ℝ^3)] seed := add_correction_eventuallyEq hP
  exact ⟨hcorrection.fderiv_eq, hhyper.congr_of_eventuallyEq (hcorrection.trans hseed),
    (characteristicSpeed_eq_of_eventuallyEq hhyper (hcorrection.trans hseed)).trans hspectrum⟩

/-- Both endpoint Jacobians and canonical speed lists survive the fixed
correction. The speed bound is signed and closed, as in the tail assembly. -/
theorem fixed_correction_endpoint_spectra {δ A B μ : ℝ} {b : ℝ → ℝ} {P : ℝ^3 → ℝ^3} (hA : 1 ≤ A ^ 2)
    (hAB : A ^ 2 < B ^ 2) (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10)) (hμ : |μ| ≤ 1 / 20000)
    (hleft : (0 : ℝ^3) ∉ tsupport P) (hright : (!₂[0, 2000000 * μ, 0] : ℝ^3) ∉ tsupport P) :
    let seed := concreteGatedFlux δ (clockFeedback A B) b
    let f := seed + P
    fderiv ℝ f 0 = fderiv ℝ seed 0 ∧
      fderiv ℝ f !₂[0, 2000000 * μ, 0] =
        fderiv ℝ seed !₂[0, 2000000 * μ, 0] ∧
      IsStrictlyHyperbolicAt f 0 ∧
      IsStrictlyHyperbolicAt f !₂[0, 2000000 * μ, 0] ∧
      (fun k ↦ characteristicSpeed f k 0) = ![-2, 0, 2] ∧
      (fun k ↦ characteristicSpeed f k !₂[0, 2000000 * μ, 0]) = ![-2, 2 * μ, 2] := by
  have hzero : (!₂[0, 0, 0] : ℝ^3) = 0 := by
    ext i
    fin_cases i <;> rfl
  have hleft' := corrected_prescribed_clock_center_spectrum
    (δ := δ) hA hAB hbsupp (by cas : |(0 : ℝ)| ≤ 100)
    (show (!₂[0, 0, 0] : ℝ^3) ∉ tsupport P by simpa only [hzero] using hleft)
  have ha : |2000000 * μ| ≤ 100 := by
    rw [abs_mul, abs_of_pos (by cas : (0 : ℝ) < 2000000)]
    linarith
  have hright' := corrected_prescribed_clock_center_spectrum (δ := δ) hA hAB hbsupp ha hright
  have hscale : (1 / 1000000 : ℝ) * (2000000 * μ) = 2 * μ := by cas
  simpa only [hzero, mul_zero, hscale] using And.intro hleft'.1 (And.intro hright'.1
      (And.intro hleft'.2.1 (And.intro hright'.2.1 (And.intro hleft'.2.2 hright'.2.2))))

/-- None of the three canonical families compresses these endpoints at a
positive small speed. This uses the computed spectra. -/
theorem fixed_correction_not_lax_compression {δ A B μ : ℝ} {b : ℝ → ℝ} {P : ℝ^3 → ℝ^3}
    (hA : 1 ≤ A ^ 2) (hAB : A ^ 2 < B ^ 2) (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10))
    (hμ : 0 < μ) (hμsmall : μ < 1 / 20000) (hleft : (0 : ℝ^3) ∉ tsupport P)
    (hright : (!₂[0, 2000000 * μ, 0] : ℝ^3) ∉ tsupport P) :
    let f := concreteGatedFlux δ (clockFeedback A B) b + P; ∀ k : Fin 3,
      ¬(characteristicSpeed f k !₂[0, 2000000 * μ, 0] < μ ∧ μ < characteristicSpeed f k 0) := by
  have hμabs : |μ| ≤ 1 / 20000 := by
    simpa only [abs_of_pos hμ] using hμsmall.le
  obtain ⟨_, _, _, _, hL, hR⟩ :=
    fixed_correction_endpoint_spectra (δ := δ) hA hAB hbsupp hμabs hleft hright
  dsimp only
  intro k hcompression
  have hLk := congrFun hL k
  have hRk := congrFun hR k
  rw [hLk, hRk] at hcompression
  obtain ⟨hRlt, hLlt⟩ := hcompression
  fin_cases k <;> norm_num at hRlt hLlt <;> linarith

/-- The failure of canonical compression excludes the `LaxShock`
predicate for every characteristic-field choice with those canonical speeds. -/
theorem fixed_correction_not_laxShock {δ A B μ : ℝ} {b : ℝ → ℝ} {P : ℝ^3 → ℝ^3} (hA : 1 ≤ A ^ 2)
    (hAB : A ^ 2 < B ^ 2) (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10)) (hμ : 0 < μ)
    (hμsmall : μ < 1 / 20000) (hleft : (0 : ℝ^3) ∉ tsupport P)
    (hright : (!₂[0, 2000000 * μ, 0] : ℝ^3) ∉ tsupport P)
    (fields : Fin 3 → CharacteristicField (concreteGatedFlux δ (clockFeedback A B) b + P))
    (hspeeds : ∀ k, (fields k).speed =
      characteristicSpeed (concreteGatedFlux δ (clockFeedback A B) b + P) k)
    (k : Fin 3) :
    ¬LaxShock fields k 0 !₂[0, 2000000 * μ, 0] μ := by
  intro hshock
  apply fixed_correction_not_lax_compression (δ := δ) hA hAB hbsupp hμ hμsmall hleft hright k
  simpa only [hspeeds k] using And.intro hshock.2.1 hshock.2.2.1

/-- The size of the right endstate is exactly linear in the absolute speed. -/
theorem norm_prescribed_clock_right_state (μ : ℝ) :
    ‖(!₂[0, 2000000 * μ, 0] : ℝ^3)‖ = 2000000 * |μ| := by
  have hsingle : (!₂[0, 2000000 * μ, 0] : ℝ^3) = PiLp.single 2 (1 : Fin 3) (2000000 * μ) := by
    ext i
    fin_cases i <;> simp
  rw [hsingle, PiLp.norm_single, Real.norm_eq_abs, abs_mul]
  norm_num

/-- A positive speed can be chosen inside any prescribed positive radius while
keeping the nonzero right endstate arbitrarily close to zero. -/
theorem exists_small_prescribed_clock_right_state {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ r ∧ μ < 1 / 20000 ∧ (!₂[0, 2000000 * μ, 0] : ℝ^3) ≠ 0 ∧
      ‖(!₂[0, 2000000 * μ, 0] : ℝ^3)‖ < ε := by
  let μ := min r (min (1 / 40000) (ε / 4000000))
  have hμ : 0 < μ := lt_min hr (lt_min (by cas) (div_pos hε (by cas)))
  have hμr : μ ≤ r := min_le_left r (min (1 / 40000) (ε / 4000000))
  have hμcap : μ ≤ 1 / 40000 :=
    (min_le_right r (min (1 / 40000) (ε / 4000000))).trans (min_le_left _ _)
  have hμε : μ ≤ ε / 4000000 :=
    (min_le_right r (min (1 / 40000) (ε / 4000000))).trans (min_le_right _ _)
  have hnorm : ‖(!₂[0, 2000000 * μ, 0] : ℝ^3)‖ = 2000000 * μ := by
    rw [norm_prescribed_clock_right_state, abs_of_pos hμ]
  refine ⟨μ, hμ, hμr, by linarith, ?_, ?_⟩
  · apply norm_pos_iff.mp
    rw [hnorm]
    exact mul_pos (by cas) hμ
  · rw [hnorm]
    linarith

/-- Once profiles of the fixed corrected flux are supplied, there are
nonzero arbitrarily small jumps violating Lax in every canonical family.

The closed axis exclusions are consumed at amplitude zero. Smoothness follows
from addition; compact support, global hyperbolicity, and genuine nonlinearity
are retained from the same correction construction. No flux, correction, gate,
or threshold is reselected after the jump tolerance or speed is chosen. -/
theorem fixed_correction_arbitrarily_small_nonLax_profiles {δ A B r : ℝ} {b : ℝ → ℝ} {P : ℝ^3 → ℝ^3}
    (hA : 1 ≤ A ^ 2) (hAB : A ^ 2 < B ^ 2) (hb : ContDiff ℝ ∞ b)
    (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10)) (hP : ContDiff ℝ ∞ P)
    (hPc : HasCompactSupport P)
    (hhyper : IsStrictlyHyperbolicOn (concreteGatedFlux δ (clockFeedback A B) b + P) univ)
    (hgn : ∀ k, IsGenuinelyNonlinearFamily (concreteGatedFlux δ (clockFeedback A B) b + P) k)
    (hr : 0 < r) (hleft : ∀ s ∈ Icc (0 : ℝ) 1, (!₂[0, 0, s] : ℝ^3) ∉ tsupport P)
    (hright : ∀ μ : ℝ, |μ| ≤ r → ∀ s ∈ Icc (0 : ℝ) 1, (!₂[s, 2000000 * μ, 0] : ℝ^3) ∉ tsupport P)
    (hprofiles : ∀ μ : ℝ, 0 < μ → μ ≤ r → ∃ q : ℝ → ℝ^3, IsViscousProfile
      (concreteGatedFlux δ (clockFeedback A B) b + P) 0 !₂[0, 2000000 * μ, 0] μ q) :
    let f := concreteGatedFlux δ (clockFeedback A B) b + P
    ContDiff ℝ ∞ f ∧ HasCompactSupport P ∧
      IsStrictlyHyperbolicOn f univ ∧ (∀ k, IsGenuinelyNonlinearFamily f k) ∧
      ∀ ε : ℝ, 0 < ε → ∃ (μ : ℝ) (q : ℝ → ℝ^3),
        0 < μ ∧ μ ≤ r ∧ μ < 1 / 20000 ∧
        (!₂[0, 2000000 * μ, 0] : ℝ^3) ≠ 0 ∧
        ‖(!₂[0, 2000000 * μ, 0] : ℝ^3)‖ < ε ∧
        IsViscousProfile f 0 !₂[0, 2000000 * μ, 0] μ q ∧
        RankineHugoniot f 0 !₂[0, 2000000 * μ, 0] μ ∧
        ∀ k : Fin 3, ¬(characteristicSpeed f k !₂[0, 2000000 * μ, 0] < μ ∧
          μ < characteristicSpeed f k 0) := by
  have hf := (contDiff_concreteGatedFlux δ (contDiff_clockFeedback A B) hb).add hP
  refine ⟨hf, hPc, hhyper, hgn, fun ε hε ↦ ?_⟩
  obtain ⟨μ, hμ, hμr, hμsmall, hne, hnorm⟩ := exists_small_prescribed_clock_right_state hr hε
  obtain ⟨q, hq⟩ := hprofiles μ hμ hμr
  have hzero : (!₂[0, 0, 0] : ℝ^3) = 0 := by
    ext i
    fin_cases i <;> rfl
  have hPzero : (0 : ℝ^3) ∉ tsupport P := by
    simpa only [hzero] using hleft 0 ⟨le_rfl, zero_le_one⟩
  have hPright : (!₂[0, 2000000 * μ, 0] : ℝ^3) ∉ tsupport P :=
    hright μ (by simpa only [abs_of_pos hμ] using hμr) 0 ⟨le_rfl, zero_le_one⟩
  exact ⟨μ, q, hμ, hμr, hμsmall, hne, hnorm, hq, hq.rankineHugoniot (hf.differentiable (by simp)),
    fixed_correction_not_lax_compression (δ := δ) hA hAB hbsupp hμ hμsmall hPzero hPright⟩

end ViscousProfile.ReverseProfile

end PDE.Hyperbolic.ConservationLaw.System
