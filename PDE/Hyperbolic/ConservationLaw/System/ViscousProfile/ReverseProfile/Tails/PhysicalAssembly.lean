/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Tails.Attachment
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Tails.Support

import CAS.ExactTactic

/-!
# Full physical profiles for one fixed compact correction

Isolation of the seed orbit excludes both complete closed axis segments from the
permitted correction region. Once the compact correction is fixed, a small signed
translation of the right segment also avoids its support. The corrected flux
therefore agrees with the prescribed seed on both physical tail segments.

A family of matched cores for this same corrected flux then extends to
full viscous profiles at every sufficiently small positive speed. The core's time
endpoints may depend on the speed, and the full profile retains the whole closed
core. The cores are hypotheses.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

/-- Attach physical tails to a positive-speed core family for one fixed corrected
prescribed-clock flux. The seed orbit and its isolating set supply closed-axis
separation. The translation radius is chosen after `P` is fixed, then intersected
with the core radius and `1 / 40000`; the closed final speed interval stays strictly
inside the tail theorem's bound `1 / 20000`.

`core μ` is the core at speed `μ`, on `[lo μ, hi μ]`. Only its within
ODE and two section-one anchor values are required. The conclusion retains this core and uses the
same total correction at every speed. -/
theorem exists_viscousProfile_family_of_fixed_correction_and_core {δ A B e rCore : ℝ} {b : ℝ → ℝ}
    {q : ℝ → ℝ^3} {J : Set ℝ} {Ω : Set ℝ^3} {P : ℝ^3 → ℝ^3} {core : ℝ → ℝ → ℝ^3} {lo hi : ℝ → ℝ}
    (hδ : 0 ≤ δ) (hA : 1 ≤ A ^ 2) (hAB : A ^ 2 < B ^ 2) (hb : ContDiff ℝ ∞ b)
    (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10))
    (hq : ∀ t, HasDerivAt q (concreteGatedFlux δ (clockFeedback A B) b (q t)) t)
    (hq0 : q 0 = !₂[0, 0, 1]) (hqright : q (2 * e) = !₂[1, 0, 0])
    (hΩ : IsOpen Ω) (hpre : q ⁻¹' Ω ⊆ J) (hJ : J ⊆ Ioo 0 e) (hP : ContDiff ℝ ∞ P)
    (hPc : HasCompactSupport P) (hPΩ : tsupport P ⊆ Ω) (hrCore : 0 < rCore)
    (hcore : ∀ μ : ℝ, 0 < μ → μ ≤ rCore → lo μ < hi μ ∧ (∀ t ∈ Icc (lo μ) (hi μ),
      HasDerivWithinAt (core μ) ((concreteGatedFlux δ (clockFeedback A B) b + P) (core μ t) - μ •
      core μ t) (Icc (lo μ) (hi μ)) t) ∧ core μ (lo μ) = !₂[0, 0, 1] ∧ core μ (hi μ) =
      !₂[1, 2000000 * μ, 0]) :
    let seed : ℝ^3 → ℝ^3 := concreteGatedFlux δ (clockFeedback A B) b
    ∃ r : ℝ, 0 < r ∧ r ≤ rCore ∧ r ≤ 1 / 40000 ∧ r < 1 / 20000 ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        (!₂[0, 0, s] : ℝ^3) ∉ tsupport P ∧ P !₂[0, 0, s] = 0 ∧
        (seed + P) !₂[0, 0, s] = seed !₂[0, 0, s]) ∧
      (∀ μ : ℝ, |μ| ≤ r → ∀ s ∈ Icc (0 : ℝ) 1,
        (!₂[s, 2000000 * μ, 0] : ℝ^3) ∉ tsupport P ∧
        P !₂[s, 2000000 * μ, 0] = 0 ∧
        (seed + P) !₂[s, 2000000 * μ, 0] = seed !₂[s, 2000000 * μ, 0]) ∧
      ∀ μ : ℝ, 0 < μ → μ ≤ r → ∃ qμ : ℝ → ℝ^3,
        IsViscousProfile (seed + P) 0 !₂[0, 2000000 * μ, 0] μ qμ ∧
        EqOn qμ (core μ) (Icc (lo μ) (hi μ)) ∧
        (∀ t ≤ lo μ, qμ t = !₂[0, 0, qμ t 2] ∧ qμ t 2 ∈ Ioc (0 : ℝ) 1) ∧
        (∀ t ≥ hi μ,
          qμ t = !₂[qμ t 0, 2000000 * μ, 0] ∧ qμ t 0 ∈ Ioc (0 : ℝ) 1) := by
  intro seed
  -- The seed orbit separates both closed axis segments from the correction region.
  obtain ⟨hleftAxis, hrightAxis⟩ := disjoint_axis_segments_of_prescribed_clock_seed
      hδ hA hAB hb hbsupp hq hq0 hqright hΩ hpre hJ
  have hleft : ∀ s ∈ Icc (0 : ℝ) 1, (!₂[0, 0, s] : ℝ^3) ∉ tsupport P ∧ P !₂[0, 0, s] = 0 ∧
      (seed + P) !₂[0, 0, s] = seed !₂[0, 0, s] := by
    intro s hs
    have hnot : (!₂[0, 0, s] : ℝ^3) ∉ tsupport P :=
      fun hx ↦ Set.disjoint_left.mp hleftAxis ⟨s, hs, rfl⟩ (hPΩ hx)
    have hzero : P !₂[0, 0, s] = 0 := image_eq_zero_of_notMem_tsupport hnot
    exact ⟨hnot, hzero, by simp only [Pi.add_apply, hzero, add_zero]⟩
  -- Compactness is applied to this fixed total support, before varying the speed.
  obtain ⟨rAxis, hrAxis, htranslated⟩ :=
    exists_pos_translated_right_axis_notMem_tsupport hPc hPΩ hrightAxis
  let r : ℝ := min rAxis (min rCore (1 / 40000))
  have hr : 0 < r := lt_min hrAxis (lt_min hrCore (by cas))
  have hrAxisBound : r ≤ rAxis := min_le_left rAxis (min rCore (1 / 40000))
  have hrCoreBound : r ≤ rCore :=
    (min_le_right rAxis (min rCore (1 / 40000))).trans (min_le_left rCore (1 / 40000))
  have hrSmall : r ≤ 1 / 40000 :=
    (min_le_right rAxis (min rCore (1 / 40000))).trans (min_le_right rCore (1 / 40000))
  have hrTail : r < 1 / 20000 := hrSmall.trans_lt (by cas)
  have hright : ∀ μ : ℝ, |μ| ≤ r → ∀ s ∈ Icc (0 : ℝ) 1, (!₂[s, 2000000 * μ, 0] : ℝ^3) ∉ tsupport P ∧
      P !₂[s, 2000000 * μ, 0] = 0 ∧
      (seed + P) !₂[s, 2000000 * μ, 0] = seed !₂[s, 2000000 * μ, 0] := by
    intro μ hμ s hs
    obtain ⟨hnot, hzero⟩ := htranslated μ (hμ.trans hrAxisBound) s hs
    exact ⟨hnot, hzero, by simp only [Pi.add_apply, hzero, add_zero]⟩
  have hflux : ContDiff ℝ ∞ (seed + P) :=
    (contDiff_concreteGatedFlux δ (contDiff_clockFeedback A B) hb).add hP
  refine ⟨r, hr, hrCoreBound, hrSmall, hrTail, hleft, hright, fun μ hμ hμr ↦ ?_⟩
  obtain ⟨hlohi, hode, hleftAnchor, hrightAnchor⟩ := hcore μ hμ (hμr.trans hrCoreBound)
  have hμabs : |μ| ≤ r := by simpa only [abs_of_pos hμ] using hμr
  exact exists_viscousProfile_of_preserved_axis_tails
    hflux hδ hA hAB hbsupp ⟨hμ, hμr.trans_lt hrTail⟩ hlohi
    (fun s hs ↦ (hleft s hs).2.2) (fun s hs ↦ (hright μ hμabs s hs).2.2)
    hode hleftAnchor hrightAnchor

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
