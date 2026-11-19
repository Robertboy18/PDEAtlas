/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Autonomous.OrbitIsolation
public import PDE.Analysis.ODE.Interpolation.Support.Avoidance
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Tails.Axis

import CAS.ExactTactic

/-!
# Closed axis avoidance for the prescribed-clock seed

Half-line uniqueness identifies the seed's outer pieces with the prescribed axis
tails. An isolating middle-passage set therefore misses both full closed axis
segments. Compact support inside that set also gives a common radius for small
signed translations of the right segment.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

open PDE.Analysis

/-- The prescribed seed and an isolating middle-passage set determine disjointness
of both full closed axis segments. No limit of the seed is assumed: the incoming limit
comes from the incoming tail, and the outgoing range from the prescribed outgoing tail
after endpoint uniqueness.
The field and seed are fixed throughout the argument. -/
theorem disjoint_axis_segments_of_prescribed_clock_seed {δ A B e : ℝ} {b : ℝ → ℝ} {q : ℝ → ℝ^3}
    {J : Set ℝ} {U : Set ℝ^3} (hδ : 0 ≤ δ) (hA : 1 ≤ A ^ 2) (hAB : A ^ 2 < B ^ 2)
    (hb : ContDiff ℝ ∞ b) (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10))
    (hq : ∀ t, HasDerivAt q (concreteGatedFlux δ (clockFeedback A B) b (q t)) t)
    (hq0 : q 0 = !₂[0, 0, 1]) (hqright : q (2 * e) = !₂[1, 0, 0])
    (hU : IsOpen U) (hpre : q ⁻¹' U ⊆ J) (hJ : J ⊆ Ioo 0 e) :
    Disjoint ((fun s : ℝ ↦ (!₂[0, 0, s] : ℝ^3)) '' Icc 0 1) U ∧
      Disjoint ((fun s : ℝ ↦ (!₂[s, 0, 0] : ℝ^3)) '' Icc 0 1) U := by
  have hf : ContDiff ℝ 1 (concreteGatedFlux δ (clockFeedback A B) b) :=
    (contDiff_concreteGatedFlux δ (contDiff_clockFeedback A B) hb).of_le (by simp)
  obtain ⟨qin, qout, hin0, hout0, haxes, hin, hout, hinlim, _, houtlim, _, _, _⟩ :=
    exists_prescribed_clock_axis_tails (μ := 0) hδ hA hAB hbsupp (by cas)
  have hzeroVec : (!₂[0, 0, 0] : ℝ^3) = 0 := by
    ext i
    fin_cases i <;> rfl
  simp only [mul_zero] at hout0 haxes houtlim
  rw [hzeroVec] at houtlim
  have hqinD (t : ℝ) (ht : t ≤ 0) :
      HasDerivAt qin (concreteGatedFlux δ (clockFeedback A B) b (qin t)) t := by
    simpa only [zero_smul, sub_zero] using (hin t ht).2
  have hqoutD (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt qout (concreteGatedFlux δ (clockFeedback A B) b (qout t)) t := by
    simpa only [zero_smul, sub_zero] using (hout t ht).2
  have hqin_eq : EqOn q qin (Iic 0) := ODE.eqOn_Iic_of_hasDerivAt_of_eq hf (fun t _ ↦ hq t) hqinD
      (hq0.trans hin0.symm)
  -- The seed orbit inherits the limit at `-∞` of the incoming tail, and its first coordinate
  -- vanishes for nonpositive times, so `q (2 e) = (1, 0, 0)` forces `0 < e`.
  have hlim : Tendsto q atBot (𝓝 0) :=
    hinlim.congr' ((eventually_le_atBot (0 : ℝ)).mono fun t ht ↦ (hqin_eq ht).symm)
  have he : 0 < e := by
    by_contra hle
    have h2e : 2 * e ∈ Iic (0 : ℝ) := by
      simp only [mem_Iic]
      linarith [not_lt.mp hle]
    have h := congrArg (fun x : ℝ^3 ↦ x 0)
      ((hqright.symm.trans (hqin_eq h2e)).trans (haxes (2 * e)).1)
    simp at h
  have hqshift (t : ℝ) : HasDerivAt (fun s ↦ q (s + 2 * e))
      (concreteGatedFlux δ (clockFeedback A B) b (q (t + 2 * e))) t :=
    HasDerivAt.comp_add_const t (2 * e) (hq (t + 2 * e))
  have hqout_eq : EqOn (fun t ↦ q (t + 2 * e)) qout (Ici 0) :=
    ODE.eqOn_Ici_of_hasDerivAt_of_eq hf (fun t _ ↦ hqshift t) hqoutD
      (by simpa only [zero_add] using hqright.trans hout0.symm)
  have hproj2 : Continuous (fun x : ℝ^3 ↦ x 2) :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 ↦ ℝ) 2
  have hproj0 : Continuous (fun x : ℝ^3 ↦ x 0) :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 ↦ ℝ) 0
  have hzin0 : qin 0 2 = 1 := by rw [hin0]; rfl
  have hzout0 : qout 0 0 = 1 := by rw [hout0]; rfl
  have hzinlim : Tendsto (fun t ↦ qin t 2) atBot (𝓝 0) := by
    simpa only [Function.comp_def, PiLp.zero_apply] using (hproj2.tendsto (0 : ℝ^3)).comp hinlim
  have hzoutlim : Tendsto (fun t ↦ qout t 0) atTop (𝓝 0) := by
    simpa only [Function.comp_def, PiLp.zero_apply] using (hproj0.tendsto (0 : ℝ^3)).comp houtlim
  have hinrange : (fun t ↦ qin t 2) '' Iic 0 = Ioc 0 1 := image_Iic_eq_Ioc_of_tendsto_atBot
      (hproj2.comp_continuousOn (HasDerivAt.continuousOn hqinD))
      (fun t ht ↦ (hin t ht).1) hzin0 hzinlim
  have houtrange : (fun t ↦ qout t 0) '' Ici 0 = Ioc 0 1 := image_Ici_eq_Ioc_of_tendsto_atTop
      (hproj0.comp_continuousOn (HasDerivAt.continuousOn hqoutD))
      (fun t ht ↦ (hout t ht).1) hzout0 hzoutlim
  exact disjoint_closed_axis_images_of_isolated_orbit
    (q := q) (zin := fun t ↦ qin t 2) (zout := fun t ↦ qout t 0)
    he.le hU hpre hJ hlim hzeroVec hzeroVec hinrange houtrange
    (fun t ht ↦ (hqin_eq ht).trans (haxes t).1) (fun t ht ↦ (hqout_eq ht).trans (haxes t).2)

/-- A fixed compact subset of the isolating set misses all sufficiently small
signed translations of the full closed right axis segment. Compactness is used for the forbidden
support. -/
theorem exists_pos_translated_right_axis_disjoint {U C : Set ℝ^3} (hC : IsCompact C) (hCU : C ⊆ U)
    (haxis : Disjoint ((fun s : ℝ ↦ (!₂[s, 0, 0] : ℝ^3)) '' Icc 0 1) U) :
    ∃ ε > 0, ∀ μ : ℝ, |μ| ≤ ε →
      Disjoint ((fun s : ℝ ↦ (!₂[s, 2000000 * μ, 0] : ℝ^3)) '' Icc 0 1) C := by
  have hF : Continuous (fun p : ℝ × ℝ ↦ (!₂[p.1, 2000000 * p.2, 0] : ℝ^3)) := by
    refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 ↦ ℝ)).comp (continuous_pi ?_)
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_const.mul continuous_snd
    · exact continuous_const
  obtain ⟨T, ε, _, hT, hε, havoid⟩ := exists_uniform_avoidance_of_compact_zero_section
    (K := Icc (0 : ℝ) 1) (C := C) (B := fun p : ℝ × ℝ ↦ (!₂[p.1, 2000000 * p.2, 0] : ℝ^3))
    hF isCompact_Icc hC.isClosed (by
      intro s hs
      simp only [mul_zero]
      exact fun hsC ↦ Set.disjoint_left.mp haxis ⟨s, hs, rfl⟩ (hCU hsC))
  refine ⟨ε, hε, fun μ hμ ↦ ?_⟩
  apply Set.disjoint_left.mpr
  rintro _ ⟨s, hs, rfl⟩ hsC
  exact havoid s (hT hs) μ hμ hsC

/-- A compactly supported correction inside the isolating set vanishes on every
small translated right segment, including both endpoints. The same correction is
fixed before choosing the common speed radius. -/
theorem exists_pos_translated_right_axis_notMem_tsupport
    {U : Set ℝ^3} {P : ℝ^3 → ℝ^3} (hP : HasCompactSupport P) (hPU : tsupport P ⊆ U)
    (haxis : Disjoint ((fun s : ℝ ↦ (!₂[s, 0, 0] : ℝ^3)) '' Icc 0 1) U) :
    ∃ ε > 0, ∀ μ : ℝ, |μ| ≤ ε → ∀ s ∈ Icc (0 : ℝ) 1,
      (!₂[s, 2000000 * μ, 0] : ℝ^3) ∉ tsupport P ∧ P !₂[s, 2000000 * μ, 0] = 0 := by
  obtain ⟨ε, hε, havoid⟩ := exists_pos_translated_right_axis_disjoint hP hPU haxis
  refine ⟨ε, hε, fun μ hμ s hs ↦ ?_⟩
  have hnot : (!₂[s, 2000000 * μ, 0] : ℝ^3) ∉ tsupport P :=
    Set.disjoint_left.mp (havoid μ hμ) ⟨s, hs, rfl⟩
  exact ⟨hnot, image_eq_zero_of_notMem_tsupport hnot⟩

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
