/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Reflection

import PDE.Analysis.Evolution.ODE.Autonomous.Uniqueness
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.Regularity
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Tails.Connection
import CAS.ExactTactic

/-!
# Isolated arcs of the same zero-speed clock connection

The terminal ratio-one conclusion gives a self-match at zero physical speed for
one fixed flux. Its matched-connection theorem supplies a complete
orbit. Autonomous uniqueness retains the entire supplied finite branch and
rules out repeated finite states; the equilibrium limits then isolate every
interior point from the remaining orbit outside any prescribed open time arc.

The signed gate is unchanged. The construction precedes the integrated bump.
-/

@[expose] public noncomputable section

open Filter Metric Set
open scoped ContDiff Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

/-- A repeated state would give a positive period, contradicting the equilibrium
limit of a nonconstant orbit. Reaching the equilibrium also contradicts uniqueness. -/
private theorem injective_and_ne_zero_of_limit {f : ℝ^3 → ℝ^3} {q : ℝ → ℝ^3}
    (hLip : ∀ R : ℝ, 0 < R → ∃ K : NNReal, LipschitzOnWith K f (closedBall 0 R)) (hfzero : f 0 = 0)
    (hq : ∀ t, HasDerivAt q (f (q t)) t) (hqzero : q 0 ≠ 0) (hlim : Tendsto q atTop (𝓝 0)) :
    Function.Injective q ∧ ∀ t, q t ≠ 0 := by
  have hperiod : ∀ d : ℝ, 0 < d → ¬Function.Periodic q d := by
    intro d hd hp
    have hn : Tendsto (fun n : ℕ ↦ (n : ℝ) * d) atTop atTop :=
      Filter.Tendsto.atTop_mul_const hd tendsto_natCast_atTop_atTop
    have hc : Tendsto (fun _ : ℕ ↦ q 0) atTop (𝓝 0) := by
      simpa only [Function.comp_def, hp.nat_mul_eq] using hlim.comp hn
    exact hqzero (tendsto_nhds_unique tendsto_const_nhds hc)
  have hordered : ∀ s t : ℝ, s < t → q s ≠ q t := by
    intro s t hst hstq
    have hshift : (fun u ↦ q (u + (t - s))) = q := by
      apply PDE.Analysis.Evolution.eq_of_hasDerivAt_of_lipschitzOn_balls hLip (t₀ := s)
        (fun u ↦ HasDerivAt.comp_add_const u (t - s) (hq (u + (t - s)))) hq
      change q (s + (t - s)) = q s
      rw [add_sub_cancel, hstq]
    exact hperiod (t - s) (sub_pos.mpr hst) (fun u ↦ congrFun hshift u)
  refine ⟨fun s t hstq ↦ ?_, fun t ht ↦ hqzero (congrFun
    (PDE.Analysis.Evolution.eq_of_hasDerivAt_of_lipschitzOn_balls (g := fun _ ↦ (0 : ℝ^3)) hLip
      hq (fun u ↦ by simpa only [hfzero] using hasDerivAt_const u (0 : ℝ^3)) ht) 0)⟩
  rcases lt_trichotomy s t with hst | hst | hts
  exacts [(hordered s t hst hstq).elim, hst, (hordered t s hts hstq.symm).elim]

/-- The tails lie in a closed ball missing the chosen point. The remaining times
outside the open arc form a compact set, whose image also misses that point. -/
private theorem exists_open_isolating_neighborhood {q : ℝ → ℝ^3} {tStar : ℝ} {J : Set ℝ}
    (hq : Continuous q) (hinj : Function.Injective q) (hneq : q tStar ≠ 0)
    (hbot : Tendsto q atBot (𝓝 0)) (htop : Tendsto q atTop (𝓝 0)) (hJ : IsOpen J)
    (htJ : tStar ∈ J) :
    ∃ U : Set (ℝ^3), IsOpen U ∧ q tStar ∈ U ∧ ∀ t, q t ∈ U → t ∈ J := by
  obtain ⟨r, hr, hrq⟩ := exists_between (dist_pos.mpr hneq)
  have hball : ball (0 : ℝ^3) r ∈ 𝓝 (0 : ℝ^3) := isOpen_ball.mem_nhds (mem_ball_self hr)
  obtain ⟨a, ha⟩ := eventually_atBot.mp (hbot hball)
  obtain ⟨b, hb⟩ := eventually_atTop.mp (htop hball)
  let C : Set (ℝ^3) := q '' (Icc a b \ J)
  have hC : IsCompact C := (isCompact_Icc.diff hJ).image hq
  let U : Set (ℝ^3) := (closedBall 0 r ∪ C)ᶜ
  have hU : IsOpen U := (isClosed_closedBall.union hC.isClosed).isOpen_compl
  have hmem : q tStar ∈ U := by
    rintro (hsmall | ⟨s, hs, heq⟩)
    · exact (not_le.mpr hrq) (mem_closedBall.mp hsmall)
    · exact hs.2 (hinj heq ▸ htJ)
  refine ⟨U, hU, hmem, fun t htU ↦ ?_⟩
  have havoid : q t ∉ closedBall 0 r ∪ C := htU
  have hnotball : q t ∉ closedBall 0 r := fun ht ↦ havoid (Or.inl ht)
  have hat : a < t := lt_of_not_ge fun ht ↦ hnotball (ball_subset_closedBall (ha t ht))
  have htb : t < b := lt_of_not_ge fun ht ↦ hnotball (ball_subset_closedBall (hb t ht))
  by_contra htJ
  exact havoid (Or.inr ⟨t, ⟨⟨hat.le, htb.le⟩, htJ⟩, rfl⟩)

/-- A supplied zero-speed branch with terminal ratio one has an isolated interior
arc on its complete connection. Agreement retains the same closed `[0,H]`;
the ambient neighborhood misses the entire connection outside `J ∩ (0,e)`,
including the opposite finite branch and both equilibrium tails.

For the selected clock, use its fixed positive `δ`, its fixed signed gate, its
flow slice as `γ`, and its terminal time as `e`. The terminal value
hypotheses are conclusions of that selection, with no new matching or rank choice. -/
theorem exists_isolated_arc_of_prescribed_clock_zero_speed_match {δ A B e H tStar : ℝ} {b : ℝ → ℝ}
    {γ : ℝ → ℝ^3} (hδ : 0 ≤ δ) (hA : 1 ≤ A ^ 2) (hAB : A ^ 2 < B ^ 2)
    (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10)) (hb : ContDiff ℝ ∞ b) (heH : e < H)
    (htStar : tStar ∈ Ioo (0 : ℝ) e)
    (hγ : ∀ t ∈ Icc (0 : ℝ) H, HasDerivAt γ (concreteGatedFlux δ (clockFeedback A B) b (γ t)) t)
    (hγzero : γ 0 = !₂[0, 0, 1]) (hmiddle : γ e 1 = 0) (hz : 0 < γ e 2) (hρ : γ e 0 / γ e 2 = 1)
    {J : Set ℝ} (hJ : IsOpen J) (htJ : tStar ∈ J) :
    let f := concreteGatedFlux δ (clockFeedback A B) b
    ∃ (q : ℝ → ℝ^3) (U : Set (ℝ^3)) (l u : ℝ),
      IsViscousProfile f 0 0 0 q ∧ ContDiff ℝ ∞ q ∧
      (∀ t, HasDerivAt q (f (q t)) t) ∧
      EqOn q γ (Icc (0 : ℝ) H) ∧
      EqOn q (fun t ↦ GatedFlux.reversal (γ (e + e - t))) (Icc e (e + e)) ∧
      Function.Injective q ∧ (∀ t, q t ≠ 0) ∧
      IsOpen U ∧ γ tStar ∈ U ∧
      0 < l ∧ l < tStar ∧ tStar < u ∧ u < e ∧
      Icc l u ⊆ J ∧ MapsTo γ (Icc l u) U ∧
      (∀ t, q t ∈ U → t ∈ J ∩ Ioo (0 : ℝ) e) ∧
      (∀ t ∈ Icc (0 : ℝ) H, γ t ∈ U → t ∈ J ∩ Ioo (0 : ℝ) e) ∧
      (∀ t ∈ Icc (0 : ℝ) e, GatedFlux.reversal (γ t) ∉ U) := by
  classical
  intro f
  have he : 0 < e := htStar.1.trans htStar.2
  have hmatch : γ e 0 = γ e 2 := by
    simpa only [one_mul] using (div_eq_iff hz.ne').mp hρ
  have hbranch : ∀ t ∈ Icc (0 : ℝ) e, HasDerivAt γ (f (γ t)) t :=
    fun t ht ↦ hγ t ⟨ht.1, ht.2.trans heH.le⟩
  obtain ⟨q, hprofile, hfinite, hreflected⟩ :=
    exists_prescribed_clock_viscous_profile_of_terminal_match
      (μ := 0) (Tplus := e) (Tminus := e) (u := γ) (v := γ)
      hδ hA hAB hbsupp hb (by norm_num) he he
      (by simpa only [zero_smul, sub_zero] using hbranch)
      (by simpa only [neg_zero, zero_smul, sub_zero] using hbranch)
      hγzero (by simpa only [mul_zero, neg_zero] using hγzero) hmiddle hmiddle hmatch hmatch.symm
  have hprofile0 : IsViscousProfile f 0 0 0 q := by
    have hzero : (!₂[0, 0, 0] : ℝ^3) = 0 := by
      ext i
      fin_cases i <;> rfl
    simpa [f, hzero] using hprofile
  have hf : ContDiff ℝ ∞ f := contDiff_concreteGatedFlux δ (contDiff_clockFeedback A B) hb
  have hfDiff : Differentiable ℝ f := hf.differentiable (by simp)
  have hfiniteStar : q tStar = γ tStar := hfinite ⟨htStar.1.le, htStar.2.le⟩
  have hlocal : q =ᶠ[𝓝 tStar] γ :=
    Filter.eventually_of_mem (Icc_mem_nhds htStar.1 htStar.2) fun _ ht ↦ hfinite ht
  have hqStar : HasDerivAt q (f (q tStar)) tStar := hfiniteStar ▸
    (hbranch tStar ⟨htStar.1.le, htStar.2.le⟩).congr_of_eventuallyEq hlocal
  have hfzero : f 0 = 0 := by
    have hfirst := hprofile0.first_integral hfDiff tStar
    rw [hqStar.deriv, zero_smul, sub_zero] at hfirst
    exact sub_eq_self.mp hfirst.symm
  have hqODE (t : ℝ) : HasDerivAt q (f (q t)) t := by
    have hd : deriv q t = f (q t) := by
      simpa only [hfzero, zero_smul, sub_zero] using hprofile0.first_integral hfDiff t
    exact hd ▸ (hprofile0.contDiff.differentiable (by simp) t).hasDerivAt
  have hqSmooth : ContDiff ℝ ∞ q := hprofile0.contDiff_infty hf
  have hLip : ∀ R : ℝ, 0 < R → ∃ K : NNReal, LipschitzOnWith K f (closedBall 0 R) :=
    fun R _ ↦ hf.contDiffOn.exists_lipschitzOnWith (by simp) (convex_closedBall (0 : ℝ^3) R)
      (isCompact_closedBall _ _)
  have hqzero : q 0 = (!₂[0, 0, 1] : ℝ^3) := (hfinite ⟨le_rfl, he.le⟩).trans hγzero
  have hqne : q 0 ≠ 0 := fun h ↦ by simpa [hqzero] using congrArg (fun x : ℝ^3 ↦ x 2) h
  obtain ⟨hinj, hnonzero⟩ := injective_and_ne_zero_of_limit hLip hfzero hqODE hqne
    hprofile0.tendsto_atTop
  have hagree : EqOn q γ (Icc (0 : ℝ) H) :=
    PDE.Analysis.Evolution.eqOn_Icc_of_hasDerivAt_of_lipschitzOn_balls hLip
      (t₀ := tStar) ⟨htStar.1, htStar.2.trans heH⟩
      hqSmooth.continuous.continuousOn (fun t _ ↦ hqODE t)
      (fun t ht ↦ (hγ t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ hγ t ⟨ht.1.le, ht.2.le⟩) hfiniteStar
  let J₀ := J ∩ Ioo (0 : ℝ) e
  have hJ₀ : IsOpen J₀ := hJ.inter isOpen_Ioo
  have htJ₀ : tStar ∈ J₀ := ⟨htJ, htStar⟩
  obtain ⟨U, hU, htU, hisolate⟩ := exists_open_isolating_neighborhood
    hqSmooth.continuous hinj (hnonzero tStar) hprofile0.tendsto_atBot
    hprofile0.tendsto_atTop hJ₀ htJ₀
  obtain ⟨a, d, htad, had⟩ := Filter.Eventually.exists_Ioo_subset
    (((hU.preimage hqSmooth.continuous).inter hJ₀).mem_nhds ⟨htU, htJ₀⟩)
  obtain ⟨l, hal, hlt⟩ := exists_between htad.1
  obtain ⟨u, htu, hud⟩ := exists_between htad.2
  have hinner : Icc l u ⊆ (q ⁻¹' U) ∩ J₀ := fun t ht ↦ had ⟨hal.trans_le ht.1, ht.2.trans_lt hud⟩
  have hlu : l ≤ u := (hlt.trans htu).le
  have hlzero : 0 < l := (hinner ⟨le_rfl, hlu⟩).2.2.1
  have hue : u < e := (hinner ⟨hlu, le_rfl⟩).2.2.2
  refine ⟨q, U, l, u, hprofile0, hqSmooth, hqODE, hagree, hreflected,
    hinj, hnonzero, hU, hfiniteStar ▸ htU, hlzero, hlt, htu, hue, fun t ht ↦ (hinner ht).2.1,
    fun t ht ↦ hagree ⟨hlzero.le.trans ht.1, ht.2.trans (hue.le.trans heH.le)⟩ ▸ (hinner ht).1,
    hisolate, fun t ht hγU ↦ hisolate t (by rw [hagree ht]; exact hγU), fun t ht hrevU ↦ ?_⟩
  have hs : e + e - t ∈ Icc e (e + e) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hqrev : q (e + e - t) = GatedFlux.reversal (γ t) := by
    simpa only [sub_sub_cancel] using (hreflected hs : q (e + e - t) = _)
  exact (not_lt.mpr hs.1) (hisolate _ (by rw [hqrev]; exact hrevU)).2.2

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
