/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Corrections.Cubic.OuterEnvelope
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Retained.RankData

/-!
# A finite phase core from the retained selected branches

The rank bundle keeps the branches on their intervals of definition and their common
extension.
Its two descriptions of the strip derivative determine the same linear map, so
it supplies the frame used to construct a compactly supported cubic correction.
The outer-envelope theorem then proves that this correction vanishes along the
outer pieces of the phase curves.

There are three time intervals in this assembly. The common retained interval
contains both original anchors. The phase interval carries the cubic mismatch
and the phase ODE. The smaller join interval lies inside the rank neighborhood.
We use each interval for the hypotheses it supports.

After the joins and transition have been fixed, each positive scale cap and
C² tolerance give one state correction for all sufficiently small signed speeds.
The finite core starts and ends at the original sections. Its derivative
is taken within its closed time interval, including the two endpoints.
-/

@[expose] public noncomputable section

open Filter Set PDE.Analysis
open scoped ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

open PDE.Hyperbolic.ConservationLaw.System
open PDE.Analysis.ODE
open PDE.Analysis.ODE.StripRank

/-- Turn the retained selected rank bundle into a finite core for one fixed
state correction `P₂` and a whole interval of signed speeds.

The original outgoing and incoming sections are the two endpoint values. The
core family is written `core μ t`, with speed first; the retained phase families
`U t μ` and `V t μ` keep time first. All its conclusions concern `|μ| ≤ r`.

The correction, its support, its vanishing jets on the join orbit, and its
hyperbolicity and genuine-nonlinearity bounds are shared by every such speed.
The outer zeros and the frame are derived from the rank bundle and the
localization construction. Attaching infinite physical tails is a separate step. -/
theorem exists_retained_selected_phase_core {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {σ : ℝ × (Fin 3 → ℝ)} {f : ℝ^3 → ℝ^3} {q : ℝ → ℝ^3} {Fout Fincoming : ℝ → ℝ → ℝ^3}
    {τout τin : ℝ → ℝ} {I₀ Jgate : Set ℝ} {Ω : Set (ℝ^3)} {H e tStar : ℝ}
    {rStar : Module.Basis (Fin 3) ℝ (ℝ^3)} {i : Fin 3} (hf : ContDiff ℝ ∞ f)
    (hhyper : ∀ x, IsStrictlyHyperbolicAt f x) (hgn : ∀ j, IsGenuinelyNonlinearFamily f j)
    (hq : Continuous q) (hqinj : Function.Injective q) (hΩ : IsOpen Ω) (hgate : q tStar ∈ Ω)
    (hJgate : Jgate ⊆ Ioo (0 : ℝ) e) (he : 0 < e)
    (hRank : RetainedSelectedRankStrip Ψ σ f q Fout Fincoming τout τin I₀ Jgate Ω H e tStar rStar i)
    (hτout : ContinuousAt τout 0) (hτin : ContinuousAt τin 0) (hτoutZero : τout 0 = e)
    (hτinZero : τin 0 = e) :
    ∃ (U V : ℝ → ℝ → ℝ^3) (aJoin bJoin : ℝ) (θ : ℝ → ℝ),
      ContDiff ℝ ∞ U.uncurry ∧ ContDiff ℝ ∞ V.uncurry ∧
      EqOn (fun t ↦ U t 0) q (Icc 0 (e + e)) ∧
      EqOn (fun t ↦ V t 0) q (Icc 0 (e + e)) ∧
      0 < aJoin ∧ aJoin < bJoin ∧ bJoin < e + e ∧
      ContDiff ℝ ∞ θ ∧
      (∀ t ≤ aJoin, θ =ᶠ[𝓝 t] (fun _ ↦ 0)) ∧
      (∀ t, bJoin ≤ t → θ =ᶠ[𝓝 t] (fun _ ↦ 1)) ∧
      ∀ εcap : ℝ, 0 < εcap → ∀ η : ℝ, 0 < η →
        ∃ (P₂ : ℝ^3 → ℝ^3) (ε r d : ℝ) (core : ℝ → ℝ → ℝ^3),
          ContDiff ℝ ∞ P₂ ∧ HasCompactSupport P₂ ∧ tsupport P₂ ⊆ Ω ∧
          (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P₂ x‖ < η) ∧
          (∀ t ∈ Icc aJoin bJoin, ∀ n ≤ 2,
            iteratedFDeriv ℝ n P₂ (q t) = 0) ∧
          (∀ x, IsStrictlyHyperbolicAt (f + P₂) x) ∧
          (∀ j, IsGenuinelyNonlinearFamily (f + P₂) j) ∧
          0 < ε ∧ ε < εcap ∧ 0 < r ∧ r ≤ ε ∧ 0 < d ∧
          ∀ μ : ℝ, |μ| ≤ r →
            μ ∈ I₀ ∧
            (∀ t ∈ Icc (-d) aJoin, P₂ (U t μ) = 0) ∧
            (∀ t ∈ Icc bJoin (e + e + d), P₂ (V t μ) = 0) ∧
            let loμ := -(τout μ - e)
            let hiμ := e + e - (τin μ - e)
            loμ < aJoin ∧ bJoin < hiμ ∧ loμ < hiμ ∧
            EqOn (core μ) (fun t ↦ U t μ) (Icc loμ aJoin) ∧
            EqOn (core μ) (fun t ↦ blendedStrip U V θ (t, μ)) (Icc aJoin bJoin) ∧
            EqOn (core μ) (fun t ↦ V t μ) (Icc bJoin hiμ) ∧
            core μ loμ = Fout 0 μ ∧ core μ hiμ = Fincoming (e + e) μ ∧
            ∀ t ∈ Icc loμ hiμ,
              HasDerivWithinAt (core μ) ((f + P₂) (core μ t) - μ • core μ t)
                (Icc loμ hiμ) t := by
  classical
  obtain ⟨Gout, Gin, U, V, C, a, b, _, J, O, l, u, _, _, hinit, hbaseOut, hbaseIn, _, _, _, _, _,
      hJ, h0J, hJI, _, _, _, _, hnativeOde, hU, hV, hC, hphase, hphaseOde, _, _, hcubic, _, _, _, _,
      hO, htlu, hcompact, hOdomain, hOgate, _, hframes⟩ := hRank
  let loCommon := min 0 (e + e - H)
  let hiCommon := max H (e + e)
  have hlo : loCommon ≤ 0 := min_le_left _ _
  have hhi : e + e ≤ hiCommon := le_max_right _ _
  -- At zero speed the phase shift vanishes on the whole retained interval.
  have hUzero : EqOn (fun t ↦ U t 0) q (Icc 0 (e + e)) := (phase_base_eqOn_retained_interval h0J
    hτoutZero (fun μ hμ t ↦ (hphase μ hμ t).1) hbaseOut).mono (Icc_subset_Icc hlo hhi)
  have hVzero : EqOn (fun t ↦ V t 0) q (Icc 0 (e + e)) := (phase_base_eqOn_retained_interval h0J
    hτinZero (fun μ hμ t ↦ (hphase μ hμ t).2) hbaseIn).mono (Icc_subset_Icc hlo hhi)
  -- The phase ODE and cubic mismatch are used only on the phase interval [a,b].
  -- The explicit differential and the linear equivalence are derivatives of
  -- the same augmented strip at the same point.
  obtain ⟨aJoin, bJoin, haJoin, habJoin, hbJoin, θ, hθ, hθleft, hθright, hrealize⟩ :=
    exists_actual_outer_envelopes_of_rank_frame
      (lo := a) (hi := b) (L := e + e) (W := prescribedClockFullVariation Ψ σ (1, 0))
      (ν := rStar i) (phaseSlope := deriv τout 0)
      hf hhyper hgn hU hV hC hJ h0J hcubic hphaseOde hq hqinj hUzero hVzero
      hO (hcompact ⟨htlu.1.le, htlu.2.le⟩) (fun _ ht ↦ (hOdomain ht).1.1)
      (fun t ht ↦ ⟨(hJgate (hOgate ht)).1, (hJgate (hOgate ht)).2.trans (lt_add_of_pos_right e he)⟩)
      hΩ hgate fun θ hθ ↦ by
        obtain ⟨hw, hwbase, _, _, hderivatives⟩ := hframes θ hθ
        refine ⟨hw, hwbase, fun t ht ↦ ?_⟩
        obtain ⟨hD, hdet, M, hM⟩ := hderivatives t ht
        exact ⟨hD, hdet, M, hM.unique hD⟩
  refine ⟨U, V, aJoin, bJoin, θ, hU, hV, hUzero, hVzero,
    haJoin, habJoin, hbJoin, hθ, hθleft, hθright, fun εcap hcap η hη ↦ ?_⟩
  obtain ⟨P₂, ε, r₀, d, hP₂, hPc, hPΩ, hsmall, hbaseJets, hhyperP, hgnP,
      hε, hεcap, hr₀, hr₀ε, hd, houterMiddle⟩ := hrealize εcap hcap η hη
  have ha : aJoin ∈ Ioo (0 : ℝ) hiCommon := ⟨haJoin, (habJoin.trans hbJoin).trans_le hhi⟩
  have hb : bJoin ∈ Ioo loCommon (e + e) := ⟨hlo.trans_lt (haJoin.trans habJoin), hbJoin⟩
  -- Shrinking the speed interval moves the anchors inside the fixed zero
  -- envelopes. The retained ODE is still used on the full common interval.
  obtain ⟨r, hr, hrr₀, hcores⟩ := exists_phase_core_of_fixed_outer_envelopes
      (f := f) (P := P₂) (F := Gout) (G := Gin) (lo := loCommon) (hi := hiCommon)
      habJoin hlo hhi ha hb hd hr₀ (hJ.mem_nhds h0J) hτout hτin hτoutZero hτinZero
      (fun μ hμ ↦ (hnativeOde μ hμ).1) (fun μ hμ ↦ (hnativeOde μ hμ).2)
      (fun μ hμ t ↦ (hphase μ hμ t).1) (fun μ hμ t ↦ (hphase μ hμ t).2)
      (hθleft aJoin le_rfl).self_of_nhds (hθright bJoin le_rfl).self_of_nhds
      (fun μ hμ ↦ ⟨(houterMiddle μ hμ).1, (houterMiddle μ hμ).2.1⟩)
      (fun μ hμ ↦ (houterMiddle μ hμ).2.2)
  -- Choice assembles the already constructed finite curves into a family.
  -- The arbitrary value outside the speed interval has no asserted properties.
  let core : ℝ → ℝ → ℝ^3 := fun μ ↦ if hμ : |μ| ≤ r then Classical.choose ((hcores μ hμ).2.2.2.2.2)
    else fun _ ↦ 0
  refine ⟨P₂, ε, r, d, core, hP₂, hPc, hPΩ, hsmall, hbaseJets,
    hhyperP, hgnP, hε, hεcap, hr, hrr₀.trans hr₀ε, hd, fun μ hμ ↦ ?_⟩
  obtain ⟨hμJ, _, _, hleftJoin, hrightJoin, hexists⟩ := hcores μ hμ
  have hchosen : core μ = Classical.choose hexists := dite_eq_left hμ
  obtain ⟨hleft, hmiddle, hright, hleftAnchor, hrightAnchor, hode⟩ := Classical.choose_spec hexists
  obtain ⟨houterLeft, houterRight, _⟩ := houterMiddle μ (hμ.trans hrr₀)
  rw [hchosen]
  exact ⟨hJI hμJ, houterLeft, houterRight,
    hleftJoin, hrightJoin, hleftJoin.trans (habJoin.trans hrightJoin), hleft, hmiddle, hright,
    hleftAnchor.trans (hinit μ).1, hrightAnchor.trans (hinit μ).2, hode⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
