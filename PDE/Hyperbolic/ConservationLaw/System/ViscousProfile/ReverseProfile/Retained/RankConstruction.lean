/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.SmoothDependence.Variation.TwoBranchCancellation
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Retained.RankData
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Retained.Response

import PDE.Analysis.ODE.Interpolation.RetainedStrip
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Retained.StripRank
import PDE.LinearAlgebra.QuotientProjection

/-!
# Retained selected branches and the strip frame

The selected correction already produces an injective complete orbit and an open
state neighborhood containing its gate point. We retain these witnesses through
response transport and cancellation. They belong to the same orbit and the same
correction family, chosen before the tolerance.

The outgoing interval of definition is `[0, H]`. On its intersection with the phase
interval, the extended outgoing branch has the same speed germ as the corrected
branch on its interval of definition, whose first variation is the originally selected one. The rank
theorem therefore applies to the phase strip. Restricting its open rank set
to the inverse image of the selected state neighborhood supplies injectivity,
state containment, and the derivative equivalence needed by the compact chart.

Only this rank interval is shortened. The full common-interval flows, their
initial sections, their original moving events, and the gate-containing phase
interval remain in the output.
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE.Analysis
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

section RetainedRank

open PDE.Analysis.ODE

/-- Derive the chart frame from the retained first variation on the original time domain and a
selected determinant. The common extension and phase construction are reused.

The derivative comparison is made only after intersecting the phase interval
with `(0,H)`. Its proof composes the germ equality between the extended and the original
branch with the corrected/original first-variation identity. Injectivity and gate membership
are properties of the supplied orbit, not substitute rank or chart assumptions. -/
theorem exists_retained_selected_rank_strip
    {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    (hΨ : ContDiff ℝ ∞ Ψ) (σ : ℝ × (Fin 3 → ℝ))
    (f : ℝ^3 → ℝ^3) (hf : ContDiff ℝ ∞ f)
    (q : ℝ → ℝ^3) (hq : ContDiff ℝ ∞ q)
    (hqode : ∀ t, HasDerivAt q (f (q t)) t) (hqinj : Function.Injective q)
    {H e tStar : ℝ} (he : e ∈ Ioo (0 : ℝ) H)
    (htStar : tStar ∈ Ioo (0 : ℝ) e)
    {Ω : Set (ℝ^3)} {Jgate : Set ℝ}
    (hΩ : IsOpen Ω) (hgate : q tStar ∈ Ω) (hisolate : q ⁻¹' Ω ⊆ Jgate)
    (Fout Fincoming : ℝ → ℝ → ℝ^3)
    (hFout : ContDiff ℝ ∞ Fout.uncurry) (hFin : ContDiff ℝ ∞ Fincoming.uncurry)
    (I₀ : Set ℝ) (hI₀ : IsOpen I₀) (h0I₀ : (0 : ℝ) ∈ I₀)
    (hFoutBase : EqOn (fun t ↦ Fout t 0) q (Icc (0 : ℝ) H))
    (hFinBase : EqOn (fun t ↦ Fincoming t 0) q (Icc (e + e - H) (e + e)))
    (hFoutOde : ∀ μ ∈ I₀, ∀ t ∈ Icc (0 : ℝ) H,
      HasDerivAt (fun s ↦ Fout s μ) (f (Fout t μ) - μ • Fout t μ) t)
    (hFinOde : ∀ μ ∈ I₀, ∀ t ∈ Icc (e + e - H) (e + e),
      HasDerivAt (fun s ↦ Fincoming s μ)
        (f (Fincoming t μ) - μ • Fincoming t μ) t)
    (τout τin : ℝ → ℝ)
    (hτout : ContDiffOn ℝ ∞ τout I₀) (hτin : ContDiffOn ℝ ∞ τin I₀)
    (hτoutZero : τout 0 = e) (hτinZero : τin 0 = e)
    (hτoutNative : ∀ μ ∈ I₀, τout μ ∈ Ioo (0 : ℝ) H)
    (hτinNative : ∀ μ ∈ I₀, τin μ ∈ Ioo (e + e - H) (e + e))
    (ell : (ℝ^3) →L[ℝ] ℝ) (htransverse : ell (f (q e)) ≠ 0)
    (hzero : Fout (τout 0) 0 - Fincoming (τin 0) 0 = 0)
    (hfirst : HasDerivAt (fun μ ↦ Fout (τout μ) μ - Fincoming (τin μ) μ) 0 0)
    (hsecond :
      HasDerivAt (deriv (fun μ ↦ Fout (τout μ) μ - Fincoming (τin μ) μ)) 0 0)
    (hretained : EqOn (fun t ↦ deriv (Fout t) 0)
      (fun t ↦ deriv
        (retainedOutgoingBranch Ψ σ t) 0)
      (Icc (0 : ℝ) H))
    (rStar : Module.Basis (Fin 3) ℝ (ℝ^3)) (i : Fin 3)
    (hdet : Matrix.det ![⇑(f (q tStar)), ⇑(rStar i),
      ⇑(prescribedClockFullVariation Ψ σ (1, 0) tStar)] ≠ 0) :
    RetainedSelectedRankStrip Ψ σ f q Fout Fincoming τout τin I₀ Jgate Ω
      H e tStar rStar i := by
  obtain ⟨Gout, Gin, U, V, C, a, b, r, J, hGout, hGin, hinit,
      hbaseOut, hbaseIn, hgermOut, hgermIn, heStrip, htStrip, hstrip,
      hJ, h0J, hJI, hr, hspeed, hagree, hevents, hode,
      hU, hV, hC, hphase, hstripOde, hUbase, hVbase, hcubic⟩ :=
    exists_retained_phase_aligned_cubic_strip f hf q hqode he htStar
      Fout Fincoming hFout hFin I₀ hI₀ h0I₀ hFoutBase hFinBase hFoutOde hFinOde
      τout τin hτout hτin hτoutZero hτinZero hτoutNative hτinNative
      ell htransverse hfirst.deriv hsecond.deriv
  have hsubNative : Icc (max a 0) (min b H) ⊆ Icc (0 : ℝ) H :=
    Icc_subset_Icc (le_max_right a 0) (min_le_right b H)
  obtain ⟨O₀, l₀, u₀, hO₀, ht₀, hcompact₀, hO₀sub, hdetO₀, hframes⟩ :=
    exists_selected_actual_strip_rank_arc hΨ σ hf hq hqode hGout hU hV hC
      ((hτout.contDiffAt (hI₀.mem_nhds h0I₀)).differentiableAt (by simp)) hτoutZero hJ h0J
      (hbaseOut.mono (hsubNative.trans (Icc_subset_Icc (min_le_left _ _) (le_max_left _ _))))
      (fun t ht ↦ (hgermOut t (hsubNative ht)).deriv_eq.trans (hretained (hsubNative ht)))
      (fun μ hμ t ↦ (hphase μ hμ t).1)
      (fun t ht μ hμ ↦ hcubic t (Icc_subset_Icc (le_max_left a 0) (min_le_left b H) ht) μ hμ)
      ⟨max_lt htStrip.1 htStar.1, lt_min htStrip.2 (htStar.2.trans he.2)⟩ rStar i hdet
  -- State containment is chosen before the transition, on the same base orbit.
  let O := O₀ ∩ q ⁻¹' Ω
  have hO : IsOpen O := hO₀.inter (hΩ.preimage hq.continuous)
  have htO : tStar ∈ O := ⟨hcompact₀ (Ioo_subset_Icc_self ht₀), hgate⟩
  obtain ⟨l, u, _, hlu, hcompact⟩ := exists_Icc_mem_subset_of_mem_nhds (hO.mem_nhds htO)
  have hM : (fun μ ↦ Gout (τout μ) μ - Gin (τin μ) μ) =ᶠ[𝓝 (0 : ℝ)]
      (fun μ ↦ Fout (τout μ) μ - Fincoming (τin μ) μ) := by
    filter_upwards [hJ.mem_nhds h0J] with μ hμ
    rw [(hevents μ hμ).1, (hevents μ hμ).2]
  refine ⟨Gout, Gin, U, V, C, a, b, r, J, O, l, u,
    hGout, hGin, hinit, hbaseOut, hbaseIn, hgermOut, hgermIn,
    heStrip, htStrip, hstrip, hJ, h0J, hJI, hr, hspeed, hagree, hevents, hode,
    hU, hV, hC, hphase, hstripOde, hUbase, hVbase, hcubic, hM,
    hM.self_of_nhds.trans hzero, hfirst.congr_of_eventuallyEq hM,
    hsecond.congr_of_eventuallyEq hM.deriv,
    hO, Icc_mem_nhds_iff.mp hlu, hcompact, fun t ht ↦ ?_, (fun t ht ↦ hisolate ht.2),
    (fun t ht ↦ hdetO₀ t ht.1), fun θ hθ ↦ ?_⟩
  · obtain ⟨h₁, h₂⟩ := hO₀sub ht.1
    exact ⟨⟨⟨(max_lt_iff.mp h₁).1, (lt_min_iff.mp h₂).1⟩, (max_lt_iff.mp h₁).2,
      (lt_min_iff.mp h₂).2⟩, ht.2⟩
  obtain ⟨hw, hwbase, hframe⟩ := hframes θ hθ
  refine ⟨hw, hwbase.mono inter_subset_left,
    fun s hs t ht hst ↦ hqinj ((hwbase hs.1).symm.trans (hst.trans (hwbase ht.1))),
    fun t ht ↦ (hwbase ht.1).symm ▸ ht.2, fun t ht ↦ ?_⟩
  obtain ⟨hD, hdetPhase, D, hDeq⟩ := hframe t ht.1
  exact ⟨hD, hdetPhase, D, hDeq ▸ hD⟩

end RetainedRank

/-- Apply the selected correction to the two retained physical branches.
The fundamental solutions on the original time domains are constructed before target and
tolerance.
The outgoing response realizes the target, and the full incoming Hessian is zero.
Global strict hyperbolicity and every canonical genuinely nonlinear family are
inherited from the selected correction theorem. The same injective orbit and its
gate membership are retained before the signed target and tolerance. The
basis at the gate is carried along with its equality to the selected eigenvector
family, so the later rank theorems use the same basis. -/
theorem exists_selected_retained_branch_responses_with_isolation {δ A B H tAnchor tStar : ℝ}
    {c : Fin 3 → ℝ} {b : (Fin 3 → ℝ) × ℝ → ℝ} {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ} {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))} (hδ : 0 < δ)
    (hδsmall : δ < 1 / 4) (hAB : A ^ 2 < B ^ 2) (hb : ContDiff ℝ ∞ b)
    (hbsupport : tsupport (fun y ↦ b (c, y)) ⊆ Ioo (205 : ℝ) (2051 / 10)) (hΨ : ContDiff ℝ ∞ Ψ)
    (hselected : ((δ, c), (0, 0)) ∈ N) (hinitial : ∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3))
    (hode : ∀ θ ∈ N, ∀ s ∈ Icc (0 : ℝ) H, HasDerivAt (fun u ↦ Ψ (u, θ))
      (concreteGatedFlux θ.1.1 (clockFeedback A B) (fun y ↦ b (θ.1.2, y)) (Ψ (s, θ)) - θ.2.1 •
      Ψ (s, θ)) s)
    (hevent : ∀ θ ∈ N, T θ ∈ Ioo (0 : ℝ) H ∧ Ψ (T θ, θ) 1 = 0) (i j : Fin 3) (hij : i ≠ j) :
    let θ0 := ((δ, c), ((0 : ℝ), (0 : ℝ)))
    let e := T θ0
    let b0 : ℝ → ℝ := fun y ↦ b (c, y)
    let f := concreteGatedFlux δ (clockFeedback A B) b0
    let γ : ℝ → ℝ^3 := fun t ↦ Ψ (t, θ0)
    let W := prescribedClockFullVariation Ψ (δ, c) (1, 0)
    let rStar := GatedFlux.rightEigenvector (fastLogCosh δ) MiddleClock.g cutoff
      (clockFeedback A B) b0 (γ tStar)
    tStar ∈ Ioo (0 : ℝ) e →
    205 < γ tStar 1 → 2 < γ tStar 2 → (γ tStar 2) ^ 2 < A ^ 2 →
    0 < γ e 2 → γ e 0 / γ e 2 = 1 →
    Matrix.det ![⇑(deriv γ tStar), ⇑(rStar i), ⇑(W tStar)] ≠ 0 →
    Matrix.det ![⇑(deriv γ tStar), ⇑(rStar j), ⇑(W tStar)] ≠ 0 →
    (∃ a : Fin 3 → ℝ, (∀ k, a k ≠ 0) ∧ deriv γ tStar = ∑ k, a k • rStar k) →
    ∀ (S : Evolution.FundamentalSolution
      (fun t ↦ fderiv ℝ f (γ t)) tAnchor (Icc (0 : ℝ) e))
      (L : (ℝ^3) →L[ℝ] (ℝ^2)),
      LinearMap.ker L.toLinearMap = Submodule.span ℝ ({f (γ e)} : Set (ℝ^3)) →
      ∃ (q : ℝ → ℝ^3) (J : Set ℝ) (U : Set (ℝ^3)),
        IsViscousProfile f 0 0 0 q ∧ ContDiff ℝ ∞ q ∧
        (∀ t, HasDerivAt q (f (q t)) t) ∧ EqOn q γ (Icc (0 : ℝ) H) ∧
        EqOn (fun t ↦ retainedOutgoingBranch Ψ (δ, c) t 0) q (Icc (0 : ℝ) H) ∧
        EqOn (fun t ↦ retainedIncomingBranch Ψ (δ, c) e t 0) q
          (Icc (e + e - H) (e + e)) ∧
        IsOpen J ∧ J ⊆ Ioo (0 : ℝ) e ∧ IsOpen U ∧ q ⁻¹' U ⊆ J ∧
        Function.Injective q ∧ q tStar ∈ U ∧
        ∃ rGate : Module.Basis (Fin 3) ℝ (ℝ^3),
        (∀ k, rGate k = rStar k) ∧
        ∃ (Sout : Evolution.FundamentalSolution
          (fun t ↦ fderiv ℝ f (q t)) 0 (Icc (0 : ℝ) H))
          (Sin : Evolution.FundamentalSolution
            (fun t ↦ fderiv ℝ f (q t)) (e + e) (Icc (e + e - H) (e + e))),
          (∀ t ∈ Icc (0 : ℝ) e, Sout.propagator e t = S.propagator e t) ∧
          ∀ target : ℝ^2, ∀ η : ℝ, 0 < η → ∃ P : ℝ^3 → ℝ^3,
            ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ tsupport P ⊆ U ∧
            (∀ t, P (q t) = 0 ∧ fderiv ℝ P (q t) = 0) ∧
            (∫ t in (0 : ℝ)..e, L (Sout.propagator e t
              (fderiv ℝ (fderiv ℝ P) (q t)
                (deriv (retainedOutgoingBranch Ψ (δ, c) t) 0)
                (deriv (retainedOutgoingBranch Ψ (δ, c) t) 0)))) = target ∧
            (∀ t ∈ Icc e (e + e), fderiv ℝ (fderiv ℝ P) (q t) = 0) ∧
            (∫ t in (e + e)..e, L (Sin.propagator e t
              (fderiv ℝ (fderiv ℝ P) (q t)
                (deriv (retainedIncomingBranch Ψ (δ, c) e t) 0)
                (deriv (retainedIncomingBranch Ψ (δ, c) e t) 0)))) = 0 ∧
            (∀ x, ‖P x‖ < η ∧ ‖fderiv ℝ P x‖ < η) ∧
            (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
            ∀ k, IsGenuinelyNonlinearFamily (f + P) k := by
  intro θ0 e b0 f γ W rStar htStar hy hzInner hzOuter hz hρ hi hj hexp S L hL
  obtain ⟨V, r, J, q, U, l, u, χ, hV, htV, hrStar, hsmooth, hdual, hspectral,
      hcoordinates, hJ, htJ, hJV, hprofile, hqSmooth, hqODE, hqγ, hreflected,
      hinjective, hqne, hU, hl0, hlt, htu, hue, hinnerJ, hinnerU, hisolate,
      hrevU, hχ, hχcompact, hχsupport, hχnonneg, hχintegral, hfamily⟩ :=
    exists_selected_clock_neutral_integrated_correction
      hδ hδsmall hAB hb hbsupport hΨ hselected hinitial hode hevent i j hij
      htStar hy hzInner hzOuter hz hρ hi hj hexp S L hL
  have he : e ∈ Ioo (0 : ℝ) H := (hevent θ0 hselected).1
  have hJinner : J ⊆ Ioo (0 : ℝ) e := fun _ ht ↦ (hJV ht).2
  have hf : ContDiff ℝ ∞ f := contDiff_concreteGatedFlux δ (contDiff_clockFeedback A B)
    (hb.comp (contDiff_const.prodMk contDiff_id))
  have hγODE (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) : HasDerivAt γ (f (γ t)) t := by
    simpa only [γ, f, b0, θ0, zero_smul, sub_zero] using hode θ0 hselected t ht
  have hbase := retained_branches_base_eq hqγ hreflected
  -- Extend the incoming base identification to its interval of definition.
  have hinODE (t : ℝ) (ht : t ∈ Icc (e + e - H) (e + e)) :
      HasDerivAt (fun s ↦ retainedIncomingBranch Ψ (δ, c) e s 0)
        (f (retainedIncomingBranch Ψ (δ, c) e t 0)) t := by
    have hD := GatedFlux.reversal.hasFDerivAt.comp_hasDerivAt t
      (HasDerivAt.comp_const_sub (e + e) t (hγODE (e + e - t) ⟨by linarith [ht.2],
        by linarith [ht.1]⟩))
    have hReversal : f (GatedFlux.reversal (γ (e + e - t))) =
        -GatedFlux.reversal (f (γ (e + e - t))) := by
      simpa only [f, concreteGatedFlux, neg_zero, zero_smul, sub_zero] using!
        (GatedFlux.flux_sub_smul_reversal (fastLogCosh δ) MiddleClock.g cutoff
          (clockFeedback A B) b0 MiddleClock.g_neg 0 (γ (e + e - t)))
    have hD' : HasDerivAt (fun s ↦ GatedFlux.reversal (γ (e + e - s)))
        (f (GatedFlux.reversal (γ (e + e - t)))) t := by
      rw [hReversal]
      simpa only [Function.comp_def, map_neg] using! hD
    simpa only [retainedIncomingBranch, neg_zero, mul_zero, γ, θ0] using hD'
  have hinNative := retainedIncomingBranch_base_eq_on_native_interval hf he hqODE hinODE
    (hbase.2 (show e ∈ Icc e (e + e) from ⟨le_rfl, by linarith [he.1]⟩))
  -- Existence uses only continuity on each compact interval of definition.
  have hcoeff : ContDiff ℝ ∞ (fun t ↦ fderiv ℝ f (q t)) :=
    (hf.fderiv_right (by simp)).comp hqSmooth
  let Sout : Evolution.FundamentalSolution (fun t ↦ fderiv ℝ f (q t)) 0 (Icc (0 : ℝ) H) :=
    Evolution.fundamentalSolutionIcc hcoeff.continuous.continuousOn
      ⟨0, ⟨le_rfl, he.1.le.trans he.2.le⟩⟩
  let Sin : Evolution.FundamentalSolution
      (fun t ↦ fderiv ℝ f (q t)) (e + e) (Icc (e + e - H) (e + e)) :=
    Evolution.fundamentalSolutionIcc hcoeff.continuous.continuousOn
      ⟨e + e, ⟨by linarith [he.1, he.2], le_rfl⟩⟩
  refine ⟨q, J, U, hprofile, hqSmooth, hqODE, hqγ, hbase.1, hinNative, hJ, hJinner, hU,
    hisolate, hinjective, hqγ ⟨htStar.1.le, (htStar.2.trans he.2).le⟩ ▸ hinnerU ⟨hlt.le, htu.le⟩,
    r tStar, hrStar, Sout, Sin,
    fun t ht ↦ Evolution.FundamentalSolution.propagator_eq_of_orbit_eqOn he.1.le he.2.le hqγ S
      Sout ht, fun target η hη ↦ ?_⟩
  obtain ⟨P, hP, hPc, hsupport, hPjets, -, -, -, hIntegralGamma, hsmall, hhyper, hgn⟩ :=
    hfamily target η hη
  exact ⟨P, hP, hPc, hsupport, (fun t ↦ ⟨(hPjets t).1, (hPjets t).2.1⟩),
    (retainedOutgoingBranch_response_eq hΨ he.1.le he.2.le hqγ S Sout P L).trans hIntegralGamma,
    fun t ht ↦ fderiv_of_notMem_tsupport ℝ fun hp ↦ not_lt_of_ge ht.1
      (hJinner (hisolate (hsupport (tsupport_fderiv_subset ℝ hp)))).2,
    retainedIncomingBranch_response_eq_zero he.1.le hJinner hisolate hsupport Sin L,
    hsmall, hhyper, hgn⟩

/-- Cancel the moving second mismatch for one retained selected flux.

The terminal ratio, its displacement derivative and the weighted scalar residual
are the selected matching equations. The nonzero middle velocity is the output
of the strengthened selector. The projection and the fundamental solution along
the original orbit are constructed before the global orbit and any correction.
The fundamental solution is normalized at time zero.

The common orbit, support sets, speed neighborhood of the uncorrected flow and both original
propagators precede the positive tolerance. For every tolerance the theorem
constructs one compactly supported correction, two smooth solution
families and their middle-section events. Their moving mismatch has value,
first derivative and second derivative zero at speed zero. Global strict
hyperbolicity and all canonical genuinely nonlinear families are retained.

The selected support neighborhood and injective orbit are retained before the
correction. The same corrected families on the original time domains then produce a cubic
strip and its compact chart frame; the selected determinant supplies the rank. -/
theorem exists_selected_second_jet_cancellation_with_rank {δ A B H tStar : ℝ} {c : Fin 3 → ℝ}
    {b : (Fin 3 → ℝ) × ℝ → ℝ} {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {T : ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ} {N : Set ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ))} (hδ : 0 < δ)
    (hδsmall : δ < 1 / 4) (hAB : A ^ 2 < B ^ 2) (hb : ContDiff ℝ ∞ b)
    (hbsupport : tsupport (fun y ↦ b (c, y)) ⊆ Ioo (205 : ℝ) (2051 / 10)) (hΨ : ContDiff ℝ ∞ Ψ)
    (hN : IsOpen N) (hselected : ((δ, c), (0, 0)) ∈ N) (hT : ContDiffOn ℝ ∞ T N)
    (hinitial : ∀ θ, Ψ (0, θ) = (!₂[0, θ.2.2, 1] : ℝ^3))
    (hode : ∀ θ ∈ N, ∀ s ∈ Icc (0 : ℝ) H, HasDerivAt (fun u ↦ Ψ (u, θ))
      (concreteGatedFlux θ.1.1 (clockFeedback A B) (fun y ↦ b (θ.1.2, y)) (Ψ (s, θ)) - θ.2.1 •
      Ψ (s, θ)) s)
    (hevent : ∀ θ ∈ N, T θ ∈ Ioo (0 : ℝ) H ∧ Ψ (T θ, θ) 1 = 0) (i j : Fin 3) (hij : i ≠ j) :
    let θ0 := ((δ, c), ((0 : ℝ), (0 : ℝ)))
    let e := T θ0
    let b0 : ℝ → ℝ := fun y ↦ b (c, y)
    let f := concreteGatedFlux δ (clockFeedback A B) b0
    let γ : ℝ → ℝ^3 := fun t ↦ Ψ (t, θ0)
    let W := prescribedClockFullVariation Ψ (δ, c) (1, 0)
    let rStar := GatedFlux.rightEigenvector (fastLogCosh δ) MiddleClock.g cutoff
      (clockFeedback A B) b0 (γ tStar)
    let Q := retainedTerminalState Ψ T (δ, c)
    let Fout := retainedOutgoingBranch Ψ (δ, c)
    let Fincoming := retainedIncomingBranch Ψ (δ, c) e
    let τout := retainedOutgoingEvent T (δ, c)
    let τin := retainedIncomingEvent T (δ, c) e
    let Mold : ℝ → ℝ^3 := fun μ ↦ Fout (τout μ) μ - Fincoming (τin μ) μ
    tStar ∈ Ioo (0 : ℝ) e →
    205 < γ tStar 1 → 2 < γ tStar 2 → (γ tStar 2) ^ 2 < A ^ 2 →
    0 < Q (0, 0) 2 → Q (0, 0) 0 / Q (0, 0) 2 = 1 →
    deriv (fun a ↦ Q (0, a) 0 / Q (0, a) 2) 0 = 0 →
    Q (0, 0) 2 * deriv (fun μ ↦ Q (μ, 0) 0 / Q (μ, 0) 2) 0 +
      2 * deriv (fun μ ↦ Q (μ, 0) 2) 0 +
      2000000 * deriv (fun a ↦ Q (0, a) 2) 0 = 0 →
    (f (γ e)) 1 ≠ 0 →
    Matrix.det ![⇑(deriv γ tStar), ⇑(rStar i), ⇑(W tStar)] ≠ 0 →
    Matrix.det ![⇑(deriv γ tStar), ⇑(rStar j), ⇑(W tStar)] ≠ 0 →
    (∃ a : Fin 3 → ℝ, (∀ k, a k ≠ 0) ∧ deriv γ tStar = ∑ k, a k • rStar k) →
    ∃ (S : Evolution.FundamentalSolution
      (fun t ↦ fderiv ℝ f (γ t)) 0 (Icc (0 : ℝ) e))
      (L : (ℝ^3) →L[ℝ] (ℝ^2)),
      Function.Surjective L ∧
      LinearMap.ker L.toLinearMap = Submodule.span ℝ ({f (γ e)} : Set (ℝ^3)) ∧
      ∃ (q : ℝ → ℝ^3) (J : Set ℝ) (U : Set (ℝ^3)) (I₀ : Set ℝ),
        IsOpen I₀ ∧ (0 : ℝ) ∈ I₀ ∧
        (∀ μ ∈ I₀,
          ((δ, c), (μ, 0)) ∈ N ∧ ((δ, c), (-μ, -2000000 * μ)) ∈ N) ∧
        ContDiffOn ℝ ∞ τout I₀ ∧ ContDiffOn ℝ ∞ τin I₀ ∧
        IsViscousProfile f 0 0 0 q ∧ ContDiff ℝ ∞ q ∧
        (∀ t, HasDerivAt q (f (q t)) t) ∧ EqOn q γ (Icc (0 : ℝ) H) ∧
        EqOn (fun t ↦ Fout t 0) q (Icc (0 : ℝ) H) ∧
        EqOn (fun t ↦ Fincoming t 0) q (Icc (e + e - H) (e + e)) ∧
        IsOpen J ∧ J ⊆ Ioo (0 : ℝ) e ∧ IsOpen U ∧ q ⁻¹' U ⊆ J ∧
        Function.Injective q ∧ q tStar ∈ U ∧
        ∃ rGate : Module.Basis (Fin 3) ℝ (ℝ^3),
        (∀ k, rGate k = rStar k) ∧
        ∃ (Sout : Evolution.FundamentalSolution
          (fun t ↦ fderiv ℝ f (q t)) 0 (Icc (0 : ℝ) H))
          (Sin : Evolution.FundamentalSolution
            (fun t ↦ fderiv ℝ f (q t)) (e + e) (Icc (e + e - H) (e + e))),
          (∀ t ∈ Icc (0 : ℝ) e, Sout.propagator e t = S.propagator e t) ∧
          ∀ η : ℝ, 0 < η →
            ∃ (P : ℝ^3 → ℝ^3) (Gout Gin : ℝ → ℝ → ℝ^3)
              (υout υin : ℝ → ℝ) (I : Set ℝ),
              let M : ℝ → ℝ^3 := fun μ ↦ Gout (υout μ) μ - Gin (υin μ) μ
              ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ tsupport P ⊆ U ∧
              (∀ t, P (q t) = 0 ∧ fderiv ℝ P (q t) = 0) ∧
              (∀ x, ‖P x‖ < η ∧ ‖fderiv ℝ P x‖ < η) ∧
              (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
              (∀ k, IsGenuinelyNonlinearFamily (f + P) k) ∧
              (∫ t in (0 : ℝ)..e, L (Sout.propagator e t
                (fderiv ℝ (fderiv ℝ P) (q t)
                  (deriv (Fout t) 0) (deriv (Fout t) 0)))) =
                -L (deriv (deriv Mold) 0) ∧
              (∀ t ∈ Icc e (e + e), fderiv ℝ (fderiv ℝ P) (q t) = 0) ∧
              (∫ t in (e + e)..e, L (Sin.propagator e t
                (fderiv ℝ (fderiv ℝ P) (q t)
                  (deriv (Fincoming t) 0) (deriv (Fincoming t) 0)))) = 0 ∧
              ContDiff ℝ ∞ Gout.uncurry ∧ ContDiff ℝ ∞ Gin.uncurry ∧
              IsOpen I ∧ (0 : ℝ) ∈ I ∧ I ⊆ I₀ ∧
              (∀ μ, Gout 0 μ = (!₂[0, 0, 1] : ℝ^3) ∧
                Gin (e + e) μ = (!₂[1, 2000000 * μ, 0] : ℝ^3)) ∧
              EqOn (fun t ↦ Gout t 0) q (Icc (0 : ℝ) H) ∧
              EqOn (fun t ↦ Gin t 0) q (Icc (e + e - H) (e + e)) ∧
              (∀ μ ∈ I,
                (∀ t ∈ Icc (0 : ℝ) H,
                  HasDerivAt (fun s ↦ Gout s μ)
                    (f (Gout t μ) + P (Gout t μ) - μ • Gout t μ) t) ∧
                (∀ t ∈ Icc (e + e - H) (e + e),
                  HasDerivAt (fun s ↦ Gin s μ)
                    (f (Gin t μ) + P (Gin t μ) - μ • Gin t μ) t)) ∧
              ContDiffOn ℝ ∞ υout I ∧ ContDiffOn ℝ ∞ υin I ∧
              υout 0 = e ∧ υin 0 = e ∧
              (∀ μ ∈ I,
                (υout μ ∈ Ioo (0 : ℝ) H ∧ Gout (υout μ) μ 1 = 0) ∧
                (υin μ ∈ Ioo (e + e - H) (e + e) ∧ Gin (υin μ) μ 1 = 0)) ∧
              EqOn (fun t ↦ deriv (Gout t) 0) (fun t ↦ deriv (Fout t) 0)
                (Icc (0 : ℝ) H) ∧
              EqOn (fun t ↦ deriv (Gin t) 0) (fun t ↦ deriv (Fincoming t) 0)
                (Icc (e + e - H) (e + e)) ∧
              deriv υout 0 = deriv τout 0 ∧ deriv υin 0 = deriv τin 0 ∧
              M 0 = 0 ∧ HasDerivAt M 0 0 ∧ HasDerivAt (deriv M) 0 0 ∧
              RetainedSelectedRankStrip Ψ (δ, c) (f + P) q
                Gout Gin υout υin I J U H e tStar rGate i := by
  intro θ0 e b0 f γ W rStar Q Fout Fincoming τout τin Mold
    htStar hy hzInner hzOuter hz hρ hρa hres hmiddle hi hj hexp
  have hf : ContDiff ℝ ∞ f := contDiff_concreteGatedFlux δ (contDiff_clockFeedback A B)
    (hb.comp (contDiff_const.prodMk contDiff_id))
  have heSelected : e ∈ Ioo (0 : ℝ) H := (hevent θ0 hselected).1
  have hγ : ContDiff ℝ ∞ γ := hΨ.comp (contDiff_id.prodMk contDiff_const)
  let S : Evolution.FundamentalSolution (fun t ↦ fderiv ℝ f (γ t)) 0 (Icc (0 : ℝ) e) :=
    Evolution.fundamentalSolutionIcc ((hf.fderiv_right (by simp)).comp hγ).continuous.continuousOn
      ⟨0, ⟨le_rfl, heSelected.1.le⟩⟩
  obtain ⟨L, hLsurj, hL⟩ := EuclideanSpace.exists_surjective_projection_ker_span_singleton
    (fun h ↦ hmiddle (congrArg (· 1) h) : f (γ e) ≠ 0)
  refine ⟨S, L, hLsurj, hL, ?_⟩
  -- Fix the uncorrected events and their common speed neighborhood before selecting P.
  obtain ⟨I₀, hI₀, h0I₀, hparameters, hτout, hτin, hτout0, hτin0,
      he, hFoutOde, hFinOde, hOldSections⟩ :=
    exists_retained_physical_branch_events (σ := (δ, c)) hN hselected hT hode hevent
  have hOldFirst : Mold 0 = 0 ∧ HasDerivAt Mold 0 0 :=
    selected_retained_moving_mismatch_first e hΨ hN hselected hT
      (fun θ hθ ↦ (hevent θ hθ).2) hz hρ hρa hres
  -- The proof applies the integrated correction once, then fixes both original
  -- propagators. Its target family retains that same q, J, U and normalized cutoff.
  obtain ⟨q, J, U, hprofile, hqSmooth, hqODE, hqγ, hFoutBase, hFinBase,
      hJ, hJinner, hU, hisolate, hqinj, hgate, rGate, hrGate,
      Sout, Sin, hpropagators, hcorrections⟩ :=
    exists_selected_retained_branch_responses_with_isolation
      hδ hδsmall hAB hb hbsupport hΨ hselected hinitial hode hevent i j hij
      htStar hy hzInner hzOuter hz hρ hi hj hexp S L hL
  have hqe : q e = γ e := hqγ (Ioo_subset_Icc_self he)
  have hqsection : q e 1 = 0 := (congrArg (· 1) hqe).trans (hevent θ0 hselected).2
  let ell : (ℝ^3) →L[ℝ] ℝ := PiLp.proj (2 : ENNReal) (fun _ : Fin 3 ↦ ℝ) (1 : Fin 3)
  have htransverse : ell (f (q e)) ≠ 0 := show f (q e) 1 ≠ 0 from hqe ▸ hmiddle
  refine ⟨q, J, U, I₀, hI₀, h0I₀, hparameters, hτout, hτin,
    hprofile, hqSmooth, hqODE, hqγ, hFoutBase, hFinBase, hJ, hJinner,
    hU, hisolate, hqinj, hgate, rGate, hrGate, Sout, Sin, hpropagators, fun η hη ↦ ?_⟩
  -- The sign and the uncorrected event families are fixed: this is the second mismatch
  -- of the originally selected branches, projected by the previously fixed L.
  obtain ⟨P, hP, hPc, hsupport, hPjets, hresponse, hHessian,
      hIncomingResponse, hsmall, hhyper, hgn⟩ := hcorrections (-L (deriv (deriv Mold) 0)) η hη
  obtain ⟨Gout, Gin, υout, υin, I, hGout, hGin, hI, h0I, hIsub,
      hInitial, hGoutBase, hGinBase, hOde, hυout, hυin, hυout0, hυin0,
      hNewSections, hGoutFirst, hGinFirst, hυoutFirst, hυinFirst, hMzero, hMfirst, hMsecond⟩ :=
    PDE.Analysis.ODE.exists_two_branch_second_jet_cancellation_on_two_intervals f hf q hqODE
      (loOut := 0) (hiOut := H) (loIn := e + e - H) (hiIn := e + e)
      (cOut := 0) (e := e) (cIn := e + e) le_rfl he.1.le (le_add_of_nonneg_right he.1.le) le_rfl
      Fout Fincoming (contDiff_retainedOutgoingBranch hΨ (δ, c))
      (contDiff_retainedIncomingBranch hΨ (δ, c) e) I₀ hI₀ h0I₀ hFoutBase hFinBase hFoutOde
      hFinOde τout τin (hτout.of_le (by simp)) (hτin.of_le (by simp)) hτout0 hτin0 ell
      (fun μ hμ ↦ ⟨(hOldSections μ hμ).1.1, (hOldSections μ hμ).1.2.trans hqsection.symm⟩)
      (fun μ hμ ↦ ⟨(hOldSections μ hμ).2.1, (hOldSections μ hμ).2.2.trans hqsection.symm⟩)
      htransverse Sout Sin L (hqe ▸ hL) hOldFirst.2
      P hP (fun t ↦ (hPjets t).1) (fun t ↦ (hPjets t).2) hresponse
      (fun t ht ↦ by simp [hHessian t ht])
  have hγt : HasDerivAt γ (f (γ tStar)) tStar := by
    simpa only [γ, f, b0, θ0, zero_smul, sub_zero] using
      hode θ0 hselected tStar ⟨htStar.1.le, (htStar.2.trans he.2).le⟩
  have hdetCorrected : Matrix.det ![⇑((f + P) (q tStar)), ⇑(rGate i), ⇑(W tStar)] ≠ 0 := by
    change Matrix.det ![⇑(f (q tStar) + P (q tStar)), ⇑(rGate i), ⇑(W tStar)] ≠ 0
    rw [(hPjets tStar).1, add_zero, hqγ ⟨htStar.1.le, (htStar.2.trans he.2).le⟩, hrGate i]
    simpa only [hγt.deriv] using hi
  refine ⟨P, Gout, Gin, υout, υin, I, hP, hPc, hsupport, hPjets, hsmall,
    hhyper, hgn, hresponse, hHessian, hIncomingResponse, hGout, hGin,
    hI, h0I, hIsub, fun μ ↦ ?_, hGoutBase, hGinBase, hOde, hυout, hυin, hυout0, hυin0,
    fun μ hμ ↦ ?_, hGoutFirst, hGinFirst, hυoutFirst, hυinFirst, hMzero, hMfirst, hMsecond,
    exists_retained_selected_rank_strip hΨ (δ, c) (f + P) (hf.add hP) q hqSmooth
      (fun t ↦ by simpa only [Pi.add_apply, (hPjets t).1, add_zero] using hqODE t) hqinj he
      htStar hU hgate hisolate Gout Gin hGout hGin I hI h0I hGoutBase hGinBase
      (fun μ hμ ↦ (hOde μ hμ).1) (fun μ hμ ↦ (hOde μ hμ).2) υout υin hυout hυin hυout0 hυin0
      (fun μ hμ ↦ (hNewSections μ hμ).1.1) (fun μ hμ ↦ (hNewSections μ hμ).2.1) ell
      (show ell ((f + P) (q e)) ≠ 0 by
        simpa only [Pi.add_apply, (hPjets e).1, add_zero] using htransverse)
      hMzero hMfirst hMsecond hGoutFirst rGate i hdetCorrected⟩
  · have hOldInitial := retained_branches_initial hinitial (δ, c) e μ
    exact ⟨(hInitial μ).1.trans hOldInitial.1, (hInitial μ).2.trans hOldInitial.2⟩
  · obtain ⟨hout, hin⟩ := hNewSections μ hμ
    exact ⟨⟨hout.1, hout.2.trans hqsection⟩, ⟨hin.1, hin.2.trans hqsection⟩⟩

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
