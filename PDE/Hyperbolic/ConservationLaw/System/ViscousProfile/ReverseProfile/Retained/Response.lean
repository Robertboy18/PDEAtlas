/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Interval
public import PDE.Analysis.Evolution.ODE.Linear.Fundamental.Propagator.Congruence
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Corrections.Neutral.Selected
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Retained.Branches

/-!
# Transport of the selected response to the retained physical branches

The selected correction uses the original orbit `γ` on `[0, e]`. The physical
branch comparison uses the completed orbit `q` and the two original time intervals.
Their outgoing propagators agree by restriction, coefficient congruence, and
uniqueness. The outgoing speed derivative is the already retained full variation.

On the incoming segment `[e, 2e]`, support isolation puts every orbit point outside
`tsupport P`. Mathlib's derivative support lemmas then give the zero Hessian as
a bilinear map, irrespective of the incoming speed variation. Its signed response from
`2e` back to `e` is therefore zero.

The final theorem applies the selected correction theorem and constructs both original
fundamental solutions from continuous coefficients. All branch data and both
propagators precede the signed target and correction.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped BigOperators ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
namespace PrescribedClockLowerDescent

/-- The selected response is exactly the response of the retained outgoing branch.
Both the propagator and the speed derivative are transported by proved identities;
this theorem does not take the response integral as a hypothesis. -/
theorem retainedOutgoingBranch_response_eq {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    (hΨ : ContDiff ℝ ∞ Ψ) {σ : ℝ × (Fin 3 → ℝ)} {f : ℝ^3 → ℝ^3} {q : ℝ → ℝ^3} {e H tAnchor sOut : ℝ}
    (he : 0 ≤ e) (heH : e ≤ H) (hqγ : EqOn q (fun t ↦ Ψ (t, (σ, (0, 0)))) (Icc (0 : ℝ) H))
    (S : Evolution.FundamentalSolution (fun t ↦ fderiv ℝ f (Ψ (t, (σ, (0, 0))))) tAnchor
      (Icc (0 : ℝ) e))
    (Sout : Evolution.FundamentalSolution (fun t ↦ fderiv ℝ f (q t)) sOut (Icc (0 : ℝ) H))
    (P : ℝ^3 → ℝ^3) (L : (ℝ^3) →L[ℝ] (ℝ^2)) :
    (∫ t in (0 : ℝ)..e, L (Sout.propagator e t
      (fderiv ℝ (fderiv ℝ P) (q t)
        (deriv (retainedOutgoingBranch Ψ σ t) 0)
        (deriv (retainedOutgoingBranch Ψ σ t) 0)))) =
    (∫ t in (0 : ℝ)..e, L (S.propagator e t
      (fderiv ℝ (fderiv ℝ P) (Ψ (t, (σ, (0, 0))))
        (prescribedClockFullVariation Ψ σ (1, 0) t)
        (prescribedClockFullVariation Ψ σ (1, 0) t)))) := by
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  have ht' : t ∈ Icc (0 : ℝ) e := uIcc_subset_Icc ⟨le_rfl, he⟩ ⟨he, le_rfl⟩ ht
  rw [Evolution.FundamentalSolution.propagator_eq_of_orbit_eqOn he heH hqγ S Sout ht',
    (hasDerivAt_retainedOutgoingBranch_speed hΨ σ t).deriv, hqγ (Icc_subset_Icc le_rfl heH ht')]

/-- The incoming response vanishes with its physical speed derivative and
orientation `2e..e`. Support isolation, rather than any restriction on that
variation, supplies the zero forcing. -/
theorem retainedIncomingBranch_response_eq_zero {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
    {σ : ℝ × (Fin 3 → ℝ)} {f : ℝ^3 → ℝ^3} {q : ℝ → ℝ^3} {P : ℝ^3 → ℝ^3} {J : Set ℝ} {U : Set (ℝ^3)}
    {e H sIn : ℝ} (he : 0 ≤ e) (hJ : J ⊆ Ioo (0 : ℝ) e) (hisolate : q ⁻¹' U ⊆ J)
    (hsupport : tsupport P ⊆ U)
    (Sin : Evolution.FundamentalSolution (fun t ↦ fderiv ℝ f (q t)) sIn (Icc (e + e - H) (e + e)))
    (L : (ℝ^3) →L[ℝ] (ℝ^2)) :
    (∫ t in (e + e)..e, L (Sin.propagator e t (fderiv ℝ (fderiv ℝ P) (q t)
      (deriv (retainedIncomingBranch Ψ σ e t) 0) (deriv (retainedIncomingBranch Ψ σ e t) 0)))) =
      0 := by
  have he2 : e ≤ e + e := le_add_of_nonneg_right he
  refine (intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ^2)) fun t ht ↦ ?_).trans
    intervalIntegral.integral_zero
  have ht' : t ∈ Icc e (e + e) := uIcc_subset_Icc ⟨he2, le_rfl⟩ ⟨le_rfl, he2⟩ ht
  -- Differentiation cannot enlarge the topological support.
  have hHessian : fderiv ℝ (fderiv ℝ P) (q t) = 0 := fderiv_of_notMem_tsupport ℝ fun hp ↦
    not_lt_of_ge ht'.1 (hJ (hisolate (hsupport (tsupport_fderiv_subset ℝ hp)))).2
  simp [hHessian]

/-- Apply the selected correction to the two retained physical branches.
The fundamental solutions on the original time domains are constructed before target and
tolerance.
The outgoing response realizes the target, and the full incoming Hessian is zero.
Global strict hyperbolicity and every canonical genuinely nonlinear family are
inherited from the selected correction theorem. -/
theorem exists_selected_retained_branch_responses {δ A B H tAnchor tStar : ℝ} {c : Fin 3 → ℝ}
    {b : (Fin 3 → ℝ) × ℝ → ℝ} {Ψ : ℝ × ((ℝ × (Fin 3 → ℝ)) × (ℝ × ℝ)) → ℝ^3}
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
    hisolate, Sout, Sin,
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

end PrescribedClockLowerDescent
end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
