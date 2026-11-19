/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Interpolation.OuterEnvelope
public import PDE.Hyperbolic.ConservationLaw.System.Corrections.Cubic.FarSupport

/-!
# Outer envelopes for a characteristic-preserving correction

Choose the chart first, then separate the compact far-time image before choosing
the amplitude and correction. The generic envelope lemma supplies outer time
collars for that same correction. Shrinking the signed speed interval preserves
its small derivatives, characteristic families and interpolation equation.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System

open PDE.Analysis.ODE PDE.Analysis.ODE.StripRank

/-- Assemble the chart, far-image exclusion, and outer envelopes.

The complete selected orbit supplies injectivity. Only `[0,L]` is required for
the zero-speed identities. The chosen rank arc lies between those anchors.
After the chart returns `T`, the far set is formed from the closed outer pieces
minus `T`; the constructor excludes its image before choosing `A`.

The same correction is smooth, arbitrarily small through order two, preserves
hyperbolicity and every genuine-nonlinearity family, and solves the interpolation
ODE. Shrinking its speed interval for the outer envelopes does not change it. -/
theorem exists_actual_outer_envelopes_of_rank_frame {f : ℝ^3 → ℝ^3} {q W : ℝ → ℝ^3} {ν : ℝ^3}
    {phaseSlope : ℝ} {U V : ℝ → ℝ → ℝ^3} {C : ℝ × ℝ → ℝ^3} {lo hi tStar L : ℝ} {J O : Set ℝ}
    {Ω : Set (ℝ^3)} (hf : ContDiff ℝ ∞ f) (hhyper : ∀ x, IsStrictlyHyperbolicAt f x)
    (hgn : ∀ i, IsGenuinelyNonlinearFamily f i) (hU : ContDiff ℝ ∞ U.uncurry)
    (hV : ContDiff ℝ ∞ V.uncurry) (hC : ContDiff ℝ ∞ C) (hJ : IsOpen J) (hzero : (0 : ℝ) ∈ J)
    (hcubic : ∀ t ∈ Icc lo hi, ∀ μ ∈ J, V t μ - U t μ = μ ^ 3 • C (t, μ))
    (hode : ∀ t ∈ Icc lo hi, ∀ μ ∈ J, HasDerivAt (fun s ↦ U s μ) (f (U t μ) - μ • U t μ) t ∧
      HasDerivAt (fun s ↦ V s μ) (f (V t μ) - μ • V t μ) t)
    (hq : Continuous q) (hqinj : Function.Injective q) (hUzero : EqOn (fun t ↦ U t 0) q (Icc 0 L))
    (hVzero : EqOn (fun t ↦ V t 0) q (Icc 0 L)) (hO : IsOpen O) (htStar : tStar ∈ O)
    (hOdomain : O ⊆ Ioo lo hi) (hOanchors : O ⊆ Ioo 0 L) (hΩ : IsOpen Ω) (hqΩ : q tStar ∈ Ω)
    (hframe : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → ContDiff ℝ ∞ (blendedStrip U V θ) ∧
      EqOn (fun t ↦ blendedStrip U V θ (t, 0)) q O ∧ ∀ t ∈ O,
      HasFDerivAt (fun z : (ℝ × ℝ) × ℝ ↦ blendedStrip U V θ z.1 + z.2 • ν)
      (stripDifferential (f (q t)) (W t + phaseSlope • f (q t)) ν) ((t, 0), 0) ∧
      Matrix.det ![⇑(f (q t)), ⇑(W t + phaseSlope • f (q t)), ⇑ν] =
      -Matrix.det ![⇑(f (q t)), ⇑ν, ⇑(W t)] ∧ ∃ M : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ℝ^3,
      (M : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ^3) = stripDifferential (f (q t)) (W t + phaseSlope • f (q t)) ν) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < L ∧
      ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧
        (∀ t ≤ a, θ =ᶠ[𝓝 t] (fun _ ↦ 0)) ∧
        (∀ t, b ≤ t → θ =ᶠ[𝓝 t] (fun _ ↦ 1)) ∧
        ∀ εcap : ℝ, 0 < εcap → ∀ η : ℝ, 0 < η →
          ∃ (P : ℝ^3 → ℝ^3) (ε r d : ℝ),
            ContDiff ℝ ∞ P ∧ HasCompactSupport P ∧ tsupport P ⊆ Ω ∧
            (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P x‖ < η) ∧
            (∀ t ∈ Icc a b, ∀ n ≤ 2, iteratedFDeriv ℝ n P (q t) = 0) ∧
            (∀ x, IsStrictlyHyperbolicAt (f + P) x) ∧
            (∀ i, IsGenuinelyNonlinearFamily (f + P) i) ∧
            0 < ε ∧ ε < εcap ∧ 0 < r ∧ r ≤ ε ∧ 0 < d ∧
            ∀ μ : ℝ, |μ| ≤ r →
              (∀ t ∈ Icc (-d) a, P (U t μ) = 0) ∧
              (∀ t ∈ Icc b (L + d), P (V t μ) = 0) ∧
              ∀ t ∈ Icc a b,
                HasDerivAt (fun s ↦ blendedStrip U V θ (s, μ))
                  ((f + P) (blendedStrip U V θ (t, μ)) -
                    μ • blendedStrip U V θ (t, μ)) t := by
  classical
  obtain ⟨a, b, htInner, hKO, _, hrealize⟩ :=
    exists_actual_strip_far_support_realization_of_rank_frame
      hf hhyper hgn hU hV hC hJ hzero hcubic hode hq
      (fun _ _ _ _ h ↦ hqinj h) hO htStar hOdomain hΩ hqΩ hframe
  have hab : a < b := htInner.1.trans htInner.2
  have ha : 0 < a := (hOanchors (hKO ⟨le_rfl, hab.le⟩)).1
  have hb : b < L := (hOanchors (hKO ⟨hab.le, le_rfl⟩)).2
  obtain ⟨θ, hθ, hθleft, hθright⟩ := exists_smooth_transition_with_outer_collars hab
  let w := blendedStrip U V θ
  obtain ⟨chart, coord, T, N, ρ, B, R, _, _, _, _, _, _, _, _, _, _, _, hT, hKT, _, hρ, hTdomain,
      _, hrecover, _, _, _, _, _, hresidual, hfarRealize⟩ := hrealize θ hθ
  -- The time endpoints here are the unshifted anchors. No negative base time is used.
  let D : Set ℝ := (Icc 0 a \ T) ∪ (Icc b L \ T)
  have hD : IsCompact D := (isCompact_Icc.diff hT).union (isCompact_Icc.diff hT)
  have hKD : Disjoint (Icc a b) D := Set.disjoint_left.mpr fun t ht hfar ↦ by
    rcases hfar with hout | hin
    exacts [hout.2 (hKT ht), hin.2 (hKT ht)]
  obtain ⟨_, _, rA, A, _, _, _, _, _, _, _, _, _, _, _, hcorrection⟩ :=
    hfarRealize D hD hKD fun _ _ _ _ h ↦ hqinj h
  have hrecoverFirst : ∀ t ∈ T, ∀ μ ∈ Icc (-ρ) ρ, (coord (w (t, μ))).1 = (t, μ) :=
    fun t ht μ hμ ↦ by
      simpa only [zero_smul, add_zero] using
        congrArg Prod.fst (hrecover t ht μ hμ 0 ⟨neg_nonpos.mpr hρ.le, hρ.le⟩)
  refine ⟨a, b, ha, hab, hb, θ, hθ, hθleft, hθright, fun εcap hcap η hη ↦ ?_⟩
  obtain ⟨ε, P, hε, hεcap, _, _, hP, hPc, _, hPΩ, hPfar,
      _, hRzero, hsmall, _, hbaseJets, _, hmiddle, hhyperP, hgnP⟩ := hcorrection εcap hcap η hη
  obtain ⟨d, r₀, hd, hr₀, _, houter⟩ :=
    PDE.Analysis.exists_outer_envelope_zeros_of_chart_and_far_support
      hU.continuous hV.continuous ha.le hb.le hT hρ
      (fun t ht ↦ hUzero ⟨ht.1, ht.2.trans (hab.le.trans hb.le)⟩)
      (fun t ht ↦ hVzero ⟨(ha.le.trans hab.le).trans ht.1, ht.2⟩) hPfar
      hθleft hθright hTdomain hrecoverFirst hresidual hRzero
  refine ⟨P, ε, min ε r₀, d, hP, hPc, hPΩ, hsmall, hbaseJets, hhyperP, hgnP,
    hε, hεcap, lt_min hε hr₀, min_le_left _ _, hd, fun μ hμ ↦ ?_⟩
  obtain ⟨hout, hin⟩ := houter μ (hμ.trans (min_le_right _ _))
  exact ⟨hout, hin, fun t ht ↦ hmiddle t ht μ (hμ.trans (min_le_left _ _))⟩

end PDE.Hyperbolic.ConservationLaw.System
