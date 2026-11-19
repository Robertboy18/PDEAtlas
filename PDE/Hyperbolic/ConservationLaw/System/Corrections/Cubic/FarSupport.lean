/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Cubic.StripAmplitude
public import PDE.Analysis.ODE.Interpolation.Strip.Rank
public import PDE.Analysis.ODE.Interpolation.Support.Avoidance
public import PDE.Hyperbolic.ConservationLaw.System.Corrections.Cubic.Realization

import PDE.Analysis.ODE.Interpolation.CubicResidual

/-!
# Realizing a strip away from a prescribed far base segment

The time interval is chosen before the transition. Its chart, compact coordinate,
valid time neighborhood and cubic residual are then fixed before a far time set
is supplied. Injectivity of the base curve separates the two compact time sets
in state space. Restricting the permitted amplitude neighborhood to the complement
of the far image makes that separation a property of the amplitude's support.

Only after this restriction and a uniform strip-width choice is the amplitude
constructed. It precedes every scale cap and tolerance. The same correction has
small jets through order two everywhere, preserves all characteristic families,
and preserves every zero of the coordinate residual, including outside the strip.

Chart recovery is used only on its box, and residual identities only on
the original common ODE domain.
-/

@[expose] public noncomputable section

open Function Set
open PDE.Analysis.ODE.StripRank
open scoped ContDiff Matrix Topology

namespace PDE.Hyperbolic.ConservationLaw.System

/-- Construct the strip correction with its amplitude supported away from
any later prescribed compact far-time image. The frame hypothesis is the conclusion of
`exists_selected_actual_strip_rank_arc`.

The order of witnesses is significant: the compact interval precedes `θ`; the
chart, coordinate, open time set and residual precede `D`; and the restricted
amplitude precedes every cap and tolerance. Injectivity on `Icc a b ∪ D` and
separation of the time sets imply the support exclusion, rather than assuming it.

The returned open time set lies in the original ODE time interval, with one
signed speed width inside the original parameter neighborhood. Thus it can also
be used for later constant-cutoff collars outside `Icc a b`. -/
theorem exists_actual_strip_far_support_realization_of_rank_frame {f : ℝ^3 → ℝ^3} {q W : ℝ → ℝ^3}
    {ν : ℝ^3} {α : ℝ} {U V : ℝ → ℝ → ℝ^3} {C : ℝ × ℝ → ℝ^3} {lo hi tStar : ℝ} {J O : Set ℝ}
    {Ω : Set (ℝ^3)} (hf : ContDiff ℝ ∞ f) (hhyper : ∀ x, IsStrictlyHyperbolicAt f x)
    (hgn : ∀ i, IsGenuinelyNonlinearFamily f i) (hU : ContDiff ℝ ∞ U.uncurry)
    (hV : ContDiff ℝ ∞ V.uncurry) (hC : ContDiff ℝ ∞ C) (hJ : IsOpen J) (hzero : (0 : ℝ) ∈ J)
    (hcubic : ∀ t ∈ Icc lo hi, ∀ μ ∈ J, V t μ - U t μ = μ ^ 3 • C (t, μ))
    (hode : ∀ t ∈ Icc lo hi, ∀ μ ∈ J, HasDerivAt (fun s ↦ U s μ) (f (U t μ) - μ • U t μ) t ∧
      HasDerivAt (fun s ↦ V s μ) (f (V t μ) - μ • V t μ) t)
    (hq : Continuous q) (hqinj : InjOn q O) (hO : IsOpen O) (htStar : tStar ∈ O)
    (hOdomain : O ⊆ Ioo lo hi) (hΩ : IsOpen Ω) (hqΩ : q tStar ∈ Ω)
    (hframe : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → ContDiff ℝ ∞ (blendedStrip U V θ) ∧
      EqOn (fun t ↦ blendedStrip U V θ (t, 0)) q O ∧ ∀ t ∈ O,
      HasFDerivAt (fun z : (ℝ × ℝ) × ℝ ↦ blendedStrip U V θ z.1 + z.2 • ν)
      (stripDifferential (f (q t)) (W t + α • f (q t)) ν) ((t, 0), 0) ∧
      Matrix.det ![⇑(f (q t)), ⇑(W t + α • f (q t)), ⇑ν] = -Matrix.det ![⇑(f (q t)), ⇑ν, ⇑(W t)] ∧
      ∃ L : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ℝ^3, (L : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ^3) =
      stripDifferential (f (q t)) (W t + α • f (q t)) ν) :
    ∃ a b : ℝ, tStar ∈ Ioo a b ∧ Icc a b ⊆ O ∧ MapsTo q (Icc a b) Ω ∧
      ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ →
        let w := blendedStrip U V θ
        let domain := Ioo lo hi ×ˢ J
        ∃ (chart : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) (ℝ^3))
          (coord : ℝ^3 → (ℝ × ℝ) × ℝ) (T : Set ℝ) (N : Set (ℝ^3))
          (ρ B : ℝ) (R : ℝ × ℝ → ℝ^3),
          (chart : ((ℝ × ℝ) × ℝ) → ℝ^3) = (fun p ↦ w p.1 + p.2 • ν) ∧
          ContDiffOn ℝ ∞ chart chart.source ∧
          ContDiffOn ℝ ∞ chart.symm chart.target ∧ chart.target ⊆ Ω ∧
          ContDiff ℝ ∞ coord ∧ HasCompactSupport coord ∧
          tsupport coord ⊆ chart.target ∧
          IsOpen N ∧ MapsTo (fun t ↦ w (t, 0)) (Icc a b) N ∧
          N ⊆ chart.target ∧ EqOn coord chart.symm N ∧
          IsOpen T ∧ Icc a b ⊆ T ∧ T ⊆ Ioo lo hi ∧ 0 < ρ ∧
          T ×ˢ Icc (-ρ) ρ ⊆ domain ∧
          ((T ×ˢ Icc (-ρ) ρ) ×ˢ Icc (-ρ) ρ) ⊆ chart.source ∩
            (fun p : (ℝ × ℝ) × ℝ ↦ w p.1 + p.2 • ν) ⁻¹' N ∧
          (∀ t ∈ T, ∀ μ ∈ Icc (-ρ) ρ, ∀ n ∈ Icc (-ρ) ρ,
            coord (w (t, μ) + n • ν) = ((t, μ), n)) ∧
          (∀ x ∈ N, w (coord x).1 + (coord x).2 • ν = x) ∧
          1 ≤ B ∧ (∀ i : ℕ, i ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ i coord x‖ ≤ B) ∧
          ContDiffOn ℝ ∞ R domain ∧
          (∀ p ∈ domain, HasDerivAt (fun t ↦ w (t, p.2))
            (f (w p) - p.2 • w p + p.2 ^ 3 • R p) p.1) ∧
          (∀ p ∈ domain, (θ p.1 = 0 ∨ θ p.1 = 1) → deriv θ p.1 = 0 → R p = 0) ∧
          ∀ D : Set ℝ, IsCompact D → Disjoint (Icc a b) D → InjOn q (Icc a b ∪ D) →
            let Nfar := N ∩ (q '' D)ᶜ
            IsOpen Nfar ∧ MapsTo (fun t ↦ w (t, 0)) (Icc a b) Nfar ∧
              ∃ (r : ℝ) (A : ℝ^3 → ℝ^3),
                0 < r ∧ r ≤ ρ ∧ Icc a b ×ˢ Icc (-r) r ⊆ domain ∧
                MapsTo w (Icc a b ×ˢ Icc (-r) r) Nfar ∧
                (∀ p ∈ Icc a b ×ˢ Icc (-r) r, coord (w p) = (p, 0)) ∧
                ContDiff ℝ ∞ A ∧ HasCompactSupport A ∧
                tsupport A ⊆ Nfar ∩ (fun x ↦ (coord x).1) ⁻¹' domain ∧
                Disjoint (tsupport A) (q '' D) ∧
                (∀ p ∈ Icc a b ×ˢ Icc (-r) r, A (w p) = R p) ∧
                (∀ x, R ((coord x).1) = 0 → A x = 0) ∧
                ∀ εcap : ℝ, 0 < εcap → ∀ η : ℝ, 0 < η →
                  ∃ (ε : ℝ) (P₂ : ℝ^3 → ℝ^3),
                    0 < ε ∧ ε < εcap ∧ ε < r ∧ ε ≤ 1 ∧
                    ContDiff ℝ ∞ P₂ ∧ HasCompactSupport P₂ ∧
                    tsupport P₂ ⊆ tsupport A ∩ {x | |(coord x).1.2| ≤ 2 * ε} ∧
                    tsupport P₂ ⊆ Ω ∧ Disjoint (tsupport P₂) (q '' D) ∧
                    (∀ x, A x = 0 → P₂ x = 0) ∧
                    (∀ x, R ((coord x).1) = 0 → P₂ x = 0) ∧
                    (∀ n ≤ 2, ∀ x, ‖iteratedFDeriv ℝ n P₂ x‖ < η) ∧
                    (∀ x, (coord x).1.2 = 0 →
                      ∀ n ≤ 2, iteratedFDeriv ℝ n P₂ x = 0) ∧
                    (∀ t ∈ Icc a b, ∀ n ≤ 2, iteratedFDeriv ℝ n P₂ (q t) = 0) ∧
                    (∀ t ∈ Icc a b, ∀ μ : ℝ, |μ| ≤ ε →
                      P₂ (w (t, μ)) = μ ^ 3 • R (t, μ)) ∧
                    (∀ t ∈ Icc a b, ∀ μ : ℝ, |μ| ≤ ε →
                      HasDerivAt (fun s ↦ w (s, μ))
                        ((f + P₂) (w (t, μ)) - μ • w (t, μ)) t) ∧
                    (∀ x, IsStrictlyHyperbolicAt (f + P₂) x) ∧
                    ∀ i, IsGenuinelyNonlinearFamily (f + P₂) i := by
  obtain ⟨a, b, _, hab, hcompact⟩ := exists_Icc_mem_subset_of_mem_nhds
    ((hO.inter (hΩ.preimage hq)).mem_nhds ⟨htStar, hqΩ⟩)
  have htInner : tStar ∈ Ioo a b := Icc_mem_nhds_iff.mp hab
  have hKO : Icc a b ⊆ O := fun t ht ↦ (hcompact ht).1
  refine ⟨a, b, htInner, hKO, fun t ht ↦ (hcompact ht).2, fun θ hθ ↦ ?_⟩
  intro w domain
  obtain ⟨hw, hwbase, hcolumns⟩ := hframe θ hθ
  have hD : ∀ t ∈ Icc a b, ∃ L : ((ℝ × ℝ) × ℝ) ≃L[ℝ] ℝ^3,
      HasFDerivAt (fun p : (ℝ × ℝ) × ℝ ↦ w p.1 + p.2 • ν)
        (L : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ^3) ((t, 0), 0) := fun t ht ↦ by
    obtain ⟨hderiv, -, L, hL⟩ := hcolumns t (hKO ht)
    exact ⟨L, hL ▸ hderiv⟩
  obtain ⟨chart, coord, T₀, N, ρ₀, B, hchart, hchartSmooth, hinverse, htarget,
      hcoord, hcoordc, hcoordsupport, hN, hbaseN, hNtarget, hagree,
      hT₀, hKT₀, hρ₀, hbox₀, hrecover₀, hright, hB, hbound⟩ :=
    PDE.Analysis.exists_smooth_compact_strip_state_chart hw isCompact_Icc
      (fun s hs t ht hst ↦ hqinj (hKO hs) (hKO ht)
        ((hwbase (hKO hs)).symm.trans (hst.trans (hwbase (hKO ht))))) ν hD hΩ
      (fun t ht ↦ by rw [hwbase (hKO ht)]; exact (hcompact ht).2)
  -- Keep a chart time neighborhood on which the residual is defined.
  have hdomain : IsOpen domain := isOpen_Ioo.prod hJ
  obtain ⟨ρ, hρ, hρbound, hKdomain⟩ := PDE.Analysis.exists_pos_strip_width_in_open_domain
      isCompact_Icc hdomain (fun t ht ↦ ⟨hOdomain (hKO ht), hzero⟩) ρ₀ hρ₀
  let T : Set ℝ := T₀ ∩ Ioo lo hi
  have hKT : Icc a b ⊆ T := fun t ht ↦ ⟨hKT₀ ht, hOdomain (hKO ht)⟩
  have hTdomain : T ×ˢ Icc (-ρ) ρ ⊆ domain := fun p hp ↦ ⟨hp.1.2, (hKdomain
    (show (tStar, p.2) ∈ Icc a b ×ˢ Icc (-ρ) ρ from ⟨Ioo_subset_Icc_self htInner, hp.2⟩)).2⟩
  have hρsub : Icc (-ρ) ρ ⊆ Icc (-ρ₀) ρ₀ := Icc_subset_Icc (neg_le_neg hρbound) hρbound
  have hbox : ((T ×ˢ Icc (-ρ) ρ) ×ˢ Icc (-ρ) ρ) ⊆ chart.source ∩
      (fun p : (ℝ × ℝ) × ℝ ↦ w p.1 + p.2 • ν) ⁻¹' N := fun p hp ↦
    hbox₀ ⟨⟨hp.1.1.1, hρsub hp.1.2⟩, hρsub hp.2⟩
  have hrecover : ∀ t ∈ T, ∀ μ ∈ Icc (-ρ) ρ, ∀ n ∈ Icc (-ρ) ρ,
      coord (w (t, μ) + n • ν) = ((t, μ), n) :=
    fun t ht μ hμ n hn ↦ hrecover₀ t ht.1 μ (hρsub hμ) n (hρsub hn)
  -- The residual depends on the fixed strips and transition, not on the far set.
  obtain ⟨R, hR, hresidual, hcollar⟩ :=
    PDE.Analysis.ODE.exists_contDiffOn_cubic_interpolation_residual
      hf hU.contDiffOn hV.contDiffOn hC.contDiffOn hθ
      (fun p (hp : p ∈ domain) ↦ hcubic p.1 (Ioo_subset_Icc_self hp.1) p.2 hp.2)
      (fun p (hp : p ∈ domain) ↦ (hode p.1 (Ioo_subset_Icc_self hp.1) p.2 hp.2).1)
      (fun p (hp : p ∈ domain) ↦ (hode p.1 (Ioo_subset_Icc_self hp.1) p.2 hp.2).2)
  have hresidualW : ∀ p ∈ domain, HasDerivAt (fun t ↦ w (t, p.2))
      (f (w p) - p.2 • w p + p.2 ^ 3 • R p) p.1 := hresidual
  refine ⟨chart, coord, T, N, ρ, B, R,
    hchart, hchartSmooth, hinverse, htarget, hcoord, hcoordc, hcoordsupport,
    hN, hbaseN, hNtarget, hagree, hT₀.inter isOpen_Ioo, hKT, inter_subset_right, hρ, hTdomain,
    hbox, hrecover, hright, hB, hbound, hR, hresidualW, hcollar, ?_⟩
  intro D hDcompact hdisjoint hinj Nfar
  -- Separate the compact far image before asking the realization theorem for A.
  obtain ⟨Tfar, rFar, _, hKTfar, hrFar, havoid⟩ :=
    PDE.Analysis.exists_uniform_strip_avoiding_far_base_image
      hq hw.continuous isCompact_Icc hDcompact hinj hdisjoint (fun t ht ↦ hwbase (hKO ht))
  have hNfar : IsOpen Nfar := hN.inter (hDcompact.image hq).isClosed.isOpen_compl
  let r : ℝ := min ρ rFar
  have hr : 0 < r := lt_min hρ hrFar
  have hspeed : Icc (-r) r ⊆ Icc (-ρ) ρ :=
    Icc_subset_Icc (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hzeroρ : (0 : ℝ) ∈ Icc (-ρ) ρ := ⟨neg_nonpos.mpr hρ.le, hρ.le⟩
  have hrectangle : Icc a b ×ˢ Icc (-r) r ⊆ domain := fun p hp ↦ hTdomain ⟨hKT hp.1, hspeed hp.2⟩
  have hstate : MapsTo w (Icc a b ×ˢ Icc (-r) r) Nfar := by
    rintro ⟨t, μ⟩ ⟨ht, hμ⟩
    have hmem : w (t, μ) + (0 : ℝ) • ν ∈ N := (hbox (show ((t, μ), (0 : ℝ)) ∈
      ((T ×ˢ Icc (-ρ) ρ) ×ˢ Icc (-ρ) ρ) from ⟨⟨hKT ht, hspeed hμ⟩, hzeroρ⟩)).2
    exact ⟨by simpa only [zero_smul, add_zero] using hmem,
      havoid t (hKTfar ht) μ ((abs_le.mpr hμ).trans (min_le_right _ _))⟩
  have hrecoverStrip : ∀ p ∈ Icc a b ×ˢ Icc (-r) r, coord (w p) = (p, 0) := by
    rintro ⟨t, μ⟩ ⟨ht, hμ⟩
    simpa only [zero_smul, add_zero] using hrecover t (hKT ht) μ (hspeed hμ) 0 hzeroρ
  obtain ⟨A, hA, hAc, hAsupport, hAstrip, hAzero, hcorrection⟩ :=
    exists_state_cubic_residual_realization_preserving_zeros
      hf hhyper hgn hw isCompact_Icc hcoord hcoordc
      hNfar hdomain hr hstate hrectangle hrecoverStrip hR hresidualW
  have hAfar : Disjoint (tsupport A) (q '' D) :=
    Set.disjoint_left.mpr fun x hxA hxD ↦ (hAsupport hxA).1.2 hxD
  refine ⟨hNfar, fun t ht ↦ ⟨hbaseN ht, havoid t (hKTfar ht) 0 (abs_zero.trans_le hrFar.le)⟩,
    r, A, hr, min_le_left _ _, hrectangle, hstate, hrecoverStrip,
    hA, hAc, hAsupport, hAfar, hAstrip, hAzero, fun εcap hcap η hη ↦ ?_⟩
  obtain ⟨ε, P₂, hε, hεcap, hεr, hεone, hP, hPc, hsupport,
      hPzero, hRzero, hsmall, hvanish, hexact, hcorrected, hhyperP, hgnP⟩ :=
    hcorrection εcap hcap η hη
  refine ⟨ε, P₂, hε, hεcap, hεr, hεone, hP, hPc, hsupport,
    fun x hx ↦ htarget (hNtarget (hAsupport (hsupport hx).1).1.1),
    hAfar.mono_left (hsupport.trans inter_subset_left), hPzero, hRzero, hsmall, hvanish,
    fun t ht ↦ hvanish (q t) ?_, hexact, hcorrected, hhyperP, hgnP⟩
  rw [← hwbase (hKO ht)]
  exact congrArg (·.1.2) (hrecoverStrip (t, 0) ⟨ht, neg_nonpos.mpr hr.le, hr.le⟩)

end PDE.Hyperbolic.ConservationLaw.System
