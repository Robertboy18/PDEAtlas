/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.ODE.Interpolation.PhaseCore
public import PDE.Analysis.ODE.Interpolation.Strip.Rank
public import PDE.Analysis.ODE.Interpolation.Support.Avoidance

import PDE.Analysis.Integration.BumpMoments.NormalizedPulse.Transition

/-!
# Outer envelopes and moving phase anchors

A smooth transition has constant collars on both outer branches. Inside the
coordinate chart, those collars make the residual vanish. Away from the chart,
compactness supplies a common speed interval on which the branches avoid the
fixed correction's support. The resulting time envelopes extend beyond the
original anchors using continuity alone.

The phase lemmas use these fixed envelopes to recover the original anchor
values and glue the three pieces. The differential equations remain restricted
to the supplied common time interval throughout.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

/-- Put the transition strictly inside the chosen interval. Its two constant
collars include the endpoints and extend to the corresponding half-lines. -/
theorem exists_smooth_transition_with_outer_collars {a b : ℝ} (hab : a < b) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧
      (∀ t ≤ a, θ =ᶠ[𝓝 t] (fun _ ↦ 0)) ∧
      ∀ t, b ≤ t → θ =ᶠ[𝓝 t] (fun _ ↦ 1) := by
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  obtain ⟨d, hcd, hdb⟩ := exists_between hcb
  have hdc : 0 < d - c := sub_pos.mpr hcd
  let θ : ℝ → ℝ := fun t ↦ NormalizedPulse.transition ((t - c) / (d - c))
  have hθ : ContDiff ℝ ∞ θ :=
    NormalizedPulse.contDiff_transition.comp
      ((contDiff_id.sub contDiff_const).div_const (d - c))
  refine ⟨θ, hθ, ?_, ?_⟩
  · intro t ht
    filter_upwards [isOpen_Iio.mem_nhds (ht.trans_lt hac)] with s hs
    apply NormalizedPulse.transition_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.le) hdc.le
  · intro t ht
    filter_upwards [isOpen_Ioi.mem_nhds (hdb.trans_le ht)] with s hs
    apply NormalizedPulse.transition_of_one_le
    exact (one_le_div hdc).mpr (sub_le_sub_right hs.le c)

/-- Zero-speed phase translations recover the base on the retained closed
interval, including its endpoints. There is no assertion outside that interval. -/
theorem phase_base_eqOn_retained_interval
    {E : Type*} {F U : ℝ → ℝ → E} {q : ℝ → E} {τ : ℝ → ℝ}
    {e lo hi : ℝ} {J : Set ℝ} (hzero : (0 : ℝ) ∈ J) (hτzero : τ 0 = e)
    (hphase : ∀ μ ∈ J, ∀ t, U t μ = F (t + τ μ - e) μ)
    (hbase : EqOn (fun t ↦ F t 0) q (Icc lo hi)) :
    EqOn (fun t ↦ U t 0) q (Icc lo hi) := by
  intro t ht
  change U t 0 = q t
  rw [hphase 0 hzero t, hτzero, add_sub_cancel_right]
  exact hbase ht

end PDE.Analysis.ODE

namespace PDE.Analysis

open PDE.Analysis.ODE.StripRank

/-- From the actual chart and a fixed correction's far-support separation,
obtain slightly larger time envelopes. Base identities are used only on the
original closed intervals. Outside those intervals, continuity gives avoidance;
no differential equation or base identity is inferred there.

The actual realization consumer supplies this far-support hypothesis for its
chosen correction. Here the correction and its support separation are fixed
before the common speed radius is chosen. -/
theorem exists_outer_envelope_zeros_of_chart_and_far_support
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : ℝ → ℝ → E} {q : ℝ → E} {P : E → E}
    {coord : E → (ℝ × ℝ) × ℝ} {R : ℝ × ℝ → E} {θ : ℝ → ℝ}
    {a b L ρ : ℝ} {T : Set ℝ} {domain : Set (ℝ × ℝ)}
    (hU : Continuous U.uncurry) (hV : Continuous V.uncurry)
    (ha : 0 ≤ a) (hb : b ≤ L) (hT : IsOpen T) (hρ : 0 < ρ)
    (hUzero : EqOn (fun t ↦ U t 0) q (Icc 0 a))
    (hVzero : EqOn (fun t ↦ V t 0) q (Icc b L))
    (hfar : Disjoint (tsupport P) (q '' ((Icc 0 a \ T) ∪ (Icc b L \ T))))
    (hθleft : ∀ t ≤ a, θ =ᶠ[𝓝 t] (fun _ ↦ 0))
    (hθright : ∀ t, b ≤ t → θ =ᶠ[𝓝 t] (fun _ ↦ 1))
    (hTdomain : T ×ˢ Icc (-ρ) ρ ⊆ domain)
    (hrecover : ∀ t ∈ T, ∀ μ ∈ Icc (-ρ) ρ,
      (coord (blendedStrip U V θ (t, μ))).1 = (t, μ))
    (hresidual : ∀ p ∈ domain,
      (θ p.1 = 0 ∨ θ p.1 = 1) → deriv θ p.1 = 0 → R p = 0)
    (hzero : ∀ x, R (coord x).1 = 0 → P x = 0) :
    ∃ d r : ℝ, 0 < d ∧ 0 < r ∧ r ≤ ρ ∧ ∀ μ : ℝ, |μ| ≤ r →
      (∀ t ∈ Icc (-d) a, P (U t μ) = 0) ∧
      ∀ t ∈ Icc b (L + d), P (V t μ) = 0 := by
  classical
  have hbaseLeft : ∀ t ∈ Icc 0 a \ T, U t 0 ∉ tsupport P := fun t ht hx ↦
    Set.disjoint_left.mp hfar hx ⟨t, Or.inl ht, (hUzero ht.1).symm⟩
  have hbaseRight : ∀ t ∈ Icc b L \ T, V t 0 ∉ tsupport P := fun t ht hx ↦
    Set.disjoint_left.mp hfar hx ⟨t, Or.inr ht, (hVzero ht.1).symm⟩
  obtain ⟨Tout, rout, hTout, hfarOut, hrout, havoidOut⟩ :=
    exists_uniform_avoidance_of_compact_zero_section hU
      (isCompact_Icc.diff hT) (isClosed_tsupport P) hbaseLeft
  obtain ⟨Tin, rin, hTin, hfarIn, hrin, havoidIn⟩ :=
    exists_uniform_avoidance_of_compact_zero_section hV
      (isCompact_Icc.diff hT) (isClosed_tsupport P) hbaseRight
  have hcoverOut : Icc 0 a ⊆ T ∪ Tout := fun t ht ↦
    (em (t ∈ T)).imp_right fun h ↦ hfarOut ⟨ht, h⟩
  have hcoverIn : Icc b L ⊆ T ∪ Tin := fun t ht ↦
    (em (t ∈ T)).imp_right fun h ↦ hfarIn ⟨ht, h⟩
  -- These balls come from open time covers, not from extended base equations.
  obtain ⟨dout, hdout, hballOut⟩ :
      ∃ d : ℝ, 0 < d ∧ Metric.closedBall (0 : ℝ) d ⊆ T ∪ Tout :=
    Metric.nhds_basis_closedBall.mem_iff.mp
      ((hT.union hTout).mem_nhds (hcoverOut ⟨le_rfl, ha⟩))
  obtain ⟨din, hdin, hballIn⟩ :
      ∃ d : ℝ, 0 < d ∧ Metric.closedBall L d ⊆ T ∪ Tin :=
    Metric.nhds_basis_closedBall.mem_iff.mp
      ((hT.union hTin).mem_nhds (hcoverIn ⟨hb, le_rfl⟩))
  let d := min dout din
  let r := min ρ (min rout rin)
  have hdout' : d ≤ dout := min_le_left _ _
  have hdin' : d ≤ din := min_le_right _ _
  have hrρ : r ≤ ρ := min_le_left _ _
  have hleftCover : Icc (-d) a ⊆ T ∪ Tout := fun t ht ↦ by
    by_cases ht0 : 0 ≤ t
    · exact hcoverOut ⟨ht0, ht.2⟩
    · refine hballOut ?_
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      constructor <;> linarith [ht.1]
  have hrightCover : Icc b (L + d) ⊆ T ∪ Tin := fun t ht ↦ by
    by_cases htL : t ≤ L
    · exact hcoverIn ⟨ht.1, htL⟩
    · refine hballIn ?_
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      constructor <;> linarith [ht.2]
  refine ⟨d, r, lt_min hdout hdin, lt_min hρ (lt_min hrout hrin), hrρ, fun μ hμ ↦ ?_⟩
  have hμρ : μ ∈ Icc (-ρ) ρ := abs_le.mp (hμ.trans hrρ)
  have hchartZero (t : ℝ) (ht : t ∈ T) (c : ℝ)
      (hflat : θ =ᶠ[𝓝 t] (fun _ ↦ c)) (hc : c = 0 ∨ c = 1) :
      P (blendedStrip U V θ (t, μ)) = 0 := by
    refine hzero _ ?_
    rw [hrecover t ht μ hμρ]
    exact hresidual (t, μ) (hTdomain ⟨ht, hμρ⟩) (by rwa [hflat.self_of_nhds])
      (by simpa only [deriv_const] using hflat.deriv_eq)
  constructor
  · intro t ht
    rcases hleftCover ht with hchart | hfarTime
    · simpa only [blendedStrip, (hθleft t ht.2).self_of_nhds, zero_smul, add_zero] using
        hchartZero t hchart 0 (hθleft t ht.2) (Or.inl rfl)
    · exact image_eq_zero_of_notMem_tsupport
        (havoidOut t hfarTime μ (hμ.trans ((min_le_right _ _).trans (min_le_left _ _))))
  · intro t ht
    rcases hrightCover ht with hchart | hfarTime
    · simpa only [blendedStrip, (hθright t ht.1).self_of_nhds, one_smul, add_sub_cancel] using
        hchartZero t hchart 1 (hθright t ht.1) (Or.inr rfl)
    · exact image_eq_zero_of_notMem_tsupport
        (havoidIn t hfarTime μ (hμ.trans ((min_le_right _ _).trans (min_le_right _ _))))

end PDE.Analysis

namespace PDE.Analysis.ODE

open PDE.Analysis.ODE.StripRank

/-- Apply the fixed outer envelopes to the actual moving phase anchors, then
reuse the existing finite-interval gluing theorem. The ODE is used only at times
translated into `[lo,hi]`; the enlarged raw envelopes carry only zero values of
`P`. The state function `P` is fixed before the common signed speed radius. -/
theorem exists_phase_core_of_fixed_outer_envelopes
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f P : E → E} {F G U V : ℝ → ℝ → E} {θ τout τin : ℝ → ℝ}
    {J : Set ℝ} {a b e lo hi d r₀ : ℝ}
    (hab : a < b) (hlo : lo ≤ 0) (hhi : e + e ≤ hi)
    (ha : a ∈ Ioo (0 : ℝ) hi) (hb : b ∈ Ioo lo (e + e))
    (hd : 0 < d) (hr₀ : 0 < r₀) (hJ : J ∈ 𝓝 (0 : ℝ))
    (hτout : ContinuousAt τout 0) (hτin : ContinuousAt τin 0)
    (hτoutZero : τout 0 = e) (hτinZero : τin 0 = e)
    (hF : ∀ μ ∈ J, ∀ t ∈ Icc lo hi,
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (hG : ∀ μ ∈ J, ∀ t ∈ Icc lo hi,
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) - μ • G t μ) t)
    (hU : ∀ μ ∈ J, ∀ t, U t μ = F (t + τout μ - e) μ)
    (hV : ∀ μ ∈ J, ∀ t, V t μ = G (t + τin μ - e) μ)
    (hθa : θ a = 0) (hθb : θ b = 1)
    (houter : ∀ μ : ℝ, |μ| ≤ r₀ →
      (∀ t ∈ Icc (-d) a, P (U t μ) = 0) ∧
      ∀ t ∈ Icc b (e + e + d), P (V t μ) = 0)
    (hmiddle : ∀ μ : ℝ, |μ| ≤ r₀ → ∀ t ∈ Icc a b,
      HasDerivAt (fun s ↦ blendedStrip U V θ (s, μ))
        ((f + P) (blendedStrip U V θ (t, μ)) -
          μ • blendedStrip U V θ (t, μ)) t) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r₀ ∧ ∀ μ : ℝ, |μ| ≤ r →
      μ ∈ J ∧
      let α := τout μ - e
      let β := τin μ - e
      (∀ t ∈ Icc (-α) a, P (U t μ) = 0) ∧
      (∀ t ∈ Icc b (e + e - β), P (V t μ) = 0) ∧
      -α < a ∧ b < e + e - β ∧
      ∃ u : ℝ → E,
        EqOn u (fun t ↦ U t μ) (Icc (-α) a) ∧
        EqOn u (fun t ↦ blendedStrip U V θ (t, μ)) (Icc a b) ∧
        EqOn u (fun t ↦ V t μ) (Icc b (e + e - β)) ∧
        u (-α) = F 0 μ ∧ u (e + e - β) = G (e + e) μ ∧
        ∀ t ∈ Icc (-α) (e + e - β),
          HasDerivWithinAt u ((f + P) (u t) - μ • u t)
            (Icc (-α) (e + e - β)) t := by
  obtain ⟨rphase, hrphase, hphase⟩ := exists_pos_phase_anchor_radius
    hτout hτin hτoutZero hτinZero hJ ha hb hd
  refine ⟨min r₀ rphase, lt_min hr₀ hrphase, min_le_left _ _, fun μ hμ ↦ ?_⟩
  have hμ₀ : |μ| ≤ r₀ := hμ.trans (min_le_left _ _)
  obtain ⟨hμJ, hjoinOut, hjoinIn, houtSmall, hinSmall⟩ :=
    hphase μ (hμ.trans (min_le_right _ _))
  obtain ⟨hout, hin⟩ := houter μ hμ₀
  let α := τout μ - e
  let β := τin μ - e
  have hleft : ∀ t ∈ Icc (-α) a, P (U t μ) = 0 := fun t ht ↦
    hout t ⟨(neg_le_neg (abs_lt.mp houtSmall).2.le).trans ht.1, ht.2⟩
  have hright : ∀ t ∈ Icc b (e + e - β), P (V t μ) = 0 := fun t ht ↦
    hin t ⟨ht.1, by linarith [ht.2, (abs_lt.mp hinSmall).1]⟩
  refine ⟨hμJ, hleft, hright, ?_⟩
  exact exists_core_of_phase_interpolation hab hlo hhi hjoinOut hjoinIn
    (hF μ hμJ) (hG μ hμJ)
    (fun t ↦ by simpa only [add_sub_assoc] using hU μ hμJ t)
    (fun t ↦ by simpa only [add_sub_assoc] using hV μ hμJ t)
    (fun _ ↦ rfl) hθa hθb hleft hright
    (fun t ht ↦ (hmiddle μ hμ₀ t ht).hasDerivWithinAt)

end PDE.Analysis.ODE
