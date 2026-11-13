/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.ImplicitFunction.RegularLevel
public import PDE.Analysis.ODE.SmoothDependence.FiniteInterval.Parameter

import PDE.Analysis.Calculus.Prod.SliceDerivative

/-!
# Anchored flux flows and transverse events

A complete zero-speed trajectory gives a smooth family for the field
`f x - μ • x` on a fixed closed time interval. The initial section at the
supplied anchor is retained for every speed, and a transverse linear section
has a smooth event on one open speed neighborhood.

Time is translated, never reversed. The same physical speed sign therefore
holds on both sides of the anchor, including when the anchor is an endpoint.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A fixed smooth flux and a supplied complete trajectory determine an actual
smooth flow with an arbitrary smooth speed-dependent initial section. The ODE
holds at both endpoints of the requested slab. A transverse event stays in its
interior and is locally unique near the reference event.

The global smooth extension retains the initial section for all speeds; the
ODE and event conclusions hold on the returned open speed neighborhood. -/
theorem exists_anchored_flux_flow_event
    (f : E → E) (hf : ContDiff ℝ ∞ f)
    (q : ℝ → E) (hq : ∀ t, HasDerivAt q (f (q t)) t)
    (a : ℝ → E) (ha : ContDiff ℝ ∞ a)
    {lo hi c e : ℝ} (hc : c ∈ Icc lo hi) (he : e ∈ Ioo lo hi)
    (ha0 : a 0 = q c)
    (ell : E →L[ℝ] ℝ) (htransverse : ell (f (q e)) ≠ 0) :
    ∃ (Φ : ℝ × ℝ → E) (T : ℝ → ℝ) (I : Set ℝ),
      ContDiff ℝ ∞ Φ ∧ IsOpen I ∧ (0 : ℝ) ∈ I ∧
      (∀ μ, Φ (c, μ) = a μ) ∧
      EqOn (fun t ↦ Φ (t, 0)) q (Icc lo hi) ∧
      (∀ μ ∈ I, ∀ t ∈ Icc lo hi,
        HasDerivAt (fun s ↦ Φ (s, μ))
          (f (Φ (t, μ)) - μ • Φ (t, μ)) t) ∧
      ContDiffOn ℝ ∞ T I ∧ T 0 = e ∧
      (∀ μ ∈ I, T μ ∈ Ioo lo hi ∧ ell (Φ (T μ, μ)) = ell (q e)) ∧
      ∀ᶠ p in 𝓝 ((0 : ℝ), e),
        ell (Φ (p.2, p.1)) = ell (q e) ↔ T p.1 = p.2 := by
  let v : ℝ × E → E := fun p ↦ f p.2 - p.1 • p.2
  have hv : ContDiff ℝ ∞ v :=
    (hf.comp contDiff_snd).sub (contDiff_fst.smul contDiff_snd)
  let qShift : ℝ → E := fun s ↦ q (s + c)
  have hqcont : Continuous q :=
    continuous_iff_continuousAt.mpr fun t ↦ (hq t).continuousAt
  -- The complete reference supplies slack even for an endpoint anchor.
  have hlo : lo - c - 1 < 0 :=
    sub_neg.mpr ((sub_nonpos.mpr hc.1).trans_lt zero_lt_one)
  have hhi : 0 < hi - c + 1 :=
    add_pos_of_nonneg_of_pos (sub_nonneg.mpr hc.2) zero_lt_one
  have hshift (t : ℝ) (ht : t ∈ Icc lo hi) :
      t - c ∈ Icc (lo - c - 1) (hi - c + 1) := by
    constructor
    · exact (sub_le_self (lo - c) zero_le_one).trans (sub_le_sub_right ht.1 c)
    · exact (sub_le_sub_right ht.2 c).trans (le_add_of_nonneg_right zero_le_one)
  have hqShiftcont : ContinuousOn qShift (Icc (lo - c - 1) (hi - c + 1)) :=
    (hqcont.comp (continuous_id.add continuous_const)).continuousOn
  have hqShiftODE : ∀ s ∈ Ioo (lo - c - 1) (hi - c + 1),
      HasDerivAt qShift (v (0, qShift s)) s := by
    intro s _
    simpa only [qShift, v, zero_smul, sub_zero] using (hq (s + c)).comp_add_const s c
  obtain ⟨F, U, hU, hbaseU, hF, hFzero, hFbase, hFode⟩ :=
    exists_contDiff_infty_parameterized_family_near_solution_Icc v hv hlo hhi
      0 qShift hqShiftcont hqShiftODE (q c) (by simp only [qShift, zero_add])
  let Φ : ℝ × ℝ → E := fun p ↦ F (p.1 - c, (p.2, a p.2))
  let N : Set ℝ := (fun μ ↦ (μ, a μ)) ⁻¹' U
  have hΦ : ContDiff ℝ ∞ Φ :=
    hF.comp ((contDiff_fst.sub contDiff_const).prodMk
      (contDiff_snd.prodMk (ha.comp contDiff_snd)))
  have hN : IsOpen N := hU.preimage (continuous_id.prodMk ha.continuous)
  have h0N : (0 : ℝ) ∈ N := by
    change ((0 : ℝ), a 0) ∈ U
    simpa only [ha0] using hbaseU
  have hinit (μ : ℝ) : Φ (c, μ) = a μ := by
    simpa only [Φ, sub_self] using hFzero (μ, a μ)
  have hbase : EqOn (fun t ↦ Φ (t, 0)) q (Icc lo hi) := by
    intro t ht
    simpa only [Φ, ha0, qShift, sub_add_cancel] using hFbase (hshift t ht)
  have hode (μ : ℝ) (hμ : μ ∈ N) (t : ℝ) (ht : t ∈ Icc lo hi) :
      HasDerivAt (fun s ↦ Φ (s, μ))
        (f (Φ (t, μ)) - μ • Φ (t, μ)) t := by
    have hd := hFode (μ, a μ) hμ (t - c) (hshift t ht)
    simpa only [Φ, v] using hd.comp_sub_const t c
  -- The event map uses (speed, time); Φ itself uses (time, speed).
  let Y : ℝ × ℝ → ℝ := fun p ↦ ell (Φ (p.2, p.1))
  have hY : ContDiff ℝ ∞ Y :=
    ell.contDiff.comp (hΦ.comp (contDiff_snd.prodMk contDiff_fst))
  have heClosed : e ∈ Icc lo hi := Ioo_subset_Icc_self he
  have hYbase : Y (0, e) = ell (q e) := congrArg ell (hbase heClosed)
  have hvelocity : HasDerivAt (fun t ↦ Φ (t, 0)) (f (q e)) e := by
    simpa only [zero_smul, sub_zero, hbase heClosed] using hode 0 h0N e heClosed
  have htime : HasDerivAt (fun t ↦ Y (0, t)) (ell (f (q e))) e := by
    exact ell.hasFDerivAt.comp_hasDerivAt e hvelocity
  have hpartial : fderiv ℝ Y (0, e) (0, 1) ≠ 0 := by
    have heq : fderiv ℝ Y (0, e) (0, 1) = ell (f (q e)) :=
      (deriv_prod_timeSlice Y 0 e ((hY.differentiable (by simp)) (0, e))).symm.trans
        htime.deriv
    exact fun hzero ↦ htransverse (heq.symm.trans hzero)
  have hYon : ContDiffOn ℝ (⊤ : ℕ∞) Y (N ×ˢ Ioo lo hi) := hY.contDiffOn
  obtain ⟨T, I, hI, h0I, hT, hT0, hgraph, hunique⟩ :=
    hYon.exists_implicitFunction_of_fderiv_snd_ne_zero (hN.prod isOpen_Ioo) (by simp)
      (show ((0 : ℝ), e) ∈ N ×ˢ Ioo lo hi from ⟨h0N, he⟩) hpartial
  refine ⟨Φ, T, I, hΦ, hI, h0I, hinit, hbase, ?_, hT, hT0, ?_, ?_⟩
  · intro μ hμ t ht
    exact hode μ (hgraph μ hμ).1.1 t ht
  · intro μ hμ
    exact ⟨(hgraph μ hμ).1.2, (hgraph μ hμ).2.trans hYbase⟩
  · change ∀ᶠ p in 𝓝 ((0 : ℝ), e), Y p = ell (q e) ↔ T p.1 = p.2
    simpa only [hYbase] using hunique

end PDE.Analysis.ODE
