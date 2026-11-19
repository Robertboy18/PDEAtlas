/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs

import PDE.Analysis.Calculus.DSlope.Cubic.Local
import PDE.Analysis.Calculus.Jet.Localization
import PDE.Analysis.ODE.Interpolation.PhaseJets

/-!
# Cubic separation on an interval containing a prescribed gate

The two actual solution families share a complete second speed jet at their
moving section events. Phase alignment turns that event match into an anchored
match at time `e`; variational uniqueness then propagates it along a common
compact time interval.

Both `e` and the prescribed gate time `tStar` stay strictly inside the cubic
interval. Compactness gives one speed neighborhood on which both translated
families remain inside their established time domains. The families, their
moving event maps, and the sign of the physical speed are unchanged.

The original theorem is recovered by setting `tStar = e`. There is one proof of
phase localization, jet propagation, and cubic factorization.
-/

@[expose] public noncomputable section

open Filter Function Set
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Two points of an open interval lie in the interior of a closed subinterval. -/
private theorem exists_Icc_bracket {lo hi x y : ℝ} (hx : x ∈ Ioo lo hi) (hy : y ∈ Ioo lo hi) :
    ∃ a b, x ∈ Ioo a b ∧ y ∈ Ioo a b ∧ Icc a b ⊆ Ioo lo hi := by
  obtain ⟨a, hlo, ha⟩ := exists_between (lt_min hx.1 hy.1)
  obtain ⟨b, hb, hhi⟩ := exists_between (max_lt hx.2 hy.2)
  exact ⟨a, b, ⟨ha.trans_le (min_le_left _ _), (le_max_left _ _).trans_lt hb⟩,
    ⟨ha.trans_le (min_le_right _ _), (le_max_right _ _).trans_lt hb⟩,
    fun t ht ↦ ⟨hlo.trans_le ht.1, ht.2.trans_lt hhi⟩⟩

/-- Phase-aligned branches with matching first and second event jets have a smooth
cubic difference on one interval containing both the event and a prescribed gate.
The common base curve supplies their equal zeroth jets.

Both supplied families must already solve the same equation on `Icc lo hi`.
The gate assumption selects an interval inside that common domain; it does not
extend either family's ODE beyond its established time interval. No ordering
between the gate and the event is required.

The returned signed speed neighborhood contains a closed interval about zero.
The shifted families are globally smooth and retain the actual event maps near
zero speed. Their time equations and cubic identity hold on the returned compact
rectangle, with ordinary derivatives at its closed time endpoints. -/
theorem exists_phase_aligned_cubic_strip_containing_gate
    {F G : ℝ → ℝ → E} {f : E → E} {q : ℝ → E}
    {τ υ : ℝ → ℝ} {I : Set ℝ} {lo hi e tStar : ℝ}
    (hF : ContDiff ℝ ∞ F.uncurry) (hG : ContDiff ℝ ∞ G.uncurry)
    (hf : ContDiff ℝ 2 f) (hI : IsOpen I) (hzero : (0 : ℝ) ∈ I)
    (hτ : ContDiffOn ℝ ∞ τ I) (hυ : ContDiffOn ℝ ∞ υ I)
    (hτzero : τ 0 = e) (hυzero : υ 0 = e) (he : e ∈ Ioo lo hi)
    (htStar : tStar ∈ Ioo lo hi)
    (hodeF : ∀ t ∈ Icc lo hi, ∀ μ ∈ I,
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (hodeG : ∀ t ∈ Icc lo hi, ∀ μ ∈ I,
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) - μ • G t μ) t)
    (hFzero : EqOn (fun t ↦ F t 0) q (Icc lo hi))
    (hGzero : EqOn (fun t ↦ G t 0) q (Icc lo hi))
    (hfirst : deriv (fun μ ↦ G (υ μ) μ - F (τ μ) μ) 0 = 0)
    (hsecond : deriv (deriv (fun μ ↦ G (υ μ) μ - F (τ μ) μ)) 0 = 0) :
    ∃ (U V : ℝ → ℝ → E) (A : ℝ × ℝ → E)
      (a b r : ℝ) (J : Set ℝ),
      e ∈ Ioo a b ∧ tStar ∈ Ioo a b ∧ Icc a b ⊆ Ioo lo hi ∧
      IsOpen J ∧ (0 : ℝ) ∈ J ∧ J ⊆ I ∧
      0 < r ∧ Icc (-r) r ⊆ J ∧
      ContDiff ℝ ∞ U.uncurry ∧ ContDiff ℝ ∞ V.uncurry ∧ ContDiff ℝ ∞ A ∧
      (∀ μ ∈ J, ∀ t,
        U t μ = F (t + τ μ - e) μ ∧ V t μ = G (t + υ μ - e) μ) ∧
      (∀ t ∈ Icc a b, ∀ μ ∈ J,
        HasDerivAt (fun s ↦ U s μ) (f (U t μ) - μ • U t μ) t ∧
        HasDerivAt (fun s ↦ V s μ) (f (V t μ) - μ • V t μ) t) ∧
      EqOn (fun t ↦ U t 0) q (Icc a b) ∧
      EqOn (fun t ↦ V t 0) q (Icc a b) ∧
      ∀ t ∈ Icc a b, ∀ μ ∈ J, V t μ - U t μ = μ ^ 3 • A (t, μ) := by
  classical
  -- Localize the two event times together; the original solution strips stay fixed.
  obtain ⟨χ, O, _, _, _, _, hO, hzeroO, hOI, _, hrep⟩ :=
    PDE.Analysis.exists_smooth_cutoff_localization (hτ.prodMk hυ) hI
      isCompact_singleton (singleton_subset_iff.mpr hzero)
  let T : ℝ → ℝ × ℝ := I.indicator (fun μ ↦ χ μ • (τ μ, υ μ))
  have hT : ContDiff ℝ ∞ T := hrep.1
  have hTeq : EqOn T (fun μ ↦ (τ μ, υ μ)) O := hrep.2.2.2
  have h0O : (0 : ℝ) ∈ O := hzeroO (by simp)
  have hTzero : T 0 = (e, e) := by
    simpa only [hτzero, hυzero] using hTeq h0O
  let sτ : ℝ × ℝ → ℝ := fun z ↦ z.1 + (T z.2).1 - e
  let sυ : ℝ × ℝ → ℝ := fun z ↦ z.1 + (T z.2).2 - e
  have hsτ : ContDiff ℝ ∞ sτ :=
    (contDiff_fst.add (hT.fst.comp contDiff_snd)).sub contDiff_const
  have hsυ : ContDiff ℝ ∞ sυ :=
    (contDiff_fst.add (hT.snd.comp contDiff_snd)).sub contDiff_const
  let U : ℝ → ℝ → E := fun t μ ↦ F (sτ (t, μ)) μ
  let V : ℝ → ℝ → E := fun t μ ↦ G (sυ (t, μ)) μ
  have hU : ContDiff ℝ ∞ U.uncurry := hF.comp (hsτ.prodMk contDiff_snd)
  have hV : ContDiff ℝ ∞ V.uncurry := hG.comp (hsυ.prodMk contDiff_snd)
  have hagree (μ : ℝ) (hμ : μ ∈ O) (t : ℝ) :
      U t μ = F (t + τ μ - e) μ ∧ V t μ = G (t + υ μ - e) μ := by
    simp only [U, V, sτ, sυ, hTeq hμ, and_self]
  have hUzero (t : ℝ) : U t 0 = F t 0 := by
    simp only [U, sτ, hTzero, add_sub_cancel_right]
  have hVzero (t : ℝ) : V t 0 = G t 0 := by
    simp only [V, sυ, hTzero, add_sub_cancel_right]
  -- One open product controls both shifted times uniformly.
  let Ω : Set (ℝ × ℝ) :=
    ((Ioo lo hi ×ˢ O) ∩ sτ ⁻¹' Ioo lo hi) ∩ sυ ⁻¹' Ioo lo hi
  have hΩ : IsOpen Ω :=
    ((isOpen_Ioo.prod hO).inter (isOpen_Ioo.preimage hsτ.continuous)).inter
      (isOpen_Ioo.preimage hsυ.continuous)
  -- Fix a compact bracket around both times before shrinking the speed domain.
  obtain ⟨a₀, b₀, heouter, hstarouter, hCouter⟩ := exists_Icc_bracket he htStar
  have heclosed : e ∈ Icc a₀ b₀ := Ioo_subset_Icc_self heouter
  have hCzero : Icc a₀ b₀ ×ˢ {(0 : ℝ)} ⊆ Ω := by
    rintro ⟨t, μ⟩ ⟨ht, hμ⟩
    obtain rfl : μ = 0 := hμ
    change ((t ∈ Ioo lo hi ∧ (0 : ℝ) ∈ O) ∧ sτ (t, 0) ∈ Ioo lo hi) ∧ sυ (t, 0) ∈ Ioo lo hi
    refine ⟨⟨⟨hCouter ht, h0O⟩, ?_⟩, ?_⟩ <;>
      simpa only [sτ, sυ, hTzero, add_sub_cancel_right] using hCouter ht
  obtain ⟨Ttime, J₀, _, hJ₀, htime, hzeroJ₀, hproduct⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hΩ hCzero
  have h0J₀ : (0 : ℝ) ∈ J₀ := hzeroJ₀ (by simp)
  have hbox (t : ℝ) (ht : t ∈ Icc a₀ b₀) (μ : ℝ) (hμ : μ ∈ J₀) :
      (t ∈ Ioo lo hi ∧ μ ∈ O) ∧
        sτ (t, μ) ∈ Ioo lo hi ∧ sυ (t, μ) ∈ Ioo lo hi := by
    have h : (t, μ) ∈ Ω := hproduct ⟨htime ht, hμ⟩
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hJ₀O : J₀ ⊆ O := fun μ hμ ↦ (hbox e heclosed μ hμ).1.2
  have hUode : ∀ t ∈ Icc a₀ b₀, ∀ μ ∈ J₀,
      HasDerivAt (fun s ↦ U s μ) (f (U t μ) - μ • U t μ) t := fun t ht μ hμ ↦
    ((hodeF _ (Ioo_subset_Icc_self (hbox t ht μ hμ).2.1) μ (hOI (hJ₀O hμ))).comp_sub_const
      (t + (T μ).1) e).comp_add_const t (T μ).1
  have hVode : ∀ t ∈ Icc a₀ b₀, ∀ μ ∈ J₀,
      HasDerivAt (fun s ↦ V s μ) (f (V t μ) - μ • V t μ) t := fun t ht μ hμ ↦
    ((hodeG _ (Ioo_subset_Icc_self (hbox t ht μ hμ).2.2) μ (hOI (hJ₀O hμ))).comp_sub_const
      (t + (T μ).2) e).comp_add_const t (T μ).2
  have hUbase : EqOn (fun t ↦ U t 0) q (Icc a₀ b₀) := fun t ht ↦
    (hUzero t).trans (hFzero (Ioo_subset_Icc_self (hCouter ht)))
  have hVbase : EqOn (fun t ↦ V t 0) q (Icc a₀ b₀) := fun t ht ↦
    (hVzero t).trans (hGzero (Ioo_subset_Icc_self (hCouter ht)))
  -- The germ at t=e retains all derivatives of the moving event times.
  have hmove : (fun μ ↦ V e μ - U e μ) =ᶠ[𝓝 (0 : ℝ)]
      (fun μ ↦ G (υ μ) μ - F (τ μ) μ) := by
    filter_upwards [hO.mem_nhds h0O] with μ hμ
    simp only [hagree μ hμ e, add_sub_cancel_left]
  have hslice (t : ℝ) : ContDiff ℝ 2 (U t) ∧ ContDiff ℝ 2 (V t) :=
    ⟨(hU.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id),
      (hV.of_le (by simp)).comp (contDiff_const.prodMk contDiff_id)⟩
  have hsubfirst (t μ : ℝ) : deriv (fun ν ↦ V t ν - U t ν) μ =
      deriv (V t) μ - deriv (U t) μ :=
    deriv_fun_sub ((hslice t).2.differentiable two_ne_zero μ)
      ((hslice t).1.differentiable two_ne_zero μ)
  have hsubsecond (t : ℝ) : deriv (deriv (fun μ ↦ V t μ - U t μ)) 0 =
      deriv (deriv (V t)) 0 - deriv (deriv (U t)) 0 := by
    have hfun : deriv (fun μ ↦ V t μ - U t μ) =
        fun μ ↦ deriv (V t) μ - deriv (U t) μ := funext (hsubfirst t)
    rw [hfun]
    exact deriv_fun_sub ((hslice t).2.differentiable_deriv_two 0)
      ((hslice t).1.differentiable_deriv_two 0)
  have hanchor₁ : deriv (U e) 0 = deriv (V e) 0 :=
    (sub_eq_zero.mp ((hsubfirst e 0).symm.trans (hmove.deriv_eq.trans hfirst))).symm
  have hanchor₂ : deriv (deriv (U e)) 0 = deriv (deriv (V e)) 0 :=
    (sub_eq_zero.mp ((hsubsecond e).symm.trans (hmove.deriv.deriv_eq.trans hsecond))).symm
  obtain ⟨hjet₀, hjet₁, hjet₂⟩ := eqOn_speedJets_of_same_field
    (F := U) (G := V) (f := f) (q := q) (I := univ) (J := J₀)
    (a := a₀) (b := b₀) (c := e)
    isOpen_univ hJ₀ (subset_univ _) h0J₀ hU.contDiffOn hV.contDiffOn hf
    hUode hVode hUbase hVbase heclosed hanchor₁ hanchor₂
  -- The compact output interval lies strictly inside the propagation interval.
  obtain ⟨a, b, heinner, hstarinner, hinner⟩ := exists_Icc_bracket heouter hstarouter
  have hinnerClosed : Icc a b ⊆ Icc a₀ b₀ :=
    hinner.trans Ioo_subset_Icc_self
  obtain ⟨Tfactor, J, A, _, hcompact, hJ, h0J, hfactorDomain, hA, hfactor⟩ :=
    PDE.Analysis.exists_local_contDiff_cubic_factor_joint
      (F := fun z : ℝ × ℝ ↦ V z.1 z.2 - U z.1 z.2)
      (Ω := Ioo a₀ b₀ ×ˢ J₀) (K := Icc a b)
      (isOpen_Ioo.prod hJ₀) isCompact_Icc
      (fun z hz ↦ ⟨hinner hz.1, by simpa only [mem_singleton_iff.mp hz.2] using h0J₀⟩)
      (hV.sub hU).contDiffOn
      (fun t ht ↦ sub_eq_zero.mpr (hjet₀ (Ioo_subset_Icc_self ht.1)).symm)
      (fun t ht ↦ (hsubfirst t 0).trans
        (sub_eq_zero.mpr (hjet₁ (Ioo_subset_Icc_self ht.1)).symm))
      (fun t ht ↦ (hsubsecond t).trans
        (sub_eq_zero.mpr (hjet₂ (Ioo_subset_Icc_self ht.1)).symm))
  have hJJ₀ : J ⊆ J₀ := fun μ hμ ↦ (hfactorDomain
    (show (e, μ) ∈ Tfactor ×ˢ J from ⟨hcompact (Ioo_subset_Icc_self heinner), hμ⟩)).2
  -- Retain a compact signed speed interval as well as the open neighborhood.
  obtain ⟨r, hr, hrJ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hJ.mem_nhds h0J)
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hrJ
  exact ⟨U, V, A, a, b, r, J, heinner, hstarinner, hinnerClosed.trans hCouter,
    hJ, h0J, hJJ₀.trans (hJ₀O.trans hOI), hr, hrJ, hU, hV, hA,
    fun μ hμ t ↦ hagree μ (hJ₀O (hJJ₀ hμ)) t,
    fun t ht μ hμ ↦ ⟨hUode t (hinnerClosed ht) μ (hJJ₀ hμ), hVode t (hinnerClosed ht) μ (hJJ₀ hμ)⟩,
    hUbase.mono hinnerClosed, hVbase.mono hinnerClosed,
    fun t ht μ hμ ↦ hfactor t (hcompact ht) μ hμ⟩

/-- The event-only statement is the gate-containing theorem with the gate equal
to the event. It retains the original API and all of the same strip witnesses. -/
theorem exists_phase_aligned_cubic_strip
    {F G : ℝ → ℝ → E} {f : E → E} {q : ℝ → E}
    {τ υ : ℝ → ℝ} {I : Set ℝ} {lo hi e : ℝ}
    (hF : ContDiff ℝ ∞ F.uncurry) (hG : ContDiff ℝ ∞ G.uncurry)
    (hf : ContDiff ℝ 2 f) (hI : IsOpen I) (hzero : (0 : ℝ) ∈ I)
    (hτ : ContDiffOn ℝ ∞ τ I) (hυ : ContDiffOn ℝ ∞ υ I)
    (hτzero : τ 0 = e) (hυzero : υ 0 = e) (he : e ∈ Ioo lo hi)
    (hodeF : ∀ t ∈ Icc lo hi, ∀ μ ∈ I,
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t)
    (hodeG : ∀ t ∈ Icc lo hi, ∀ μ ∈ I,
      HasDerivAt (fun s ↦ G s μ) (f (G t μ) - μ • G t μ) t)
    (hFzero : EqOn (fun t ↦ F t 0) q (Icc lo hi))
    (hGzero : EqOn (fun t ↦ G t 0) q (Icc lo hi))
    (hfirst : deriv (fun μ ↦ G (υ μ) μ - F (τ μ) μ) 0 = 0)
    (hsecond : deriv (deriv (fun μ ↦ G (υ μ) μ - F (τ μ) μ)) 0 = 0) :
    ∃ (U V : ℝ → ℝ → E) (A : ℝ × ℝ → E)
      (a b r : ℝ) (J : Set ℝ),
      e ∈ Ioo a b ∧ Icc a b ⊆ Ioo lo hi ∧
      IsOpen J ∧ (0 : ℝ) ∈ J ∧ J ⊆ I ∧
      0 < r ∧ Icc (-r) r ⊆ J ∧
      ContDiff ℝ ∞ U.uncurry ∧ ContDiff ℝ ∞ V.uncurry ∧ ContDiff ℝ ∞ A ∧
      (∀ μ ∈ J, ∀ t,
        U t μ = F (t + τ μ - e) μ ∧ V t μ = G (t + υ μ - e) μ) ∧
      (∀ t ∈ Icc a b, ∀ μ ∈ J,
        HasDerivAt (fun s ↦ U s μ) (f (U t μ) - μ • U t μ) t ∧
        HasDerivAt (fun s ↦ V s μ) (f (V t μ) - μ • V t μ) t) ∧
      EqOn (fun t ↦ U t 0) q (Icc a b) ∧
      EqOn (fun t ↦ V t 0) q (Icc a b) ∧
      ∀ t ∈ Icc a b, ∀ μ ∈ J, V t μ - U t μ = μ ^ 3 • A (t, μ) := by
  obtain ⟨U, V, A, a, b, r, J, heinner, _, hrest⟩ :=
    exists_phase_aligned_cubic_strip_containing_gate (tStar := e)
      hF hG hf hI hzero hτ hυ hτzero hυzero he he
      hodeF hodeG hFzero hGzero hfirst hsecond
  exact ⟨U, V, A, a, b, r, J, heinner, hrest⟩

end PDE.Analysis.ODE
