/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.FirstIntegral
public import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Flux.Reflection

import PDE.Analysis.Calculus.Piecewise
import PDE.Analysis.Evolution.ODE.Regularity
import PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile.Tails.Axis
import CAS.ExactTactic

/-!
# Attaching the fixed-flux tails to exactly matched finite branches

Two finite shots at opposite speeds meet after time and coordinate
reversal when their terminal middle coordinates vanish and their other terminal
coordinates match. The section-one axis tails then complete a connection for
the same fixed flux. Ordinary derivatives are retained at all three joins.
For a smooth gate, the equation gives a smooth solution and hence the classical
second-order viscous profile, with both finite branches retained.
-/

@[expose] public noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile

open Filter Set PDE.Analysis
open scoped ContDiff Topology

/-- Two solutions of `x' = F x` that agree at a junction `c`, the first on `s ∩ Iic c` and the
second on `Ici c`, glue to the solution `fun t ↦ if t ≤ c then g t else k t` on `s`. -/
private theorem hasDerivAt_ite_le {F : ℝ^3 → ℝ^3} {g k : ℝ → ℝ^3} {s : Set ℝ} {c t : ℝ}
    (hg : ∀ t ∈ s, t ≤ c → HasDerivAt g (F (g t)) t) (hk : ∀ t, c ≤ t → HasDerivAt k (F (k t)) t)
    (hcs : c ∈ s) (hc : g c = k c) (ht : t ∈ s) :
    HasDerivAt (fun t ↦ if t ≤ c then g t else k t) (F (if t ≤ c then g t else k t)) t := by
  rcases lt_trichotomy t c with hlt | rfl | hgt
  · rw [ite_eq_left hlt.le]
    exact (hg t ht hlt.le).congr_of_eventuallyEq
      (eventually_of_mem (Iio_mem_nhds hlt) fun x hx ↦ ite_eq_left (le_of_lt hx))
  · rw [ite_eq_left (le_refl t)]
    exact hasDerivAt_iff_hasFDerivAt.mpr <| hasFDerivAt_if_of_eq (· ≤ t)
      (hg t hcs le_rfl).hasFDerivAt (hc ▸ hk t le_rfl : HasDerivAt k (F (g t)) t).hasFDerivAt hc
  · rw [ite_eq_right (not_le.mpr hgt)]
    exact (hk t hgt.le).congr_of_eventuallyEq
      (eventually_of_mem (Ioi_mem_nhds hgt) fun x hx ↦ ite_eq_right (not_le.mpr hx))

/-- Exact terminal matching of two supplied finite shots gives a global connection
for one fixed concrete flux. The second shot starts at the displaced section and
has speed `-μ`; its time and coordinate reversal has speed `μ`. -/
private theorem exists_prescribed_clock_connection_of_terminal_match {δ A B μ Tplus Tminus : ℝ}
    {b : ℝ → ℝ} {u v : ℝ → ℝ^3} (hδ : 0 ≤ δ) (hA : 1 ≤ A ^ 2) (hAB : A ^ 2 < B ^ 2)
    (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10)) (hμ : |μ| < 1 / 20000) (hTplus : 0 < Tplus)
    (hTminus : 0 < Tminus)
    (hu : ∀ t ∈ Icc (0 : ℝ) Tplus,
      HasDerivAt u (concreteGatedFlux δ (clockFeedback A B) b (u t) - μ • u t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) Tminus,
      HasDerivAt v (concreteGatedFlux δ (clockFeedback A B) b (v t) - (-μ) • v t) t)
    (hu0 : u 0 = !₂[0, 0, 1]) (hv0 : v 0 = !₂[0, -(2000000 * μ), 1]) (huMiddle : u Tplus 1 = 0)
    (hvMiddle : v Tminus 1 = 0) (hmatchX : u Tplus 0 = v Tminus 2)
    (hmatchZ : u Tplus 2 = v Tminus 0) :
    ∃ q : ℝ → ℝ^3,
      EqOn q u (Icc (0 : ℝ) Tplus) ∧
      EqOn q (fun t ↦ GatedFlux.reversal (v (Tplus + Tminus - t)))
        (Icc Tplus (Tplus + Tminus)) ∧
      (∀ t, HasDerivAt q
        (concreteGatedFlux δ (clockFeedback A B) b (q t) - μ • q t) t) ∧
      Tendsto q atBot (𝓝 0) ∧ Tendsto (deriv q) atBot (𝓝 0) ∧
      Tendsto q atTop (𝓝 !₂[0, 2000000 * μ, 0]) ∧
      Tendsto (deriv q) atTop (𝓝 0) := by
  let f : ℝ^3 → ℝ^3 := concreteGatedFlux δ (clockFeedback A B) b
  let S : ℝ := Tplus + Tminus
  have hTplusS : Tplus < S := lt_add_of_pos_right _ hTminus
  have hSsub : S - Tplus = Tminus := add_sub_cancel_left Tplus Tminus
  obtain ⟨qin, qout, hqin0, hqout0, _, hqinData, hqoutData,
      hqinlim, hqindlim, hqoutlim, hqoutdlim, _, _⟩ :=
    exists_prescribed_clock_axis_tails hδ hA hAB hbsupp hμ
  let w : ℝ → ℝ^3 := fun t ↦ GatedFlux.reversal (v (S - t))
  let tail : ℝ → ℝ^3 := fun t ↦ qout (t - S)
  have hterminal : u Tplus = GatedFlux.reversal (v Tminus) := by
    ext i
    fin_cases i
    · simpa [GatedFlux.reversal_apply] using hmatchX
    · simp [GatedFlux.reversal_apply, huMiddle, hvMiddle]
    · simpa [GatedFlux.reversal_apply] using hmatchZ
  have huW : u Tplus = w Tplus := by simpa only [w, hSsub] using hterminal
  have hjoinS : w S = tail S := by simp [w, tail, hv0, hqout0, GatedFlux.reversal_apply]
  -- Time reversal changes the speed only through the fixed-flux reflection identity.
  have hwODE (t : ℝ) (ht : t ∈ Icc Tplus S) : HasDerivAt w (f (w t) - μ • w t) t := by
    have hD : HasDerivAt w (GatedFlux.reversal (-(f (v (S - t)) - (-μ) • v (S - t)))) t :=
      GatedFlux.reversal.hasFDerivAt.comp_hasDerivAt t
        (HasDerivAt.comp_const_sub S t (hv (S - t) ⟨sub_nonneg.mpr ht.2, by linarith [ht.1]⟩))
    rw [map_neg] at hD
    exact hD.congr_deriv (GatedFlux.flux_sub_smul_reversal (fastLogCosh δ) MiddleClock.g
      cutoff (clockFeedback A B) b MiddleClock.g_neg μ (v (S - t))).symm
  -- Assemble from the right so each subsequent join uses an ordinary derivative.
  let qRight : ℝ → ℝ^3 := fun t ↦ if t ≤ S then w t else tail t
  have hqRightODE (t : ℝ) (ht : Tplus ≤ t) : HasDerivAt qRight (f (qRight t) - μ • qRight t) t :=
    hasDerivAt_ite_le (F := fun x ↦ f x - μ • x) (s := Ici Tplus) (fun t ht hts ↦ hwODE t ⟨ht, hts⟩)
      (fun t ht ↦ HasDerivAt.comp_sub_const t S (hqoutData (t - S) (sub_nonneg.mpr ht)).2)
      hTplusS.le hjoinS ht
  have hjoinTplus : u Tplus = qRight Tplus := by
    simpa only [qRight, ite_eq_left hTplusS.le] using huW
  let qMiddle : ℝ → ℝ^3 := fun t ↦ if t ≤ Tplus then u t else qRight t
  have hqMiddleODE (t : ℝ) (ht : 0 ≤ t) : HasDerivAt qMiddle (f (qMiddle t) - μ • qMiddle t) t :=
    hasDerivAt_ite_le (F := fun x ↦ f x - μ • x) (s := Ici 0) (fun t ht htT ↦ hu t ⟨ht, htT⟩)
      hqRightODE hTplus.le hjoinTplus ht
  have hjoinZero : qin 0 = qMiddle 0 := by
    simpa only [qMiddle, ite_eq_left hTplus.le] using hqin0.trans hu0.symm
  let q : ℝ → ℝ^3 := fun t ↦ if t ≤ 0 then qin t else qMiddle t
  have hqODE (t : ℝ) : HasDerivAt q (f (q t) - μ • q t) t :=
    hasDerivAt_ite_le (F := fun x ↦ f x - μ • x) (s := univ) (fun t _ ht ↦ (hqinData t ht).2)
      hqMiddleODE (mem_univ 0) hjoinZero (mem_univ t)
  have hleftEq : q =ᶠ[atBot] qin := by
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    simp only [q, ite_eq_left ht]
  have hleftDEq : deriv q =ᶠ[atBot] deriv qin := by
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    rw [(hqODE t).deriv, (hqinData t ht).2.deriv]
    simp only [q, ite_eq_left ht, f]
  have hrightEq : q =ᶠ[atTop] tail := by
    filter_upwards [eventually_gt_atTop S] with t ht
    simp only [q, ite_eq_right (not_le.mpr ((hTplus.trans hTplusS).trans ht)), qMiddle,
      ite_eq_right (not_le.mpr (hTplusS.trans ht)), qRight, ite_eq_right (not_le.mpr ht)]
  have hrightDEq : deriv q =ᶠ[atTop] (fun t ↦ deriv qout (t - S)) := by
    filter_upwards [eventually_gt_atTop S, hrightEq] with t ht heq
    rw [(hqODE t).deriv, (hqoutData (t - S) (sub_nonneg.mpr ht.le)).2.deriv, heq]
  have hshift : Tendsto (fun t : ℝ ↦ t - S) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  refine ⟨q, ?_, ?_, hqODE, hqinlim.congr' hleftEq.symm, hqindlim.congr' hleftDEq.symm,
    (hqoutlim.comp hshift).congr' hrightEq.symm, (hqoutdlim.comp hshift).congr' hrightDEq.symm⟩
  · intro t ht
    rcases ht.1.eq_or_lt with rfl | ht0
    · simpa only [q, ite_eq_left le_rfl] using hqin0.trans hu0.symm
    · simp only [q, ite_eq_right (not_le.mpr ht0), qMiddle, ite_eq_left ht.2]
  · change EqOn q w (Icc Tplus S)
    intro t ht
    have ht0 : ¬t ≤ 0 := not_le.mpr (hTplus.trans_le ht.1)
    rcases ht.1.eq_or_lt with rfl | htle
    · simpa only [q, ite_eq_right ht0, qMiddle, ite_eq_left le_rfl] using huW
    · simp only [q, ite_eq_right ht0, qMiddle, ite_eq_right (not_le.mpr htle), qRight,
        ite_eq_left ht.2]

/-- Exactly matched finite branches for a smooth signed gate extend to a classical
viscous profile for the same fixed flux. The profile retains both supplied finite
branches, with the second branch reflected and reversed in time. Exact terminal
matching is a hypothesis at the chosen speed. -/
theorem exists_prescribed_clock_viscous_profile_of_terminal_match {δ A B μ Tplus Tminus : ℝ}
    {b : ℝ → ℝ} {u v : ℝ → ℝ^3} (hδ : 0 ≤ δ) (hA : 1 ≤ A ^ 2) (hAB : A ^ 2 < B ^ 2)
    (hbsupp : tsupport b ⊆ Icc (205 : ℝ) (2051 / 10)) (hb : ContDiff ℝ ∞ b) (hμ : |μ| < 1 / 20000)
    (hTplus : 0 < Tplus) (hTminus : 0 < Tminus)
    (hu : ∀ t ∈ Icc (0 : ℝ) Tplus,
      HasDerivAt u (concreteGatedFlux δ (clockFeedback A B) b (u t) - μ • u t) t)
    (hv : ∀ t ∈ Icc (0 : ℝ) Tminus,
      HasDerivAt v (concreteGatedFlux δ (clockFeedback A B) b (v t) - (-μ) • v t) t)
    (hu0 : u 0 = !₂[0, 0, 1]) (hv0 : v 0 = !₂[0, -(2000000 * μ), 1]) (huMiddle : u Tplus 1 = 0)
    (hvMiddle : v Tminus 1 = 0) (hmatchX : u Tplus 0 = v Tminus 2)
    (hmatchZ : u Tplus 2 = v Tminus 0) :
    ∃ q : ℝ → ℝ^3,
      IsViscousProfile (concreteGatedFlux δ (clockFeedback A B) b)
        0 !₂[0, 2000000 * μ, 0] μ q ∧
      EqOn q u (Icc (0 : ℝ) Tplus) ∧
      EqOn q (fun t ↦ GatedFlux.reversal (v (Tplus + Tminus - t)))
        (Icc Tplus (Tplus + Tminus)) := by
  obtain ⟨q, hqu, hqv, hqODE, hleft, hleftD, hright, hrightD⟩ :=
    exists_prescribed_clock_connection_of_terminal_match hδ hA hAB hbsupp hμ
      hTplus hTminus hu hv hu0 hv0 huMiddle hvMiddle hmatchX hmatchZ
  let f : ℝ^3 → ℝ^3 := concreteGatedFlux δ (clockFeedback A B) b
  have hf : ContDiff ℝ ∞ f := contDiff_concreteGatedFlux δ (contDiff_clockFeedback A B) hb
  have hfield : ContDiff ℝ ∞ (fun p : ℝ × ℝ^3 ↦ f p.2 - μ • p.2) := by fun_prop
  have hqSmooth : ContDiff ℝ ∞ q := contDiffOn_univ.mp
    (PDE.Analysis.Evolution.contDiffOn_of_hasDerivAt (f := fun _ x ↦ f x - μ • x) isOpen_univ
      hfield.contDiffOn fun t _ ↦ hqODE t)
  have hderiv : deriv q = fun t ↦ f (q t) - μ • q t := funext fun t ↦ (hqODE t).deriv
  refine ⟨q, ⟨hqSmooth.of_le (by simp), fun t ↦ ?_, hleft, hright, hleftD, hrightD⟩, hqu, hqv⟩
  have hqt : HasDerivAt q (deriv q t) t := (hqODE t).differentiableAt.hasDerivAt
  have hd := ((hf.differentiable (by simp) (q t)).hasFDerivAt.comp_hasDerivAt t hqt).sub
    (hqt.const_smul μ)
  change HasDerivAt (fun s ↦ f (q s) - μ • q s)
    (fderiv ℝ f (q t) (deriv q t) - μ • deriv q t) t at hd
  rw [← hderiv] at hd
  exact hd.deriv

end PDE.Hyperbolic.ConservationLaw.System.ViscousProfile.ReverseProfile
