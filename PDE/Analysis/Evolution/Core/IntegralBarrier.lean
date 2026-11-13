/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A strict barrier for an integral energy balance

An integrable rate determines a continuous trajectory through its time integral.
If a continuous upper bound for that rate is negative at a proposed barrier,
the trajectory cannot reach the barrier from below. The proof uses only the
integral balance near the first contact.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution

/-- If `e(t) - e(a) = ∫ₐᵗ g` on `[a, b]` with `g` integrable, `e(a) < R`, and
`g t ≤ F (e t)` for a function `F` continuous at `R` with `F R < 0`, then `e < R`
on `[a, b]`. -/
theorem strict_sublevel_invariant_of_integral_balance
    {e g F : ℝ → ℝ} {a b R : ℝ}
    (hg : IntervalIntegrable g volume a b)
    (hbalance : ∀ t ∈ Icc a b, e t - e a = ∫ s in a..t, g s)
    (ha : e a < R) (hF : ContinuousAt F R) (hFR : F R < 0)
    (hbound : ∀ t ∈ Icc a b, g t ≤ F (e t)) :
    ∀ t ∈ Icc a b, e t < R := by
  have he : ContinuousOn e (Icc a b) := by
    have hc : ContinuousOn (fun t ↦ e a + ∫ s in a..t, g s) (uIcc a b) :=
      continuousOn_const.add
      (intervalIntegral.continuousOn_primitive_interval' hg left_mem_uIcc)
    apply (hc.mono Icc_subset_uIcc).congr
    intro t ht
    linarith [hbalance t ht]
  intro t ht
  by_contra hnot
  have hRet : R ≤ e t := le_of_not_gt hnot
  have hcont : ContinuousOn e (Icc a t) :=
    he.mono (Icc_subset_Icc_right ht.2)
  have hhitNonempty : (Icc a t ∩ e ⁻¹' {R}).Nonempty := by
    rcases intermediate_value_Icc ht.1 hcont ⟨ha.le, hRet⟩ with ⟨s, hs, hsE⟩
    exact ⟨s, hs, by simp [hsE]⟩
  have hhitClosed : IsClosed (Icc a t ∩ e ⁻¹' {R}) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hhitCompact : IsCompact (Icc a t ∩ e ⁻¹' {R}) :=
    isCompact_Icc.of_isClosed_subset hhitClosed inter_subset_left
  obtain ⟨tau, htauMem, htauLeast⟩ := hhitCompact.exists_isLeast hhitNonempty
  have htauIcc : tau ∈ Icc a b := ⟨htauMem.1.1, htauMem.1.2.trans ht.2⟩
  have htauEq : e tau = R := by simpa using htauMem.2
  have hat : a < tau := lt_of_le_of_ne htauMem.1.1
    (fun h ↦ ha.ne (by simpa [h] using htauEq))
  have hFtau : ContinuousAt F (e tau) := htauEq.symm ▸ hF
  have hnear : ∀ᶠ x in 𝓝[Icc a b] tau, F (e x) < 0 :=
    (hFtau.comp_continuousWithinAt (he tau htauIcc)).eventually
      (Iio_mem_nhds (by simpa only [Function.comp_apply, htauEq] using hFR))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (eventually_nhdsWithin_iff.mp hnear)
  let s := max a (tau - ε / 2)
  have has : a ≤ s := le_max_left _ _
  have hst : s < tau := max_lt hat (by linarith)
  have hsIcc : s ∈ Icc a b := ⟨has, hst.le.trans htauIcc.2⟩
  have hsLower : tau - ε / 2 ≤ s := le_max_right _ _
  have hnonpos (x : ℝ) (hx : x ∈ Icc s tau) : g x ≤ 0 := by
    have hxIcc : x ∈ Icc a b := ⟨has.trans hx.1, hx.2.trans htauIcc.2⟩
    have hdist : dist x tau < ε := by
      rw [Real.dist_eq]
      apply abs_lt.mpr
      constructor <;> linarith [hx.1, hx.2]
    exact (hbound x hxIcc).trans (hball hdist hxIcc).le
  have hsBelow : e s < R := by
    by_contra hsNot
    have hsCont : ContinuousOn e (Icc a s) :=
      hcont.mono (Icc_subset_Icc_right (hst.le.trans htauMem.1.2))
    rcases intermediate_value_Icc has hsCont ⟨ha.le, le_of_not_gt hsNot⟩ with
      ⟨y, hy, hyE⟩
    have hyHit : y ∈ Icc a t ∩ e ⁻¹' {R} :=
      ⟨⟨hy.1, hy.2.trans (hst.le.trans htauMem.1.2)⟩, by simp [hyE]⟩
    exact (not_lt_of_ge (htauLeast hyHit)) (hy.2.trans_lt hst)
  have hIntegral : (∫ x in s..tau, g x) ≤ 0 := by
    have hn := intervalIntegral.integral_nonneg (μ := volume) hst.le
      (fun x hx ↦ neg_nonneg.mpr (hnonpos x hx))
    simpa only [intervalIntegral.integral_neg, neg_nonneg] using hn
  have hab : a ≤ b := ht.1.trans ht.2
  have hgas : IntervalIntegrable g volume a s := hg.mono_set (by
    simpa only [uIcc_of_le has, uIcc_of_le hab] using
      (Icc_subset_Icc le_rfl hsIcc.2))
  have hgst : IntervalIntegrable g volume s tau := hg.mono_set (by
    simpa only [uIcc_of_le hst.le, uIcc_of_le hab] using
      (Icc_subset_Icc has htauIcc.2))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hgas hgst
  have hbt := hbalance tau htauIcc
  have hbs := hbalance s hsIcc
  linarith

end PDE.Analysis.Evolution
