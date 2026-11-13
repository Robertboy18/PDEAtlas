/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Zeros crossed in one direction

Let `f` be a real function on an order-connected set `S` that is continuous on `S` and has a
positive derivative at each of its zeros in `S`. Then `f` crosses zero only upwards: a positive
value stays positive to its right (`pos_of_le_of_deriv_pos_at_zeros`), a negative value stays
negative to its left (`neg_of_le_of_deriv_pos_at_zeros`), and `f` has at most one zero in `S`
(`eq_of_deriv_pos_at_zeros`). Signs at two points then locate every zero of `f` in `S`
(`mem_Ioo_of_deriv_pos_at_zeros`). These are the facts behind interlacing arguments for the
zeros of solutions of second-order equations: on an interval free of the zeros of one solution,
a suitable combination with a second solution has a derivative of fixed sign at its zeros.

The same facts count the zeros of a function on an interval cut into regions by breakpoints at
which it does not vanish (`mem_Ioo_of_regions`): if on each region the function, multiplied by a
fixed sign, has a positive derivative at its zeros, then each region with a sign change on an
enclosure `(p, q)` holds exactly one zero, which lies in `(p, q)`, and a last region with the
wrong sign at its right end holds none. A continuous function without zeros on an
order-connected set has one sign there (`sign_eq_of_forall_ne_zero`), so its sign on an interval
can be read at a single point (`pos_mul_of_witness`).
-/

@[expose] public section

namespace PDE.Analysis

open Set Filter Topology

/-- At a zero with positive derivative a function is negative just to the left. -/
theorem eventually_neg_left_of_deriv_pos {f : ℝ → ℝ} {x : ℝ} (hd : DifferentiableAt ℝ f x)
    (h0 : f x = 0) (hpos : 0 < deriv f x) : ∀ᶠ t in 𝓝[<] x, f t < 0 := by
  have h := hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
  have hev : ∀ᶠ t in 𝓝[≠] x, 0 < slope f x t := h.eventually (lt_mem_nhds hpos)
  have hev' : ∀ᶠ t in 𝓝[<] x, 0 < slope f x t :=
    hev.filter_mono (nhdsWithin_mono _ fun t ht ↦ ne_of_lt ht)
  filter_upwards [hev', self_mem_nhdsWithin] with t ht htx
  rw [slope_def_field, h0, sub_zero] at ht
  have htx' : t - x < 0 := sub_neg.mpr htx
  exact (div_pos_iff.mp ht).resolve_left (fun h' ↦ (not_lt.mpr h'.2.le) htx') |>.1

/-- At a zero with positive derivative a function is positive just to the right. -/
theorem eventually_pos_right_of_deriv_pos {f : ℝ → ℝ} {x : ℝ} (hd : DifferentiableAt ℝ f x)
    (h0 : f x = 0) (hpos : 0 < deriv f x) : ∀ᶠ t in 𝓝[>] x, 0 < f t := by
  have h := hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
  have hev : ∀ᶠ t in 𝓝[≠] x, 0 < slope f x t := h.eventually (lt_mem_nhds hpos)
  have hev' : ∀ᶠ t in 𝓝[>] x, 0 < slope f x t :=
    hev.filter_mono (nhdsWithin_mono _ fun t ht ↦ ne_of_gt ht)
  filter_upwards [hev', self_mem_nhdsWithin] with t ht htx
  rw [slope_def_field, h0, sub_zero] at ht
  exact (div_pos_iff.mp ht).resolve_right (fun h' ↦ (not_lt.mpr h'.2.le) (sub_pos.mpr htx)) |>.1

/-- A function that has a positive derivative at its zeros in an order-connected set keeps a
positive value at every point of the set to the right. -/
theorem pos_of_le_of_deriv_pos_at_zeros {f : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hc : ContinuousOn f S)
    (hd : ∀ x ∈ S, f x = 0 → DifferentiableAt ℝ f x ∧ 0 < deriv f x)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≤ b) (hfa : 0 < f a) : 0 < f b := by
  by_contra hfb
  push Not at hfb
  have hsub : Icc a b ⊆ S := hS.out ha hb
  set T := Icc a b ∩ {x | f x ≤ 0} with hT
  have hTc : IsClosed T :=
    (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hbT : b ∈ T := ⟨⟨hab, le_rfl⟩, hfb⟩
  have hbdd : BddBelow T := ⟨a, fun x hx ↦ hx.1.1⟩
  set c := sInf T with hcdef
  have hcT : c ∈ T := hTc.csInf_mem ⟨b, hbT⟩ hbdd
  have hpos : ∀ t ∈ Ico a c, 0 < f t := by
    intro t ht
    by_contra hft
    push Not at hft
    have htT : t ∈ T := ⟨⟨ht.1, ht.2.le.trans hcT.1.2⟩, hft⟩
    exact (not_le.mpr ht.2) (csInf_le hbdd htT)
  have hac : a < c := by
    rcases eq_or_lt_of_le hcT.1.1 with h | h
    · rw [← h] at hcT
      exact absurd hcT.2 (not_le.mpr hfa)
    · exact h
  have hfc : f c = 0 := by
    refine le_antisymm hcT.2 ?_
    by_contra hneg
    push Not at hneg
    have hcont : ContinuousOn f (Icc a c) := hc.mono ((Icc_subset_Icc le_rfl hcT.1.2).trans hsub)
    obtain ⟨t, ht, hft⟩ := intermediate_value_Ioo' hac.le hcont ⟨hneg, hfa⟩
    exact (hpos t ⟨ht.1.le, ht.2⟩).ne' hft
  obtain ⟨hdc, hdpos⟩ := hd c (hsub hcT.1) hfc
  have hev := eventually_neg_left_of_deriv_pos hdc hfc hdpos
  have hev2 : ∀ᶠ t in 𝓝[<] c, a < t := Filter.eventually_of_mem (Ioo_mem_nhdsLT hac) fun t ht ↦ ht.1
  obtain ⟨t, hft, hat, htc⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
  exact (hpos t ⟨hat.le, htc⟩).not_gt hft

/-- A function that has a positive derivative at its zeros in an order-connected set keeps a
negative value at every point of the set to the left. -/
theorem neg_of_le_of_deriv_pos_at_zeros {f : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hc : ContinuousOn f S)
    (hd : ∀ x ∈ S, f x = 0 → DifferentiableAt ℝ f x ∧ 0 < deriv f x)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≤ b) (hfb : f b < 0) : f a < 0 := by
  by_contra hfa
  push Not at hfa
  rcases eq_or_lt_of_le hfa with h | h
  · obtain ⟨hda, hdpos⟩ := hd a ha h.symm
    have hev := eventually_pos_right_of_deriv_pos hda h.symm hdpos
    rcases eq_or_lt_of_le hab with hab' | hab'
    · rw [hab'] at h
      exact absurd h.symm hfb.ne
    have hev2 : ∀ᶠ t in 𝓝[>] a, t < b :=
      Filter.eventually_of_mem (Ioo_mem_nhdsGT hab') fun t ht ↦ ht.2
    obtain ⟨t, hft, htb, hat⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
    have htS : t ∈ S := hS.out ha hb ⟨(mem_Ioi.mp hat).le, htb.le⟩
    exact (pos_of_le_of_deriv_pos_at_zeros hS hc hd htS hb htb.le hft).not_gt hfb
  · exact (pos_of_le_of_deriv_pos_at_zeros hS hc hd ha hb hab h).not_gt hfb

/-- A function that has a positive derivative at its zeros in an order-connected set has at
most one zero there. -/
theorem eq_of_deriv_pos_at_zeros {f : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hc : ContinuousOn f S)
    (hd : ∀ x ∈ S, f x = 0 → DifferentiableAt ℝ f x ∧ 0 < deriv f x)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hfx : f x = 0) (hfy : f y = 0) : x = y := by
  wlog hxy : x < y generalizing x y
  · rcases eq_or_lt_of_le (not_lt.mp hxy) with h | h
    · exact h.symm
    · exact (this hy hx hfy hfx h).symm
  obtain ⟨hdx, hdpos⟩ := hd x hx hfx
  have hev := eventually_pos_right_of_deriv_pos hdx hfx hdpos
  have hev2 : ∀ᶠ t in 𝓝[>] x, t < y := Filter.eventually_of_mem (Ioo_mem_nhdsGT hxy) fun t ht ↦ ht.2
  obtain ⟨t, hft, hty, hxt⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
  have htS : t ∈ S := hS.out hx hy ⟨(mem_Ioi.mp hxt).le, hty.le⟩
  exact absurd hfy (pos_of_le_of_deriv_pos_at_zeros hS hc hd htS hy hty.le hft).ne'

/-- If a function with a positive derivative at its zeros in an order-connected set is negative
at `p` and positive at `q`, then each of its zeros in the set lies in `(p, q)`. -/
theorem mem_Ioo_of_deriv_pos_at_zeros {f : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hc : ContinuousOn f S)
    (hd : ∀ x ∈ S, f x = 0 → DifferentiableAt ℝ f x ∧ 0 < deriv f x)
    {p q : ℝ} (hp : p ∈ S) (hq : q ∈ S) (hfp : f p < 0) (hfq : 0 < f q)
    {x : ℝ} (hx : x ∈ S) (hfx : f x = 0) : x ∈ Ioo p q := by
  constructor
  · by_contra h
    push Not at h
    exact (neg_of_le_of_deriv_pos_at_zeros hS hc hd hx hp h hfp).ne hfx
  · by_contra h
    push Not at h
    exact (pos_of_le_of_deriv_pos_at_zeros hS hc hd hq hx h hfq).ne' hfx

/-- A function with a positive derivative at its zeros in an order-connected set has no zero in
the set to the left of a point where it is negative. -/
theorem lt_of_deriv_pos_at_zeros {f : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hc : ContinuousOn f S)
    (hd : ∀ x ∈ S, f x = 0 → DifferentiableAt ℝ f x ∧ 0 < deriv f x)
    {p : ℝ} (hp : p ∈ S) (hfp : f p < 0) {x : ℝ} (hx : x ∈ S) (hfx : f x = 0) : p < x := by
  by_contra h
  push Not at h
  exact (neg_of_le_of_deriv_pos_at_zeros hS hc hd hx hp h hfp).ne hfx

/-- A continuous function without zeros on an order-connected set has one sign there: the
product of two of its values is positive. -/
theorem sign_eq_of_forall_ne_zero {g : ℝ → ℝ} {S : Set ℝ} (hS : S.OrdConnected)
    (hc : ContinuousOn g S) (hne : ∀ x ∈ S, g x ≠ 0) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    0 < g x * g y := by
  by_contra h
  push Not at h
  rcases mul_nonpos_iff.mp h with ⟨hgx, hgy⟩ | ⟨hgx, hgy⟩
  · obtain ⟨z, hz, hgz⟩ := hS.isPreconnected.intermediate_value hy hx hc ⟨hgy, hgx⟩
    exact hne z hz hgz
  · obtain ⟨z, hz, hgz⟩ := hS.isPreconnected.intermediate_value hx hy hc ⟨hgx, hgy⟩
    exact hne z hz hgz

/-- On an interval `(u, v)` where a continuous `f` has no zero, a point `w ∈ (u, v]` with
`0 < s f(w)` gives `0 < s f(x)` on all of `(u, v)`. -/
theorem pos_mul_of_witness {f : ℝ → ℝ} (hf : Continuous f) {u v w s : ℝ}
    (hne : ∀ x ∈ Ioo u v, f x ≠ 0) (hw : w ∈ Ioc u v) (hfw : 0 < s * f w) :
    ∀ x ∈ Ioo u v, 0 < s * f x := by
  intro x hx
  have hfw0 : f w ≠ 0 := fun h ↦ by
    rw [h, mul_zero] at hfw
    exact lt_irrefl _ hfw
  have hprod : 0 < f w * f x := by
    rcases hw.2.eq_or_lt with hwv | hwv
    · refine sign_eq_of_forall_ne_zero ordConnected_Ioc hf.continuousOn (fun t ht ↦ ?_) hw
        ⟨hx.1, hx.2.le⟩
      rcases ht.2.eq_or_lt with htv | htv
      · rw [htv, ← hwv]
        exact hfw0
      · exact hne t ⟨ht.1, htv⟩
    · exact sign_eq_of_forall_ne_zero ordConnected_Ioo hf.continuousOn hne ⟨hw.1, hwv⟩ hx
  have h₃ : 0 < (s * f x) * f w ^ 2 := by
    have h₄ := mul_pos hfw hprod
    have e : (s * f w) * (f w * f x) = (s * f x) * f w ^ 2 := by ring
    linarith
  exact pos_of_mul_pos_left h₃ (sq_nonneg _)

/-- Zeros of a function on an interval cut into regions. The breakpoints `β 0, ..., β n` cut
`(β 0, β n)` into the regions `(β k, β (k + 1))`, and `f` does not vanish at the interior
breakpoints. On region `k` the function `s k * f` has a positive derivative at the zeros of
`f`. Each region `k < m` contains an enclosure `(p k, q k)` on which `s k * f` changes sign
from negative to positive. If `m = n - 1`, the last region has no enclosure and
`s m * f (β n) < 0`. Then every zero of `f` in `(β 0, β n)` lies in one of the enclosures, and
each enclosure contains exactly one zero. -/
theorem mem_Ioo_of_regions {f : ℝ → ℝ} (hf : Differentiable ℝ f) {n m : ℕ}
    {β p q s : ℕ → ℝ}
    (hβf : ∀ k, 0 < k → k < n → f (β k) ≠ 0)
    (hs : ∀ k < n, ∀ x ∈ Set.Ioo (β k) (β (k + 1)), f x = 0 → 0 < s k * deriv f x)
    (hmn : m ≤ n) (hnm : n ≤ m + 1)
    (hp : ∀ k < m, β k < p k) (hpq : ∀ k < m, p k < q k) (hq : ∀ k < m, q k < β (k + 1))
    (hfp : ∀ k < m, s k * f (p k) < 0) (hfq : ∀ k < m, 0 < s k * f (q k))
    (hcut : m < n → s m * f (β n) < 0) :
    (∀ x ∈ Set.Ioo (β 0) (β n), f x = 0 → ∃ k < m, x ∈ Set.Ioo (p k) (q k)) ∧
      ∀ k < m, ∃! x, x ∈ Set.Ioo (p k) (q k) ∧ f x = 0 := by
  have hc : ∀ k, ContinuousOn (fun t ↦ s k * f t) (Ioo (β k) (β (k + 1))) := fun k ↦
    (continuous_const.mul hf.continuous).continuousOn
  have hreg : ∀ k < n, s k ≠ 0 → ∀ x ∈ Ioo (β k) (β (k + 1)), s k * f x = 0 →
      DifferentiableAt ℝ (fun t ↦ s k * f t) x ∧ 0 < deriv (fun t ↦ s k * f t) x := by
    intro k hk hs0 x hx h0
    refine ⟨(hf x).const_mul _, ?_⟩
    rw [deriv_const_mul _ (hf x)]
    exact hs k hk x hx ((mul_eq_zero.mp h0).resolve_left hs0)
  have hsk : ∀ k < m, s k ≠ 0 := fun k hk h ↦ by
    have h' := hfp k hk
    rw [h, zero_mul] at h'
    exact lt_irrefl _ h'
  have hpS : ∀ k < m, p k ∈ Ioo (β k) (β (k + 1)) := fun k hk ↦
    ⟨hp k hk, (hpq k hk).trans (hq k hk)⟩
  have hqS : ∀ k < m, q k ∈ Ioo (β k) (β (k + 1)) := fun k hk ↦
    ⟨(hp k hk).trans (hpq k hk), hq k hk⟩
  refine ⟨fun x hx hfx ↦ ?_, fun k hk ↦ ?_⟩
  · have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h] at hx
        exact absurd (hx.1.trans hx.2) (lt_irrefl _)
      · exact h
    have hxn : x < β (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]; exact hx.2
    classical
    have hex : ∃ j, x < β (j + 1) := ⟨n - 1, hxn⟩
    obtain ⟨k, hk1, hkmin⟩ : ∃ k, x < β (k + 1) ∧ ∀ j < k, ¬x < β (j + 1) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj ↦ Nat.find_min hex hj⟩
    have hkn : k < n := by
      by_contra hkn
      exact hkmin (n - 1) (by omega) hxn
    have hk0 : β k < x := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0]
        exact hx.1
      · have hnot := hkmin (k - 1) (by omega)
        rw [Nat.sub_add_cancel hpos, not_lt] at hnot
        refine lt_of_le_of_ne hnot fun h ↦ hβf k hpos hkn ?_
        rw [h]
        exact hfx
    have hxS : x ∈ Ioo (β k) (β (k + 1)) := ⟨hk0, hk1⟩
    have hgx : (fun t ↦ s k * f t) x = 0 := by
      simp only [hfx, mul_zero]
    rcases lt_or_ge k m with hkm | hkm
    · exact ⟨k, hkm, mem_Ioo_of_deriv_pos_at_zeros ordConnected_Ioo (hc k)
        (hreg k hkn (hsk k hkm)) (hpS k hkm) (hqS k hkm) (hfp k hkm) (hfq k hkm) hxS hgx⟩
    · obtain rfl : k = m := by omega
      have hmn' : k + 1 = n := by omega
      subst hmn'
      have hneg := hcut (by omega)
      have hsm : s k ≠ 0 := fun h ↦ by
        rw [h, zero_mul] at hneg
        exact lt_irrefl _ hneg
      have hev : ∀ᶠ t in 𝓝[<] (β (k + 1)), s k * f t < 0 :=
        (((continuous_const.mul hf.continuous).tendsto (β (k + 1))).eventually
          (gt_mem_nhds hneg)).filter_mono nhdsWithin_le_nhds
      have hev2 : ∀ᶠ t in 𝓝[<] (β (k + 1)), x < t :=
        Filter.eventually_of_mem (Ioo_mem_nhdsLT hk1) fun t ht ↦ ht.1
      obtain ⟨t, hgt, hxt, htb⟩ := (hev.and (hev2.and self_mem_nhdsWithin)).exists
      have htS : t ∈ Ioo (β k) (β (k + 1)) := ⟨hk0.trans hxt, htb⟩
      have h := neg_of_le_of_deriv_pos_at_zeros ordConnected_Ioo (hc k) (hreg k hkn hsm) hxS htS
        hxt.le hgt
      exact absurd hgx h.ne
  · have hkn : k < n := lt_of_lt_of_le hk hmn
    have hd := hreg k hkn (hsk k hk)
    have hcpq : ContinuousOn (fun t ↦ s k * f t) (Icc (p k) (q k)) :=
      (continuous_const.mul hf.continuous).continuousOn
    obtain ⟨x, hx, hgx⟩ := intermediate_value_Ioo (hpq k hk).le hcpq ⟨hfp k hk, hfq k hk⟩
    have hfx : f x = 0 := (mul_eq_zero.mp hgx).resolve_left (hsk k hk)
    have hxS : x ∈ Ioo (β k) (β (k + 1)) := ⟨(hp k hk).trans hx.1, hx.2.trans (hq k hk)⟩
    refine ⟨x, ⟨hx, hfx⟩, fun y hy ↦ ?_⟩
    have hyS : y ∈ Ioo (β k) (β (k + 1)) := ⟨(hp k hk).trans hy.1.1, hy.1.2.trans (hq k hk)⟩
    exact eq_of_deriv_pos_at_zeros ordConnected_Ioo (hc k) hd hyS hxS
      (by simp only [hy.2, mul_zero]) hgx

end PDE.Analysis
