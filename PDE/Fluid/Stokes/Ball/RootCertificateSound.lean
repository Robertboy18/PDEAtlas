/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.RootCertificate
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Soundness of the root certificates for `j_l` and the azimuthal roots

The enclosures of the zeros of `j_l` below `100` are certified by induction on `l`, and the
azimuthal roots of degree `l` below `100` from those of `j_l`.

* `jZeroEnclosures_zero_of_pi`: the zeros of `j_0 x = sin x / x` in `(0, 100]` are `k π`,
  `k = 1, …, 31`, so enclosures of these 31 multiples of `π` give `JZeroEnclosures 0`.
* `JZeroEnclosures.succ`: let `z_0 < … < z_{n-1}` be the zeros of `j_l` in `(0, 100]`. Since
  `(x ^ (l + 2) j_{l+1})' = x ^ (l + 2) j_l` and `j_l > 0` on `(0, z_0)`, the function `j_{l+1}`
  has no zero in `(0, z_0]`. On each interval between consecutive zeros of `j_l`, and on
  `(z_{n-1}, 100)`, the function `j_l` has one sign, and at a zero of `j_{l+1}` the derivative
  of `j_{l+1}` is `j_l`. So `j_{l+1}` crosses zero there in one direction only, and the signs
  checked by `chainCheck` at the endpoints of the intervals of `F` and at `100` locate each
  zero of `j_{l+1}` (`mem_Ioo_of_regions`).
* `azimuthal_roots_of_check`: the regions are `(0, z_0)`, the intervals between consecutive
  zeros of `j_l`, and `(z_{n-1}, 100)`. A root `α` of `azimuthalBoundaryJ l` satisfies
  `l (l + 1) < α ^ 2` and `α (azimuthalBoundaryJ l)'(α) = (l (l + 1) - α ^ 2) j_l(α)`, so on each
  region the derivative at a root has the sign of `-j_l`. At a zero `z` of `j_l` the function
  is `-z j_{l+1}(z) ≠ 0`. The signs checked by `azimuthalCheck` then locate every root in
  `(0, 100)` in an interval of `F`, one root in each interval.

The breakpoints `z_k`, followed by `100`, come from `JZeroEnclosures.exists_breakpoints`, and
the signs from `rootPointSigns_sound`. The proofs never reduce `rootPointSigns` or `cutSigns`:
the sign tuples are named by equations `rootPointSigns l n = (a, b, y, z)` first.
-/

@[expose] public section

open Set PDE.Analysis PDE.Analysis.SpecialFunctions

namespace PDE.Fluid.Stokes.Ball

/-! ### Certified signs -/

/-- The signs decided by `rootPointSigns` at a positive dyadic point `x` are the signs of `j_l`,
`j_{l+1}` and `azimuthalBoundaryJ l` at `x`. -/
theorem rootPointSigns_sound_of_eq {l n : ℕ} {a b y z : ℤ}
    (h : rootPointSigns l n = (a, b, y, z)) (hn : 0 < n) {x : ℝ} (hx : (n : ℝ) / 2 ^ 40 = x) :
    (a ≠ 0 → 0 < (a : ℝ) * sphericalBesselJ l x) ∧
      (b ≠ 0 → 0 < (b : ℝ) * sphericalBesselJ (l + 1) x) ∧
      (z ≠ 0 → 0 < (z : ℝ) * azimuthalBoundaryJ l x) := by
  have hs := rootPointSigns_sound l n
  rw [h, hx] at hs
  have hx0 : 0 < x := by rw [← hx]; positivity
  refine ⟨fun ha ↦ ?_, fun hb ↦ ?_, fun hz ↦ ?_⟩
  · rw [sphericalBesselJ_eq_pow_mul, mul_left_comm]
    exact mul_pos (pow_pos hx0 _) (hs.1 ha)
  · rw [sphericalBesselJ_eq_pow_mul, mul_left_comm]
    exact mul_pos (pow_pos hx0 _) (hs.2.1 hb)
  · rw [← pow_mul_boundaryFunction_azimuthal_eq, mul_left_comm]
    exact mul_pos (pow_pos hx0 _) (hs.2.2.2 hz)

/-! ### Breakpoints from the zeros of `j_l` -/

/-- A sequence equal to `f` below `n` and to `c` from `n` on. -/
private theorem exists_seq_eq_of_lt (n : ℕ) (f : ℕ → ℝ) (c : ℝ) :
    ∃ s : ℕ → ℝ, (∀ k < n, s k = f k) ∧ ∀ k, n ≤ k → s k = c :=
  ⟨fun k ↦ if k < n then f k else c, fun _ hk ↦ ite_eq_left hk,
    fun _ hk ↦ ite_eq_right (not_lt.2 hk)⟩

/-- The zeros of `j_l` in the intervals of `E`, followed by the point `100`. -/
theorem JZeroEnclosures.exists_breakpoints {l : ℕ} {E : List (ℕ × ℕ)}
    (hE : JZeroEnclosures l E) :
    ∃ β : ℕ → ℝ, (∀ k < E.length, β k ∈ Ioo (enclosureLo E k) (enclosureHi E k) ∧
      sphericalBesselJ l (β k) = 0) ∧ ∀ k, E.length ≤ k → β k = 100 := by
  choose! z hz using fun k (hk : k < E.length) ↦ (hE.existsUnique k hk).exists
  obtain ⟨β, hβ, hβn⟩ := exists_seq_eq_of_lt E.length z 100
  exact ⟨β, fun k hk ↦ hβ k hk ▸ hz k hk, hβn⟩

/-- The breakpoints of `JZeroEnclosures.exists_breakpoints` increase up to `100`. -/
theorem JZeroEnclosures.breakpoint_lt {l : ℕ} {E : List (ℕ × ℕ)} (hE : JZeroEnclosures l E)
    {β : ℕ → ℝ} (hβ : ∀ k < E.length, β k ∈ Ioo (enclosureLo E k) (enclosureHi E k) ∧
      sphericalBesselJ l (β k) = 0)
    (hβn : ∀ k, E.length ≤ k → β k = 100) {i j : ℕ} (hij : i < j) (hj : j ≤ E.length) :
    β i < β j := by
  have hi : i < E.length := by omega
  rcases hj.lt_or_eq with hj' | hj'
  · exact ((hβ i hi).1.2.trans (enclosureHi_lt_enclosureLo hE.sorted hij hj')).trans
      (hβ j hj').1.1
  · rw [hβn j hj'.ge]
    exact (hβ i hi).1.2.trans (enclosureHi_lt_hundred hE.sorted hi)

/-- Comparing two breakpoints compares their indices. -/
theorem JZeroEnclosures.lt_of_breakpoint_lt {l : ℕ} {E : List (ℕ × ℕ)}
    (hE : JZeroEnclosures l E) {β : ℕ → ℝ}
    (hβ : ∀ k < E.length, β k ∈ Ioo (enclosureLo E k) (enclosureHi E k) ∧
      sphericalBesselJ l (β k) = 0)
    (hβn : ∀ k, E.length ≤ k → β k = 100) {i j : ℕ} (hi : i ≤ E.length) (h : β i < β j) :
    i < j := by
  by_contra hji
  push Not at hji
  rcases hji.lt_or_eq with hji | hji
  · exact absurd h (hE.breakpoint_lt hβ hβn hji hi).not_gt
  · rw [hji] at h
    exact lt_irrefl _ h

/-- The breakpoints are positive. -/
theorem JZeroEnclosures.breakpoint_pos {l : ℕ} {E : List (ℕ × ℕ)} (hE : JZeroEnclosures l E)
    {β : ℕ → ℝ} (hβ : ∀ k < E.length, β k ∈ Ioo (enclosureLo E k) (enclosureHi E k) ∧
      sphericalBesselJ l (β k) = 0)
    (hβn : ∀ k, E.length ≤ k → β k = 100) (k : ℕ) : 0 < β k := by
  rcases lt_or_ge k E.length with hk | hk
  · exact (enclosureLo_pos hE.sorted hk).trans (hβ k hk).1.1
  · rw [hβn k hk]
    norm_num

/-- The breakpoints are at most `100`. -/
theorem JZeroEnclosures.breakpoint_le_hundred {l : ℕ} {E : List (ℕ × ℕ)}
    (hE : JZeroEnclosures l E) {β : ℕ → ℝ}
    (hβ : ∀ k < E.length, β k ∈ Ioo (enclosureLo E k) (enclosureHi E k) ∧
      sphericalBesselJ l (β k) = 0)
    (hβn : ∀ k, E.length ≤ k → β k = 100) (k : ℕ) : β k ≤ 100 := by
  rcases lt_or_ge k E.length with hk | hk
  · exact ((hβ k hk).1.2.trans (enclosureHi_lt_hundred hE.sorted hk)).le
  · rw [hβn k hk]

/-- Every zero of `j_l` in `(0, 100]` is one of the breakpoints. -/
theorem JZeroEnclosures.eq_breakpoint {l : ℕ} {E : List (ℕ × ℕ)} (hE : JZeroEnclosures l E)
    {β : ℕ → ℝ} (hβ : ∀ k < E.length, β k ∈ Ioo (enclosureLo E k) (enclosureHi E k) ∧
      sphericalBesselJ l (β k) = 0) {x : ℝ} (hx : x ∈ Ioc 0 100)
    (h : sphericalBesselJ l x = 0) : ∃ k < E.length, x = β k := by
  obtain ⟨k, hk, hxk⟩ := hE.complete x hx h
  exact ⟨k, hk, (hE.existsUnique k hk).unique ⟨hxk, h⟩ (hβ k hk)⟩

/-- `j_l` has no zero between consecutive breakpoints. -/
theorem JZeroEnclosures.ne_zero_of_mem_Ioo {l : ℕ} {E : List (ℕ × ℕ)}
    (hE : JZeroEnclosures l E) {β : ℕ → ℝ}
    (hβ : ∀ k < E.length, β k ∈ Ioo (enclosureLo E k) (enclosureHi E k) ∧
      sphericalBesselJ l (β k) = 0)
    (hβn : ∀ k, E.length ≤ k → β k = 100) {k : ℕ} (hk : k < E.length) :
    ∀ x ∈ Ioo (β k) (β (k + 1)), sphericalBesselJ l x ≠ 0 := by
  intro x hx h
  have hx0 : 0 < x := (hE.breakpoint_pos hβ hβn k).trans hx.1
  have hx100 : x ≤ 100 := (hx.2.trans_le (hE.breakpoint_le_hundred hβ hβn _)).le
  obtain ⟨j, hj, rfl⟩ := hE.eq_breakpoint hβ ⟨hx0, hx100⟩ h
  have h₁ := hE.lt_of_breakpoint_lt hβ hβn hk.le hx.1
  have h₂ := hE.lt_of_breakpoint_lt hβ hβn hj.le hx.2
  omega

/-- `j_l` has no zero between `0` and the first breakpoint. -/
theorem JZeroEnclosures.ne_zero_of_mem_Ioo_zero {l : ℕ} {E : List (ℕ × ℕ)}
    (hE : JZeroEnclosures l E) {β : ℕ → ℝ}
    (hβ : ∀ k < E.length, β k ∈ Ioo (enclosureLo E k) (enclosureHi E k) ∧
      sphericalBesselJ l (β k) = 0)
    (hβn : ∀ k, E.length ≤ k → β k = 100) :
    ∀ x ∈ Ioo 0 (β 0), sphericalBesselJ l x ≠ 0 := by
  intro x hx h
  have hx100 : x ≤ 100 := (hx.2.trans_le (hE.breakpoint_le_hundred hβ hβn _)).le
  obtain ⟨j, hj, rfl⟩ := hE.eq_breakpoint hβ ⟨hx.1, hx100⟩ h
  have h₂ := hE.lt_of_breakpoint_lt hβ hβn hj.le hx.2
  omega

/-! ### The chain step from `j_l` to `j_{l+1}` -/

/-- The conditions of `chainCheck`, with the signs at `100` written out. -/
theorem chainCheck_spec {l : ℕ} {E F : List (ℕ × ℕ)} (h : chainCheck l E F = true)
    {a b y z : ℤ} (hC : cutSigns l = (a, b, y, z)) :
    enclosuresSorted F = true ∧
    ((E.length = 0 ∧ F.length = 0) ∨
      ((F.length = E.length ∨ F.length + 1 = E.length) ∧
        (∀ k < F.length, (E.getD k (0, 0)).2 ≤ (F.getD k (0, 0)).1 ∧
          (E.length ≤ k + 1 ∨ (F.getD k (0, 0)).2 ≤ (E.getD (k + 1) (0, 0)).1) ∧
          ∀ a₁ b₁ y₁ z₁ a₂ b₂ y₂ z₂ : ℤ,
            rootPointSigns l (F.getD k (0, 0)).1 = (a₁, b₁, y₁, z₁) →
            rootPointSigns l (F.getD k (0, 0)).2 = (a₂, b₂, y₂, z₂) →
            a₁ ≠ 0 ∧ a₂ = a₁ ∧ b₁ = -a₁ ∧ b₂ = a₁) ∧
        a ≠ 0 ∧ b ≠ 0 ∧ (F.length + 1 = E.length → b = -a))) := by
  unfold chainCheck at h
  rw [hC] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, h⟩ := h
  refine ⟨hs, h.imp id fun h' ↦ ⟨h'.1.1, fun k hk ↦ ?_, h'.2⟩⟩
  have hk' := List.all_eq_true.mp h'.1.2 k (List.mem_range.mpr hk)
  beta_reduce at hk'
  rw [Bool.and_eq_true, Bool.and_eq_true] at hk'
  obtain ⟨⟨hk₁, hk₂⟩, hk₃⟩ := hk'
  refine ⟨of_decide_eq_true hk₁, ?_, fun a₁ b₁ y₁ z₁ a₂ b₂ y₂ z₂ h₁ h₂ ↦ ?_⟩
  · rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hk₂
    exact hk₂
  · rw [h₁, h₂] at hk₃
    exact of_decide_eq_true hk₃

/-- The chain step: enclosures of the zeros of `j_l` and a successful `chainCheck` give
enclosures of the zeros of `j_{l+1}`. -/
theorem JZeroEnclosures.succ {l : ℕ} {E F : List (ℕ × ℕ)} (hE : JZeroEnclosures l E)
    (h : chainCheck l E F = true) : JZeroEnclosures (l + 1) F := by
  obtain ⟨⟨ca, cb, cy, cz⟩, hC⟩ : ∃ C, cutSigns l = C := ⟨_, rfl⟩
  obtain ⟨hFs, hcase⟩ := chainCheck_spec h hC
  obtain ⟨β, hβ, hβn⟩ := hE.exists_breakpoints
  have hβ' : ∀ k < E.length, β k ∈ Ioo (enclosureLo E k) (enclosureHi E k) :=
    fun k hk ↦ (hβ k hk).1
  have hβpos := hE.breakpoint_pos hβ hβn
  have hpos0 : ∀ x ∈ Ioc 0 (β 0), 0 < sphericalBesselJ (l + 1) x :=
    sphericalBesselJ_succ_pos_of_forall_pos
      (sphericalBesselJ_pos_of_forall_ne_zero (hE.ne_zero_of_mem_Ioo_zero hβ hβn))
  rcases hcase with ⟨hE0, hF0⟩ | ⟨hlen, hall, hca, hcb, hcab⟩
  · refine ⟨hFs, fun k hk ↦ absurd hk (by omega), fun x hx hx0 ↦ ?_⟩
    rw [hβn 0 (by omega)] at hpos0
    exact absurd hx0 (hpos0 x hx).ne'
  have hFpos : ∀ k < F.length, 0 < (F.getD k (0, 0)).1 := fun k hk ↦
    (enclosuresSorted_spec hFs hk).1
  have hFpos' : ∀ k < F.length, 0 < (F.getD k (0, 0)).2 := fun k hk ↦
    (hFpos k hk).trans (enclosuresSorted_spec hFs hk).2.1
  have hcut0 : 0 < cutNumerator := by unfold cutNumerator; positivity
  obtain ⟨hja100, hjb100, -⟩ := rootPointSigns_sound_of_eq hC hcut0 cutNumerator_div_two_pow_forty
  replace hja100 := hja100 hca
  replace hjb100 := hjb100 hcb
  have hsgn : ∀ k < F.length, ∃ a : ℤ, a ≠ 0 ∧
      0 < (a : ℝ) * sphericalBesselJ l (enclosureLo F k) ∧
      0 < -(a : ℝ) * sphericalBesselJ (l + 1) (enclosureLo F k) ∧
      0 < (a : ℝ) * sphericalBesselJ (l + 1) (enclosureHi F k) := by
    intro k hk
    obtain ⟨⟨a₁, b₁, y₁, z₁⟩, h₁⟩ : ∃ X, rootPointSigns l (F.getD k (0, 0)).1 = X := ⟨_, rfl⟩
    obtain ⟨⟨a₂, b₂, y₂, z₂⟩, h₂⟩ : ∃ X, rootPointSigns l (F.getD k (0, 0)).2 = X := ⟨_, rfl⟩
    obtain ⟨ha0, -, rfl, hb₂⟩ := (hall k hk).2.2 a₁ b₁ y₁ z₁ a₂ b₂ y₂ z₂ h₁ h₂
    subst b₂
    obtain ⟨hl₁, hl₂, -⟩ :=
      rootPointSigns_sound_of_eq h₁ (hFpos k hk) (x := enclosureLo F k) rfl
    obtain ⟨-, hr₂, -⟩ := rootPointSigns_sound_of_eq h₂ (hFpos' k hk) (x := enclosureHi F k) rfl
    exact ⟨a₁, ha0, hl₁ ha0, by exact_mod_cast hl₂ (neg_ne_zero.mpr ha0), hr₂ ha0⟩
  choose! a _ haj hal har using hsgn
  obtain ⟨s, hs_lt, hs_ge⟩ : ∃ s : ℕ → ℝ, (∀ k < F.length, s k = a k) ∧
      ∀ k, F.length ≤ k → s k = ca := exists_seq_eq_of_lt _ _ _
  have hp : ∀ k < F.length, β k < enclosureLo F k := fun k hk ↦
    (hβ' k (by omega)).2.trans_le (natCast_div_two_pow_forty_le (hall k hk).1)
  have hpq : ∀ k < F.length, enclosureLo F k < enclosureHi F k := fun k hk ↦
    enclosureLo_lt_enclosureHi hFs hk
  have hq : ∀ k < F.length, enclosureHi F k < β (k + 1) := by
    intro k hk
    rcases lt_or_ge (k + 1) E.length with h₁ | h₁
    · exact (natCast_div_two_pow_forty_le ((hall k hk).2.1.resolve_left (by omega))).trans_lt
        (hβ' (k + 1) h₁).1
    · rw [hβn (k + 1) h₁]
      exact enclosureHi_lt_hundred hFs hk
  have hsign : ∀ k < E.length, ∀ x ∈ Ioo (β k) (β (k + 1)),
      0 < s k * sphericalBesselJ l x := by
    intro k hk
    rcases lt_or_ge k F.length with hkm | hkm
    · refine pos_mul_of_witness (continuous_sphericalBesselJ l)
        (hE.ne_zero_of_mem_Ioo hβ hβn hk) ⟨hp k hkm, ((hpq k hkm).trans (hq k hkm)).le⟩ ?_
      rw [hs_lt k hkm]
      exact haj k hkm
    · refine pos_mul_of_witness (continuous_sphericalBesselJ l)
        (hE.ne_zero_of_mem_Ioo hβ hβn hk)
        ⟨hE.breakpoint_lt hβ hβn (Nat.lt_succ_self k) (by omega), le_rfl⟩ ?_
      rw [hs_ge k hkm, hβn (k + 1) (by omega)]
      exact hja100
  have hβf : ∀ k, 0 < k → k < E.length → sphericalBesselJ (l + 1) (β k) ≠ 0 :=
    fun k _ hk ↦ sphericalBesselJ_succ_ne_zero_of_eq_zero (hβpos k).ne' (hβ k hk).2
  have hs : ∀ k < E.length, ∀ x ∈ Ioo (β k) (β (k + 1)), sphericalBesselJ (l + 1) x = 0 →
      0 < s k * deriv (sphericalBesselJ (l + 1)) x := by
    intro k hk x hx h0
    rw [deriv_sphericalBesselJ_succ_of_eq_zero ((hβpos k).trans hx.1).ne' h0]
    exact hsign k hk x hx
  have hfp : ∀ k < F.length, s k * sphericalBesselJ (l + 1) (enclosureLo F k) < 0 :=
    fun k hk ↦ by rw [hs_lt k hk]; linarith [hal k hk]
  have hfq : ∀ k < F.length, 0 < s k * sphericalBesselJ (l + 1) (enclosureHi F k) :=
    fun k hk ↦ by rw [hs_lt k hk]; exact har k hk
  have hcut (hlt : F.length < E.length) :
      s F.length * sphericalBesselJ (l + 1) (β E.length) < 0 := by
    rw [hs_ge _ le_rfl, hβn _ le_rfl]
    rw [hcab (by omega)] at hjb100
    push_cast at hjb100
    linarith
  obtain ⟨hA, hB⟩ := mem_Ioo_of_regions (differentiable_sphericalBesselJ (l + 1)) hβf hs
    (by omega) (by omega) hp hpq hq hfp hfq hcut
  refine ⟨hFs, hB, fun x hx hx0 ↦ ?_⟩
  rcases le_or_gt x (β 0) with hxb | hxb
  · exact absurd hx0 (hpos0 x ⟨hx.1, hxb⟩).ne'
  rcases hx.2.eq_or_lt with hx100 | hx100
  · rw [← hx100, hx0, mul_zero] at hjb100
    exact absurd hjb100 (lt_irrefl _)
  · exact hA x ⟨hxb, by rw [hβn E.length le_rfl]; exact hx100⟩ hx0

/-! ### The zeros of `j_0` -/

/-- A zero of `j_0` in `(0, 100]` is `(k + 1) π` with `k < 31`. -/
theorem exists_eq_mul_pi_of_sphericalBesselJ_zero {x : ℝ} (hx : x ∈ Ioc 0 100)
    (h : sphericalBesselJ 0 x = 0) : ∃ k : ℕ, k < 31 ∧ x = (k + 1) * Real.pi := by
  have hsin : Real.sin x = 0 := by rw [← mul_sphericalBesselJ_zero, h, mul_zero]
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hpi : (314 / 100 : ℝ) < Real.pi := by
    have := Real.pi_gt_d2
    norm_num at this ⊢
    linarith
  have hn0 : 0 < n := by
    by_contra hneg
    push Not at hneg
    have h₁ : (n : ℝ) ≤ 0 := by exact_mod_cast hneg
    have h₂ := mul_nonpos_of_nonpos_of_nonneg h₁ Real.pi_pos.le
    linarith [hx.1]
  have hn31 : n ≤ 31 := by
    by_contra hbig
    push Not at hbig
    have h₁ : (32 : ℝ) ≤ n := by exact_mod_cast hbig
    have h₂ := mul_le_mul_of_nonneg_right h₁ Real.pi_pos.le
    linarith [hx.2]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨(n - 1).toNat, by omega⟩
  refine ⟨k, by omega, ?_⟩
  rw [← hn]
  push_cast
  ring

/-- The zeros `k π`, `k = 1, …, 31`, of `j_0` below `100`: a sorted list of 31 entries whose
entry `k` encloses `(k + 1) π` through the bounds `3.14159265358979323846 < π <
3.14159265358979323847` gives `JZeroEnclosures 0`. -/
theorem jZeroEnclosures_zero_of_pi {E : List (ℕ × ℕ)} (hs : enclosuresSorted E = true)
    (hlen : E.length = 31)
    (hpi : ∀ k < 31, ((E.getD k (0, 0)).1 : ℚ) <
        ((k : ℚ) + 1) * (314159265358979323846 / 10 ^ 20) * 2 ^ 40 ∧
      ((k : ℚ) + 1) * (314159265358979323847 / 10 ^ 20) * 2 ^ 40 < ((E.getD k (0, 0)).2 : ℚ)) :
    JZeroEnclosures 0 E := by
  have hlo : (314159265358979323846 / 10 ^ 20 : ℝ) < Real.pi :=
    lt_of_eq_of_lt (by norm_num) Real.pi_gt_d20
  have hhi : Real.pi < (314159265358979323847 / 10 ^ 20 : ℝ) :=
    lt_of_lt_of_eq Real.pi_lt_d20 (by norm_num)
  have hmem : ∀ k < 31, ((k : ℝ) + 1) * Real.pi ∈ Ioo (enclosureLo E k) (enclosureHi E k) := by
    intro k hk
    have h₁ := (Rat.cast_lt (K := ℝ)).mpr (hpi k hk).1
    have h₂ := (Rat.cast_lt (K := ℝ)).mpr (hpi k hk).2
    push_cast at h₁ h₂
    have hk0 : (0 : ℝ) < k + 1 := by positivity
    constructor
    · rw [enclosureLo, div_lt_iff₀ (by positivity)]
      linarith [mul_pos hk0 (sub_pos.mpr hlo)]
    · rw [enclosureHi, lt_div_iff₀ (by positivity)]
      linarith [mul_pos hk0 (sub_pos.mpr hhi)]
  have hzero : ∀ k : ℕ, sphericalBesselJ 0 (((k : ℝ) + 1) * Real.pi) = 0 := by
    intro k
    have hne : ((k : ℝ) + 1) * Real.pi ≠ 0 := by positivity
    rw [sphericalBesselJ_zero_eq hne, div_eq_zero_iff]
    left
    exact_mod_cast Real.sin_nat_mul_pi (k + 1)
  refine ⟨hs, fun k hk ↦ ⟨((k : ℝ) + 1) * Real.pi, ⟨hmem k (by omega), hzero k⟩, ?_⟩,
    fun x hx h ↦ ?_⟩
  · rintro y ⟨hy, hy0⟩
    have hy' : y ∈ Ioc 0 100 :=
      ⟨(enclosureLo_pos hs hk).trans hy.1, (hy.2.trans (enclosureHi_lt_hundred hs hk)).le⟩
    obtain ⟨j, hj, rfl⟩ := exists_eq_mul_pi_of_sphericalBesselJ_zero hy' hy0
    rw [eq_of_mem_enclosure hs (by omega) hk (hmem j hj) hy]
  · obtain ⟨j, hj, rfl⟩ := exists_eq_mul_pi_of_sphericalBesselJ_zero hx h
    exact ⟨j, by omega, hmem j hj⟩

/-! ### The azimuthal roots -/

/-- The conditions of `azimuthalCheck`, with the signs at `100` written out. -/
theorem azimuthalCheck_spec {l : ℕ} {E F : List (ℕ × ℕ)} (h : azimuthalCheck l E F = true)
    {a b y z : ℤ} (hC : cutSigns l = (a, b, y, z)) :
    enclosuresSorted F = true ∧ (F.length = E.length ∨ F.length = E.length + 1) ∧
      (∀ k < F.length, (k = 0 ∨ (E.getD (k - 1) (0, 0)).2 ≤ (F.getD k (0, 0)).1) ∧
        (E.length ≤ k ∨ (F.getD k (0, 0)).2 ≤ (E.getD k (0, 0)).1) ∧
        ∀ a₁ b₁ y₁ z₁ a₂ b₂ y₂ z₂ : ℤ,
          rootPointSigns l (F.getD k (0, 0)).1 = (a₁, b₁, y₁, z₁) →
          rootPointSigns l (F.getD k (0, 0)).2 = (a₂, b₂, y₂, z₂) →
          a₁ ≠ 0 ∧ a₂ = a₁ ∧ z₁ = a₁ ∧ z₂ = -a₁) ∧
      a ≠ 0 ∧ z ≠ 0 ∧ (F.length = E.length → z = a) := by
  unfold azimuthalCheck at h
  rw [hC] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hs, hlen⟩, hall⟩, hcut⟩ := h
  refine ⟨hs, hlen, fun k hk ↦ ?_, hcut⟩
  have hk' := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
  beta_reduce at hk'
  rw [Bool.and_eq_true, Bool.and_eq_true] at hk'
  obtain ⟨⟨hk₁, hk₂⟩, hk₃⟩ := hk'
  refine ⟨?_, ?_, fun a₁ b₁ y₁ z₁ a₂ b₂ y₂ z₂ h₁ h₂ ↦ ?_⟩
  · rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hk₁
    exact hk₁
  · rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hk₂
    exact hk₂
  · rw [h₁, h₂] at hk₃
    exact of_decide_eq_true hk₃

/-- The azimuthal roots below `100` from the zeros of `j_l` and a successful `azimuthalCheck`:
every root in `(0, 100)` lies in an interval of `F`, and each interval of `F` contains exactly
one root. -/
theorem azimuthal_roots_of_check {l : ℕ} {E F : List (ℕ × ℕ)} (hE : JZeroEnclosures l E)
    (h : azimuthalCheck l E F = true) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 100, boundaryFunction .azimuthal l α = 0 →
      ∃ k < F.length, α ∈ Set.Ioo (enclosureLo F k) (enclosureHi F k)) ∧
    ∀ k < F.length, ∃! α, α ∈ Set.Ioo (enclosureLo F k) (enclosureHi F k) ∧
      boundaryFunction .azimuthal l α = 0 := by
  obtain ⟨⟨ca, cb, cy, cz⟩, hC⟩ : ∃ C, cutSigns l = C := ⟨_, rfl⟩
  obtain ⟨hFs, hlen, hall, hca, hcz, hcza⟩ := azimuthalCheck_spec h hC
  obtain ⟨β, hβ, hβn⟩ := hE.exists_breakpoints
  have hβ' : ∀ k < E.length, β k ∈ Ioo (enclosureLo E k) (enclosureHi E k) :=
    fun k hk ↦ (hβ k hk).1
  have hβpos := hE.breakpoint_pos hβ hβn
  have hFpos : ∀ k < F.length, 0 < (F.getD k (0, 0)).1 := fun k hk ↦
    (enclosuresSorted_spec hFs hk).1
  have hFpos' : ∀ k < F.length, 0 < (F.getD k (0, 0)).2 := fun k hk ↦
    (hFpos k hk).trans (enclosuresSorted_spec hFs hk).2.1
  have hcut0 : 0 < cutNumerator := by unfold cutNumerator; positivity
  obtain ⟨hja100, -, hza100⟩ := rootPointSigns_sound_of_eq hC hcut0 cutNumerator_div_two_pow_forty
  replace hja100 := hja100 hca
  replace hza100 := hza100 hcz
  have hsgn : ∀ k < F.length, ∃ a : ℤ, 0 < (a : ℝ) * sphericalBesselJ l (enclosureLo F k) ∧
      0 < (a : ℝ) * azimuthalBoundaryJ l (enclosureLo F k) ∧
      0 < -(a : ℝ) * azimuthalBoundaryJ l (enclosureHi F k) := by
    intro k hk
    obtain ⟨⟨a₁, b₁, y₁, z₁⟩, h₁⟩ : ∃ X, rootPointSigns l (F.getD k (0, 0)).1 = X := ⟨_, rfl⟩
    obtain ⟨⟨a₂, b₂, y₂, z₂⟩, h₂⟩ : ∃ X, rootPointSigns l (F.getD k (0, 0)).2 = X := ⟨_, rfl⟩
    obtain ⟨ha0, -, hz₁, rfl⟩ := (hall k hk).2.2 a₁ b₁ y₁ z₁ a₂ b₂ y₂ z₂ h₁ h₂
    subst z₁
    obtain ⟨hl₁, -, hl₃⟩ :=
      rootPointSigns_sound_of_eq h₁ (hFpos k hk) (x := enclosureLo F k) rfl
    obtain ⟨-, -, hr₃⟩ := rootPointSigns_sound_of_eq h₂ (hFpos' k hk) (x := enclosureHi F k) rfl
    exact ⟨a₁, hl₁ ha0, hl₃ ha0, by exact_mod_cast hr₃ (neg_ne_zero.mpr ha0)⟩
  choose! a haj haz har using hsgn
  obtain ⟨γ, hγ0, hγs⟩ : ∃ γ : ℕ → ℝ, γ 0 = 0 ∧ ∀ k, γ (k + 1) = β k :=
    ⟨fun k ↦ if k = 0 then 0 else β (k - 1), by simp, fun k ↦ by simp⟩
  obtain ⟨t, ht_lt, ht_ge⟩ : ∃ t : ℕ → ℝ, (∀ k < F.length, t k = a k) ∧
      ∀ k, F.length ≤ k → t k = ca := exists_seq_eq_of_lt _ _ _
  have hγnn : ∀ k, 0 ≤ γ k
    | 0 => hγ0.ge
    | j + 1 => (hβpos j).le.trans (hγs j).ge
  have hγlt : ∀ k ≤ E.length, γ k < γ (k + 1)
    | 0, _ => by rw [hγ0, hγs]; exact hβpos 0
    | j + 1, hk => by rw [hγs, hγs]; exact hE.breakpoint_lt hβ hβn (Nat.lt_succ_self j) hk
  have hne : ∀ k < E.length + 1, ∀ x ∈ Ioo (γ k) (γ (k + 1)), sphericalBesselJ l x ≠ 0
    | 0, _ => by rw [hγ0, hγs]; exact hE.ne_zero_of_mem_Ioo_zero hβ hβn
    | j + 1, hk => by rw [hγs, hγs]; exact hE.ne_zero_of_mem_Ioo hβ hβn (by omega)
  have hp : ∀ k < F.length, γ k < enclosureLo F k
    | 0, hk => hγ0 ▸ enclosureLo_pos hFs hk
    | j + 1, hk => by
      have h₁ := (hall (j + 1) hk).1.resolve_left j.succ_ne_zero
      rw [Nat.add_sub_cancel] at h₁
      exact hγs j ▸ (hβ' j (by omega)).2.trans_le (natCast_div_two_pow_forty_le h₁)
  have hpq : ∀ k < F.length, enclosureLo F k < enclosureHi F k := fun k hk ↦
    enclosureLo_lt_enclosureHi hFs hk
  have hq : ∀ k < F.length, enclosureHi F k < γ (k + 1) := by
    intro k hk
    rw [hγs]
    rcases lt_or_ge k E.length with h₁ | h₁
    · exact (natCast_div_two_pow_forty_le ((hall k hk).2.1.resolve_left (by omega))).trans_lt
        (hβ' k h₁).1
    · rw [hβn k h₁]
      exact enclosureHi_lt_hundred hFs hk
  have hsign : ∀ k < E.length + 1, ∀ x ∈ Ioo (γ k) (γ (k + 1)),
      0 < t k * sphericalBesselJ l x := by
    intro k hk
    rcases lt_or_ge k F.length with hkm | hkm
    · refine pos_mul_of_witness (continuous_sphericalBesselJ l) (hne k hk)
        ⟨hp k hkm, ((hpq k hkm).trans (hq k hkm)).le⟩ ?_
      rw [ht_lt k hkm]
      exact haj k hkm
    · refine pos_mul_of_witness (continuous_sphericalBesselJ l) (hne k hk)
        ⟨hγlt k (by omega), le_rfl⟩ ?_
      rw [ht_ge k hkm, hγs, hβn k (by omega)]
      exact hja100
  have hβf : ∀ k, 0 < k → k < E.length + 1 → azimuthalBoundaryJ l (γ k) ≠ 0
    | j + 1, _, hk => by
      have h₀ := (hβ j (by omega)).2
      rw [hγs, azimuthalBoundaryJ, h₀, mul_zero, zero_sub, neg_ne_zero]
      exact mul_ne_zero (hβpos j).ne' (sphericalBesselJ_succ_ne_zero_of_eq_zero (hβpos j).ne' h₀)
  have hs : ∀ k < E.length + 1, ∀ x ∈ Ioo (γ k) (γ (k + 1)), azimuthalBoundaryJ l x = 0 →
      0 < -t k * deriv (azimuthalBoundaryJ l) x := by
    intro k hk x hx h₀
    have hx0 : 0 < x := (hγnn k).trans_lt hx.1
    have hpos := mul_pos (sub_pos.2 (lt_sq_of_azimuthalBoundaryJ_eq_zero hx0 h₀))
      (hsign k hk x hx)
    refine pos_of_mul_pos_left (?_ : 0 < _ * x) hx0.le
    linear_combination hpos + t k * deriv_azimuthalBoundaryJ_mul_of_eq_zero hx0.ne' h₀
  have hfp : ∀ k < F.length, -t k * azimuthalBoundaryJ l (enclosureLo F k) < 0 :=
    fun k hk ↦ by rw [ht_lt k hk]; linarith [haz k hk]
  have hfq : ∀ k < F.length, 0 < -t k * azimuthalBoundaryJ l (enclosureHi F k) :=
    fun k hk ↦ by rw [ht_lt k hk]; exact har k hk
  have hγend : γ (E.length + 1) = 100 := by rw [hγs, hβn _ le_rfl]
  have hcut (hlt : F.length < E.length + 1) :
      -t F.length * azimuthalBoundaryJ l (γ (E.length + 1)) < 0 := by
    rw [ht_ge _ le_rfl, hγend]
    rw [hcza (by omega)] at hza100
    linarith
  obtain ⟨hA, hB⟩ := mem_Ioo_of_regions (s := fun k ↦ -t k)
    (differentiable_azimuthalBoundaryJ l) hβf hs (by omega) (by omega) hp hpq hq hfp hfq hcut
  refine ⟨fun α hα h₀ ↦ hA α ?_ ((boundaryFunction_azimuthal_eq_zero_iff hα.1).mp h₀),
    fun k hk ↦ ?_⟩
  · rw [hγ0, hγend]
    exact hα
  · obtain ⟨x, ⟨hx, hx0⟩, huniq⟩ := hB k hk
    have hpos : ∀ y ∈ Ioo (enclosureLo F k) (enclosureHi F k), 0 < y := fun y hy ↦
      (enclosureLo_pos hFs hk).trans hy.1
    refine ⟨x, ⟨hx, (boundaryFunction_azimuthal_eq_zero_iff (hpos x hx)).mpr hx0⟩,
      fun y hy ↦ huniq y ⟨hy.1, (boundaryFunction_azimuthal_eq_zero_iff (hpos y hy.1)).mp hy.2⟩⟩

end PDE.Fluid.Stokes.Ball
