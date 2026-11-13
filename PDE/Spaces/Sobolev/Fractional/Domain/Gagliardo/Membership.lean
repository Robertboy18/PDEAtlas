/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Gagliardo.HalfSpace
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Gagliardo.Identification
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Gagliardo membership of restrictions of `H^s` functions

For `0 < s < 1` and every set `Ω`, a real function that is the restriction to `Ω` of a real
function in `H^s(ℝ^n)` satisfies the Gagliardo condition on `Ω`. The proof realizes the
restriction class in `W^{s,2}(Ω)` through `HsRestrictionSpace.toGagliardoCLM`.

On `ℝ^n` and on the upper half-space `ℝ^n₊` the two conditions are equivalent. On `ℝ^n` this
follows from `memGagliardo_univ_iff_exists_hsSpaceReal`, and on `ℝ^n₊` from the even reflection
equivalence `GagliardoSpace.halfSpaceEquivHsRestrictionSpace`. A smooth bump gives a real
function with positive and finite Gagliardo seminorm on `ℝ^n₊`.
-/

@[expose] public section

noncomputable section

open scoped FractionalSobolev

open MeasureTheory SobolevSpace.HalfSpace

namespace SobolevSpace.Fractional

variable {n : ℕ} {s : ℝ} {Ω : Set (ℝ^n)}

/-- For `0 < s < 1` and every set `Ω`, the restriction to `Ω` of a real function in
`H^s(ℝ^n)` satisfies the Gagliardo condition on `Ω`. -/
theorem memGagliardo_of_memHsRestriction (hs0 : 0 < s) (hs1 : s < 1) {f : ℝ^n → ℝ}
    (hf : MemHsRestriction n s hs0.le Ω f) : MemGagliardo n s Ω f := by
  rw [memHsRestriction_iff_exists_toLp] at hf
  rw [GagliardoSpace.memGagliardo_iff_exists_gagliardoSpace]
  obtain ⟨q, hq⟩ := hf
  refine ⟨HsRestrictionSpace.toGagliardoCLM hs0 hs1 Ω q, ?_⟩
  simpa only [HsRestrictionSpace.toLp_toGagliardoCLM] using hq

/-- The submodule form of `memGagliardo_of_memHsRestriction`. -/
theorem hsRestrictionSubmodule_le_gagliardoSubmodule (hs0 : 0 < s) (hs1 : s < 1)
    (Ω : Set (ℝ^n)) :
    hsRestrictionSubmodule n s hs0.le Ω ≤ gagliardoSubmodule n s Ω :=
  fun _ hf ↦ memGagliardo_of_memHsRestriction hs0 hs1 hf

/-- For `0 < s < 1`, a real function satisfies the Gagliardo condition on `ℝ^n` if and only
if it agrees almost everywhere with a real function in `H^s(ℝ^n)`. -/
theorem memGagliardo_univ_iff_memHsRestriction (hs0 : 0 < s) (hs1 : s < 1) (f : ℝ^n → ℝ) :
    MemGagliardo n s Set.univ f ↔ MemHsRestriction n s hs0.le Set.univ f := by
  refine ⟨fun hf ↦ ?_, memGagliardo_of_memHsRestriction hs0 hs1⟩
  obtain ⟨u, hu⟩ := (memGagliardo_univ_iff_exists_hsSpaceReal hs0 hs1 f).1 hf
  refine ⟨u, ?_⟩
  rw [Measure.restrict_univ]
  filter_upwards [hu] with x hx
  simpa [reOfL2] using congrArg Complex.re hx.symm

/-- The submodule form of `memGagliardo_univ_iff_memHsRestriction`. -/
theorem gagliardoSubmodule_univ_eq_hsRestrictionSubmodule (hs0 : 0 < s) (hs1 : s < 1) :
    gagliardoSubmodule n s Set.univ = hsRestrictionSubmodule n s hs0.le Set.univ :=
  SetLike.ext fun f ↦ memGagliardo_univ_iff_memHsRestriction hs0 hs1 f

/-- For `1 ≤ n` and `0 < s < 1`, some non-constant real function on `ℝ^n` satisfies both the
Gagliardo condition and the restriction condition on `ℝ^n`, with positive and finite
Gagliardo seminorm. -/
theorem exists_nonconstant_memHsRestriction_univ (hn : 1 ≤ n) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ v : ℝ^n → ℝ, (∃ x y : ℝ^n, v x ≠ v y) ∧
      MemGagliardo n s Set.univ v ∧ MemHsRestriction n s hs0.le Set.univ v ∧
      0 < gagliardoSq n s Set.univ v ∧ gagliardoSq n s Set.univ v < ⊤ := by
  obtain ⟨v, hne, hv, hpos, hfin⟩ := exists_nonconstant_memGagliardo_univ hn hs0 hs1
  exact ⟨v, hne, hv, (memGagliardo_univ_iff_memHsRestriction hs0 hs1 v).1 hv, hpos, hfin⟩

section HalfSpace

variable [Fact (0 < n)]

/-- For `0 < s < 1`, a real function satisfying the Gagliardo condition on the upper
half-space is the restriction to it of a real function in `H^s(ℝ^n)`. -/
theorem memHsRestriction_of_memGagliardo_upper (hs0 : 0 < s) (hs1 : s < 1) {f : ℝ^n → ℝ}
    (hf : MemGagliardo n s ℝ^n₊ f) : MemHsRestriction n s hs0.le ℝ^n₊ f := by
  rw [GagliardoSpace.memGagliardo_iff_exists_gagliardoSpace] at hf
  rw [memHsRestriction_iff_exists_toLp]
  obtain ⟨u, hu⟩ := hf
  refine ⟨GagliardoSpace.halfSpaceEquivHsRestrictionSpace hs0 hs1 u, ?_⟩
  simpa only [GagliardoSpace.toLp_halfSpaceEquivHsRestrictionSpace] using hu

/-- For `0 < s < 1`, a real function satisfies the Gagliardo condition on the upper
half-space if and only if it is the restriction to it of a real function in `H^s(ℝ^n)`. -/
theorem memGagliardo_upper_iff_memHsRestriction (hs0 : 0 < s) (hs1 : s < 1) (f : ℝ^n → ℝ) :
    MemGagliardo n s ℝ^n₊ f ↔ MemHsRestriction n s hs0.le ℝ^n₊ f :=
  ⟨memHsRestriction_of_memGagliardo_upper hs0 hs1, memGagliardo_of_memHsRestriction hs0 hs1⟩

/-- The submodule form of `memGagliardo_upper_iff_memHsRestriction`. -/
theorem gagliardoSubmodule_upper_eq_hsRestrictionSubmodule (hs0 : 0 < s) (hs1 : s < 1) :
    gagliardoSubmodule n s ℝ^n₊ = hsRestrictionSubmodule n s hs0.le ℝ^n₊ :=
  SetLike.ext fun f ↦ memGagliardo_upper_iff_memHsRestriction hs0 hs1 f

/-- For `0 < s < 1`, some real function satisfies the Gagliardo condition on the upper
half-space with positive and finite Gagliardo seminorm there. -/
theorem exists_gagliardoSq_upper_pos_lt_top (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ v : ℝ^n → ℝ, MemGagliardo n s ℝ^n₊ v ∧
      0 < gagliardoSq n s ℝ^n₊ v ∧ gagliardoSq n s ℝ^n₊ v < ⊤ := by
  obtain ⟨f, hrIn, hrOut⟩ : ∃ f : ContDiffBump (0 : ℝ^n), f.rIn = 1 ∧ f.rOut = 2 :=
    ⟨⟨1, 2, by norm_num, by norm_num⟩, rfl, rfl⟩
  set a : ℝ^n := EuclideanSpace.single (PDE.Common.lastIndex (n := n)) (1 / 2 : ℝ) with ha
  set b : ℝ^n := EuclideanSpace.single (PDE.Common.lastIndex (n := n)) (3 : ℝ) with hb
  have haU : a ∈ ℝ^n₊ := by simp [upper, ha]
  have hbU : b ∈ ℝ^n₊ := by simp [upper, hb]
  have hfa : f a = 1 := by
    refine f.one_of_mem_closedBall ?_
    rw [mem_closedBall_zero_iff, ha, PiLp.norm_single, hrIn]
    norm_num
  have hfb : f b = 0 := by
    refine f.zero_of_le_dist ?_
    rw [dist_zero_right, hb, PiLp.norm_single, hrOut]
    norm_num
  have hne : (f : ℝ^n → ℝ) a ≠ (f : ℝ^n → ℝ) b := by
    rw [hfa, hfb]
    norm_num
  have hcs := f.hasCompactSupport
  refine ⟨(f : ℝ^n → ℝ), ?_, ?_, ?_⟩
  · exact MemGagliardo.mono (Set.subset_univ _)
      (memGagliardo_univ_of_hasCompactSupport hs0 hs1 hcs f.contDiff)
  · exact gagliardoSq_pos_of_isOpen (isOpen_upper n) f.continuous haU hbU hne
  · exact lt_of_le_of_lt (gagliardoSq_mono (Set.subset_univ _) _)
      (gagliardoSq_univ_lt_top_of_hasCompactSupport hs0 hs1 hcs f.contDiff)

end HalfSpace

end SobolevSpace.Fractional
