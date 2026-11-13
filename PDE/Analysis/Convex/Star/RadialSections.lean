/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Star
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Radial intervals between star-convex sets

A ray through a point between a closed inner set and a bounded open outer set has
finite endpoints on the two frontiers. Both sets are star-convex about the origin.
The inner endpoint is allowed to be the origin; neither an interior assumption
at the origin nor connectedness of the difference is needed.
-/

@[expose] public section

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K W : Set E} {x : E}

/-- The positive ray through an annular point meets the two frontiers, with the
whole intervening interval in the difference. The inner endpoint may be zero. -/
theorem StarConvex.exists_radial_frontier_interval
    (hK : StarConvex ℝ 0 K) (hW : StarConvex ℝ 0 W)
    (hKclosed : IsClosed K) (hWopen : IsOpen W)
    (hWbdd : Bornology.IsBounded W) (hKW : K ⊆ W) (hKne : K.Nonempty)
    (hx : x ∈ W \ K) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < 1 ∧ 1 < b ∧
      a • x ∈ frontier K ∧ b • x ∈ frontier W ∧
      ∀ t ∈ Ioo a b, t • x ∈ W \ K := by
  have hzero : (0 : E) ∈ K := hK.mem hKne
  have hx0 : x ≠ 0 := fun h ↦ hx.2 (h ▸ hzero)
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hcont : Continuous (fun t : ℝ ↦ t • x) := continuous_id.smul continuous_const
  let A : Set ℝ := {t | 0 ≤ t ∧ t • x ∈ K}
  let B : Set ℝ := {t | 0 ≤ t ∧ t • x ∈ W}
  have hA0 : (0 : ℝ) ∈ A := ⟨le_rfl, by simpa using hzero⟩
  have hB1 : (1 : ℝ) ∈ B := ⟨zero_le_one, by simpa using hx.1⟩
  have hAB : A ⊆ B := fun _ ht ↦ ⟨ht.1, hKW ht.2⟩
  obtain ⟨R, hR⟩ := hWbdd.exists_norm_le
  have hBbdd : BddAbove B := by
    refine ⟨R / ‖x‖, fun t ht ↦ ?_⟩
    rw [le_div_iff₀ hnorm]
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] using hR _ ht.2
  have hAbdd : BddAbove A := hBbdd.mono hAB
  let a := sSup A
  let b := sSup B
  have ha0 : 0 ≤ a := le_csSup hAbdd hA0
  have hb1 : 1 ≤ b := le_csSup hBbdd hB1
  have hAclosed : IsClosed A := isClosed_Ici.inter (hKclosed.preimage hcont)
  have haA : a ∈ A := hAclosed.csSup_mem ⟨0, hA0⟩ hAbdd
  have houtsideK : ∀ t, a < t → t • x ∉ K := by
    intro t ht hmem
    exact (not_le_of_gt ht) (le_csSup hAbdd ⟨ha0.trans ht.le, hmem⟩)
  have ha1 : a < 1 := by
    by_contra! ha
    have hin : (a⁻¹ : ℝ) • (a • x) ∈ K :=
      hK.smul_mem haA.2 (inv_nonneg.mpr (zero_le_one.trans ha))
        (inv_le_one_of_one_le₀ ha)
    exact hx.2 (by simpa [smul_smul, (zero_lt_one.trans_le ha).ne'] using hin)
  have hbnot : b • x ∉ W := by
    intro hmem
    obtain ⟨l, r, hbr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      ((hWopen.preimage hcont).mem_nhds hmem)
    obtain ⟨t, hbt, htr⟩ := exists_between hbr.2
    have htB : t ∈ B := ⟨(zero_le_one.trans hb1).trans hbt.le,
      hsub ⟨hbr.1.trans hbt, htr⟩⟩
    exact (not_le_of_gt hbt) (le_csSup hBbdd htB)
  have hb1lt : 1 < b := lt_of_le_of_ne hb1 (by
    intro h
    apply hbnot
    simpa [← h] using hx.1)
  have hbin : b • x ∈ closure W :=
    map_mem_closure (f := fun t : ℝ ↦ t • x) hcont
      (csSup_mem_closure ⟨1, hB1⟩ hBbdd)
      (fun _ ht ↦ ht.2)
  have hain : a • x ∈ frontier K := by
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure haA.2, ?_⟩
    apply map_mem_closure hcont (s := Ioi a)
    · rw [closure_Ioi]
      exact le_rfl
    · exact fun t ht ↦ houtsideK t ht
  refine ⟨a, b, ha0, ha1, hb1lt, hain, ⟨hbin, ?_⟩, ?_⟩
  · simpa [hWopen.interior_eq] using hbnot
  · intro t ht
    obtain ⟨r, hrB, htr⟩ := exists_lt_of_lt_csSup ⟨1, hB1⟩ ht.2
    have ht0 : 0 ≤ t := ha0.trans ht.1.le
    have hr0 : 0 < r := lt_of_le_of_lt ht0 htr
    have htrW : (t / r) • (r • x) ∈ W :=
      hW.smul_mem hrB.2 (div_nonneg ht0 hr0.le) ((div_le_one hr0).mpr htr.le)
    refine ⟨?_, houtsideK t ht.1⟩
    simpa [smul_smul, div_mul_cancel₀ _ hr0.ne'] using htrW
