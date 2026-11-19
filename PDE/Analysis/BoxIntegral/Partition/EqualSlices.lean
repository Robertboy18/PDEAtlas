/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.BoxIntegral.Partition.Basic

/-!
# Equal slices in one coordinate

A box admits a partition into any positive number of equal slices
in a selected coordinate. Every other interval stays unchanged. The half-open
convention assigns each dividing face to the slice immediately below it.
-/

@[expose] public noncomputable section

namespace BoxIntegral.Prepartition

open Set Function

variable {ι : Type*}

/-- Partition one coordinate into `N` equal intervals while preserving all
other coordinate intervals. No finiteness assumption on the coordinate type
is needed for this finite partition. -/
theorem exists_equal_coordinate_partition (I : Box ι) (j : ι)
    {N : ℕ} (hN : 0 < N) :
    ∃ π : Prepartition I, π.IsPartition ∧
      ∀ J ∈ π, J.upper j - J.lower j = (I.upper j - I.lower j) / N ∧
        ∀ i, i ≠ j → J.lower i = I.lower i ∧ J.upper i = I.upper i := by
  classical
  let h := (I.upper j - I.lower j) / (N : ℝ)
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hh : 0 < h := div_pos (sub_pos.mpr (I.lower_lt_upper j)) hNreal
  have hwidth : (N : ℝ) * h = I.upper j - I.lower j := mul_div_cancel₀ _ hNreal.ne'
  let J : Fin N → Box ι := fun k ↦
    { lower := update I.lower j (I.lower j + (k : ℝ) * h)
      upper := update I.upper j (I.lower j + ((k : ℝ) + 1) * h)
      lower_lt_upper := fun i ↦ by
        rcases eq_or_ne i j with rfl | hij
        · simp only [update_self]
          linarith
        · simpa only [update_of_ne hij] using I.lower_lt_upper i }
  have hJI (k : Fin N) : J k ≤ I := by
    have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast k.isLt
    refine Box.le_iff_bounds.mpr ⟨le_update_iff.2 ⟨?_, fun _ _ ↦ le_rfl⟩,
      update_le_iff.2 ⟨?_, fun _ _ ↦ le_rfl⟩⟩
    · exact le_add_of_nonneg_right (by positivity)
    · linarith only [hwidth, mul_le_mul_of_nonneg_right hkN hh.le]
  have hdisjoint {k l : Fin N} (hkl : k < l) : Disjoint (J k : Set (ι → ℝ)) (J l) :=
    disjoint_left.mpr fun x hx hy ↦ by
      have hindex : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
      have hxj := (hx j).2
      have hyj := (hy j).1
      simp only [J, update_self] at hxj hyj
      linarith only [hxj, hyj, mul_le_mul_of_nonneg_right hindex hh.le]
  let π : Prepartition I :=
    { boxes := Finset.univ.image J
      le_of_mem' := Finset.forall_mem_image.2 fun k _ ↦ hJI k
      pairwiseDisjoint := by
        rintro _ hK _ hL hne
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hK
        obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hL
        rcases lt_or_gt_of_ne (fun h ↦ hne (congrArg J h) : k ≠ l) with hlt | hgt
        exacts [hdisjoint hlt, (hdisjoint hgt).symm] }
  refine ⟨π, fun x hx ↦ ?_, Finset.forall_mem_image.2 fun k _ ↦ ⟨?_, fun i hij ↦ ?_⟩⟩
  · let q := (x j - I.lower j) / h
    have hq : 0 < q := div_pos (sub_pos.mpr (hx j).1) hh
    have hqN : q ≤ N := (div_le_iff₀ hh).mpr (by linarith only [(hx j).2, hwidth])
    have hcpos : 0 < ⌈q⌉₊ := Nat.ceil_pos.mpr hq
    let k : Fin N := ⟨⌈q⌉₊ - 1, by have := Nat.ceil_le.mpr hqN; omega⟩
    have hkc : (k : ℝ) + 1 = (⌈q⌉₊ : ℝ) := by exact_mod_cast Nat.sub_add_cancel hcpos
    have hlo := (lt_div_iff₀ hh).mp
      (by linarith only [hkc, Nat.ceil_lt_add_one hq.le] : (k : ℝ) < q)
    have hhi := (div_le_iff₀ hh).mp (Nat.le_ceil q)
    refine ⟨J k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, fun i ↦ ?_⟩
    rcases eq_or_ne i j with rfl | hij
    · simp only [J, update_self, mem_Ioc]
      rw [← hkc] at hhi
      exact ⟨by linarith only [hlo], by linarith only [hhi]⟩
    · simpa only [J, update_of_ne hij] using hx i
  · simp only [J, update_self]
    change _ - _ = h
    ring
  · simp only [J, update_of_ne hij, and_self]

end BoxIntegral.Prepartition
