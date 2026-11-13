/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import CAS.ExactTactic

/-!
# One-sided expansion of finite interval covers

Expanding each interval backwards by a fixed multiple of its length increases
the measure of their union by at most the same factor. Overlapping intervals
can be merged without changing the original union, and their expansions lie
inside the expansion of the merged interval. This reduces the estimate to a
disjoint family, where lengths add.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

/-- The exact length of a backwards-expanded interval. -/
theorem volume_Ioc_backward_expansion (a b k : ℝ) (hk : 0 ≤ k) :
    volume (Ioc (a - k * (b - a)) b) =
      ENNReal.ofReal (1 + k) * volume (Ioc a b) := by
  rw [Real.volume_Ioc, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  cas

/-- Backwards expansion respects inclusion of the endpoint intervals. -/
theorem Ioc_backward_expansion_subset {a b c d k : ℝ} (hk : 0 ≤ k)
    (hca : c ≤ a) (hbd : b ≤ d) :
    Ioc (a - k * (b - a)) b ⊆ Ioc (c - k * (d - c)) d := by
  apply Ioc_subset_Ioc ?_ hbd
  have hlength : b - a ≤ d - c := sub_le_sub hbd hca
  exact sub_le_sub hca (mul_le_mul_of_nonneg_left hlength hk)

/-- A finite union of intervals grows in measure by at most `1 + k` when each interval
is extended backwards by `k` times its length. Endpoints may coincide. -/
theorem volume_biUnion_Ioc_backward_expansion
    (s : Finset (ℝ × ℝ)) {k : ℝ} (hk : 0 ≤ k)
    (hab : ∀ p ∈ s, p.1 ≤ p.2) :
    volume (⋃ p ∈ s, Ioc (p.1 - k * (p.2 - p.1)) p.2) ≤
      ENNReal.ofReal (1 + k) * volume (⋃ p ∈ s, Ioc p.1 p.2) := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hd : (s : Set (ℝ × ℝ)).PairwiseDisjoint (fun p ↦ Ioc p.1 p.2)
    · calc
        _ ≤ ∑ p ∈ s, volume (Ioc (p.1 - k * (p.2 - p.1)) p.2) :=
          measure_biUnion_finset_le _ _
        _ = ENNReal.ofReal (1 + k) * ∑ p ∈ s, volume (Ioc p.1 p.2) := by
          simp only [volume_Ioc_backward_expansion _ _ _ hk, Finset.mul_sum]
        _ = _ := by rw [measure_biUnion_finset hd (fun _ _ ↦ measurableSet_Ioc)]
    · simp only [PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, not_forall] at hd
      obtain ⟨p, hp, q, hq, hpq, hover⟩ := hd
      have hover' : max p.1 q.1 < min p.2 q.2 :=
        lt_of_not_ge (Ioc_disjoint_Ioc.not.mp hover)
      let r : ℝ × ℝ := (min p.1 q.1, max p.2 q.2)
      let t := (s.erase p).erase q
      let s' := insert r t
      have hqt : q ∈ s.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
      have hdecomp : s = insert p (insert q t) := by
        simp only [t, Finset.insert_erase hqt, Finset.insert_erase hp]
      have hcard : s'.card < n := by
        have h₁ := Finset.card_erase_add_one hp
        have h₂ := Finset.card_erase_add_one hqt
        have h₃ := Finset.card_insert_le r t
        dsimp only [s', t] at *
        omega
      have hr : r.1 ≤ r.2 :=
        (min_le_left _ _).trans ((hab p hp).trans (le_max_left _ _))
      have hpos : ∀ z ∈ s', z.1 ≤ z.2 := by
        intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hz
        · exact hr
        · exact hab z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))
      have hunion : Ioc p.1 p.2 ∪ Ioc q.1 q.2 = Ioc r.1 r.2 :=
        Ioc_union_Ioc'
          ((le_max_right _ _).trans (hover'.le.trans (min_le_left _ _)))
          ((le_max_left _ _).trans (hover'.le.trans (min_le_right _ _)))
      have hunion_all : (⋃ z ∈ s, Ioc z.1 z.2) = ⋃ z ∈ s', Ioc z.1 z.2 := by
        rw [hdecomp]
        simp only [s', Finset.set_biUnion_insert, ← union_assoc, hunion]
      have hsubset :
          (⋃ z ∈ s, Ioc (z.1 - k * (z.2 - z.1)) z.2) ⊆
            ⋃ z ∈ s', Ioc (z.1 - k * (z.2 - z.1)) z.2 := by
        rw [hdecomp]
        simp only [s', Finset.set_biUnion_insert]
        refine union_subset ?_ (union_subset ?_ (subset_union_right ..))
        · exact (Ioc_backward_expansion_subset hk (min_le_left _ _)
            (le_max_left _ _)).trans (subset_union_left ..)
        · exact (Ioc_backward_expansion_subset hk (min_le_right _ _)
            (le_max_right _ _)).trans (subset_union_left ..)
      calc
        _ ≤ volume (⋃ z ∈ s', Ioc (z.1 - k * (z.2 - z.1)) z.2) :=
          measure_mono hsubset
        _ ≤ ENNReal.ofReal (1 + k) * volume (⋃ z ∈ s', Ioc z.1 z.2) :=
          ih s'.card hcard s' hpos rfl
        _ = _ := by rw [hunion_all]

/-- A family of intervals is controlled by the union of its forward extensions.
The extensions begin after a lag of `lag` interval lengths and last `m` interval
lengths; the loss tends to one as `m` increases. -/
theorem volume_biUnion_Ioc_le_forward
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ s, a i ≤ b i) {lag m : ℝ} (hlag : 0 ≤ lag) (hm : 0 < m) :
    volume (⋃ i ∈ s, Ioc (a i) (b i)) ≤
      ENNReal.ofReal (1 + (lag + 1) / m) *
        volume (⋃ i ∈ s,
          Ioc (b i + lag * (b i - a i)) (b i + (lag + m) * (b i - a i))) := by
  classical
  let endpoints : ι → ℝ × ℝ := fun i ↦
    (b i + lag * (b i - a i), b i + (lag + m) * (b i - a i))
  have hk : 0 ≤ (lag + 1) / m := div_nonneg (by positivity) hm.le
  have hlength : ∀ p ∈ s.image endpoints, p.1 ≤ p.2 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    dsimp only [endpoints]
    nlinarith [mul_nonneg hm.le (sub_nonneg.mpr (hab i hi))]
  have hleft (i : ι) :
      (endpoints i).1 - (lag + 1) / m * ((endpoints i).2 - (endpoints i).1) = a i := by
    dsimp only [endpoints]
    cas using hm
  have hright (i : ι) (hi : i ∈ s) : b i ≤ (endpoints i).2 := by
    exact le_add_of_nonneg_right (mul_nonneg (add_nonneg hlag hm.le)
      (sub_nonneg.mpr (hab i hi)))
  have himage (f : (ℝ × ℝ) → Set ℝ) :
      (⋃ p ∈ s.image endpoints, f p) = ⋃ i ∈ s, f (endpoints i) := by
    ext x
    simp
  calc
    _ ≤ volume (⋃ p ∈ s.image endpoints,
        Ioc (p.1 - (lag + 1) / m * (p.2 - p.1)) p.2) := by
      rw [himage]
      apply measure_mono
      refine iUnion₂_mono fun i hi ↦ ?_
      rw [hleft]
      exact Ioc_subset_Ioc le_rfl (hright i hi)
    _ ≤ ENNReal.ofReal (1 + (lag + 1) / m) *
        volume (⋃ p ∈ s.image endpoints, Ioc p.1 p.2) :=
      volume_biUnion_Ioc_backward_expansion _ hk hlength
    _ = _ := by rw [himage]

end PDE.Analysis
