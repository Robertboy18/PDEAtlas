/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.SpaceTime.Windows
public import PDE.Analysis.BoxIntegral.Partition.FiniteGrowth

/-!
# Dense superlevels in finite parabolic windows

The forward-cover iteration applies to time windows partitioned into
parabolic slices. Descendants halve the spatial radius and quarter the time
length. An explicit radius bound is carried even for a zero-dimensional
spatial face, where side equations alone would give no bound.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open BoxIntegral Set MeasureTheory
open scoped Topology ENNReal

variable {n : ℕ}

/-- A forward growth rule on parabolic descendants forces a dense full-sized
time slice after finitely many level reductions. Only the time interval grows,
and its final volume is the number of slices times the initial volume. -/
theorem exists_dense_time_slice_of_forward_growth
    (I : Box (Fin (n + 1))) (j : Fin (n + 1))
    {r ε δ lag m β : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hδ : 0 ≤ δ) (hlag : 0 ≤ lag) (hm : 0 < m)
    (hside : ∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r)
    (htime : I.upper j - I.lower j = ε * r ^ 2)
    (N S : ℕ) (hstep : lag + m ≤ (S : ℝ))
    (t : ℕ → ℝ) (ht : ∀ k < N, t (k + 1) < t k)
    {u : (Fin (n + 1) → ℝ) → ℝ}
    (hu : ContinuousOn u
      (I.forwardExtension j (-1) (1 + (N : ℝ) * S) (by positivity)).Icc)
    (hparent : ∀ k < N, ∀ J : Box (Fin (n + 1)),
      J ≤ I.forwardExtension j (-1) (1 + (k : ℝ) * S) (by positivity) →
      ∀ rJ : ℝ, 0 < rJ → rJ ≤ r →
        (∀ i, (J.face j).upper i - (J.face j).lower i = 2 * rJ) →
        J.upper j - J.lower j = ε * rJ ^ 2 →
        ∀ K ∈ Prepartition.splitCenterTwiceAt J j,
          δ * volume.real (K : Set (Fin (n + 1) → ℝ)) <
            (volume.restrict {x | t k < u x}).real K →
              (J.forwardExtension j lag m hm : Set (Fin (n + 1) → ℝ)) ⊆
                {x | t (k + 1) < u x})
    (hinitial : β * volume.real (I : Set (Fin (n + 1) → ℝ)) ≤
      (volume.restrict {x | t 0 < u x}).real I)
    (hbudget : (δ * (1 + (lag + 1) / m)) ^ N * (1 + (N : ℝ) * S) < β) :
    ∃ k < N, ∃ J : Box (Fin (n + 1)),
      J ≤ I.forwardExtension j (-1) (1 + (k : ℝ) * S) (by positivity) ∧
      (∀ i, (J.face j).upper i - (J.face j).lower i = 2 * r) ∧
      J.upper j - J.lower j = ε * r ^ 2 ∧
      δ * volume.real (J : Set (Fin (n + 1) → ℝ)) <
        (volume.restrict {x | t k < u x}).real J := by
  classical
  let W (k : ℕ) := I.forwardExtension j (-1) (1 + (k : ℝ) * S) (by positivity)
  have hpart (k : ℕ) : ∃ π : Prepartition (W k), π.IsPartition ∧
      ∀ J ∈ π, (∀ i, (J.face j).upper i - (J.face j).lower i = 2 * r) ∧
        J.upper j - J.lower j = ε * r ^ 2 := by
    have hp := exists_parabolic_partition_time_stretch I j hside htime
      (show 0 < 1 + k * S by omega)
    have hbox : I.forwardExtension j (-1) (1 + k * S : ℕ)
        (Nat.cast_pos.mpr (show 0 < 1 + k * S by omega)) = W k := by
      congr 1
      norm_cast
    exact hbox ▸ hp
  choose π hπ hπsides using hpart
  let P (J : Box (Fin (n + 1))) := ∃ rJ : ℝ, 0 < rJ ∧ rJ ≤ r ∧
    (∀ i, (J.face j).upper i - (J.face j).lower i = 2 * rJ) ∧
      J.upper j - J.lower j = ε * rJ ^ 2
  have hmono {k l : ℕ} (hkl : k ≤ l) : W k ≤ W l := I.forwardExtension_mono j (-1) _ _ (by gcongr)
  have hPπ (k : ℕ) (_ : k < N) (J : Box (Fin (n + 1))) (hJ : J ∈ π k) : P J :=
    ⟨r, hr, le_rfl, hπsides k J hJ⟩
  have hPsplit (k : ℕ) (_ : k < N) (J : Box (Fin (n + 1))) (_ : J ≤ W k)
      (hPJ : P J) (K : Box (Fin (n + 1)))
      (hK : K ∈ Prepartition.splitCenterTwiceAt J j) : P K := by
    obtain ⟨rJ, hrJ, hrJr, hJside, hJtime⟩ := hPJ
    exact ⟨rJ / 2, by positivity, (half_le_self hrJ.le).trans hrJr,
      parabolic_sides_of_mem_splitCenterTwiceAt j hJside hJtime hK⟩
  have hnext (k : ℕ) (_ : k < N) (J : Box (Fin (n + 1))) (hJ : J ≤ W k)
      (hPJ : P J) :
      (J.forwardExtension j lag m hm : Set (Fin (n + 1) → ℝ)) ⊆ W (k + 1) := by
    obtain ⟨rJ, hrJ, hrJr, _, hJtime⟩ := hPJ
    change J.forwardExtension j lag m hm ≤ W (k + 1)
    apply Box.forwardExtension_le_stretch j hlag hm (by positivity) (by positivity) hJ
    · rw [hJtime, htime]
      gcongr
    · push_cast
      linarith only [hstep]
  have hvol : 0 < volume.real (I : Set (Fin (n + 1) → ℝ)) := by
    rw [volume_real_box_space_time_of_side I j hside htime]
    positivity
  have hvolume : volume.real (W N : Set (Fin (n + 1) → ℝ)) =
      (1 + (N : ℝ) * S) * volume.real (I : Set (Fin (n + 1) → ℝ)) := by
    rw [volume_real_time_stretch_of_side I j (by positivity) hside htime,
      volume_real_box_space_time_of_side I j hside htime]
    exact mul_left_comm _ _ _
  obtain ⟨k, hk, J, hJ, hdense⟩ :=
    Prepartition.exists_dense_partition_member_of_forward_growth W π (fun k _ ↦ hπ k) j
      (fun i ↦ if i = j then 4 else 2) (fun i ↦ by split_ifs <;> norm_num)
      (fun J ↦ Prepartition.splitCenterTwiceAt J j)
      (fun J ↦ Prepartition.isPartition_splitCenterTwiceAt J j)
      (by
        intro J K hK i
        by_cases hij : i = j <;>
          simpa only [hij, ↓reduceIte] using
            Prepartition.upper_sub_lower_of_mem_splitCenterTwiceAt j hK i)
      P hPπ hPsplit (fun _ hk ↦ Box.le_iff_Icc.mp (hmono hk)) hu t ht hδ hlag hm hnext
      (fun k hk J hJI ⟨rJ, hrJ, hrJr, hJside, hJtime⟩ K hK ↦
        hparent k hk J hJI rJ hrJ hrJr hJside hJtime K hK)
      (by simpa only [W, Nat.cast_zero, zero_mul, add_zero,
        Box.forwardExtension_neg_one_one] using hinitial)
      (by rw [hvolume, ← mul_assoc]; exact mul_lt_mul_of_pos_right hbudget hvol)
  exact ⟨k, hk, J, (π k).le_of_mem hJ, (hπsides k J hJ).1,
    (hπsides k J hJ).2, hdense⟩

end PDE.Analysis
