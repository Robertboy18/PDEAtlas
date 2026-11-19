/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.SpaceTime.Boxes
public import PDE.Analysis.BoxIntegral.Partition.EqualSlices
import CAS.ExactTactic

/-!
# Partitions of enlarged time windows

Stretching only the time coordinate preserves the spatial face. An integer
stretch admits a partition into boxes with the original parabolic
side lengths. These are the roots for finite stopping arguments; the spatial
dimension may be zero.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open BoxIntegral Set MeasureTheory

variable {n : ℕ}

/-- An integer enlargement of the time interval has a partition into
parabolic boxes with the original radius and time length. -/
theorem exists_parabolic_partition_time_stretch
    (I : Box (Fin (n + 1))) (j : Fin (n + 1)) {r ε : ℝ}
    (hside : ∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r)
    (htime : I.upper j - I.lower j = ε * r ^ 2)
    {N : ℕ} (hN : 0 < N) :
    ∃ π : Prepartition (I.forwardExtension j (-1) N (Nat.cast_pos.mpr hN)),
      π.IsPartition ∧ ∀ J ∈ π,
        (∀ i, (J.face j).upper i - (J.face j).lower i = 2 * r) ∧
          J.upper j - J.lower j = ε * r ^ 2 := by
  obtain ⟨π, hπ, hslices⟩ := Prepartition.exists_equal_coordinate_partition
    (I.forwardExtension j (-1) N (Nat.cast_pos.mpr hN)) j hN
  refine ⟨π, hπ, fun J hJ ↦ ⟨?_, ?_⟩⟩
  · intro i
    have hi := (hslices J hJ).2 (j.succAbove i) (Fin.succAbove_ne j i)
    change J.upper (j.succAbove i) - J.lower (j.succAbove i) = _
    rw [hi.1, hi.2]
    simpa only [Box.forwardExtension, Function.update_of_ne (Fin.succAbove_ne j i),
      Box.face, Function.comp_apply]
      using hside i
  · rw [(hslices J hJ).1, Box.upper_sub_lower_forwardExtension, htime]
    have hNreal : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
    clear * - N r ε hNreal
    cas using hNreal

/-- The volume of an enlarged time window grows exactly linearly with its
stretch factor. -/
theorem volume_real_time_stretch_of_side
    (I : Box (Fin (n + 1))) (j : Fin (n + 1)) {r ε L : ℝ}
    (hL : 0 < L)
    (hside : ∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r)
    (htime : I.upper j - I.lower j = ε * r ^ 2) :
    volume.real (I.forwardExtension j (-1) L hL : Set (Fin (n + 1) → ℝ)) =
      (2 * r) ^ n * (L * (ε * r ^ 2)) := by
  apply volume_real_box_space_time_of_side _ j
  · simpa only [Box.face_forwardExtension] using hside
  · rw [Box.upper_sub_lower_forwardExtension, htime]

/-- Every contact cylinder centered in a stretched time window lies in a
single larger cylinder. The radius bound is retained explicitly, so the
statement also applies when the spatial face has dimension zero. -/
theorem subbox_cylinder_subset_time_stretch_cylinder
    {I J : Box (Fin (n + 1))} (j : Fin (n + 1))
    {r rJ ε L R D : ℝ} (hrJ : 0 ≤ rJ) (hr : rJ ≤ r)
    (hL : 0 < L) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hJI : J ≤ I.forwardExtension j (-1) L hL)
    (hside : ∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r)
    (htime : I.upper j - I.lower j = ε * r ^ 2) :
    Metric.closedBall (euclideanBoxCenter (J.face j)) (rJ * R) ×ˢ
        Icc (J.lower j) (J.lower j + rJ ^ 2 * D) ⊆
      Metric.closedBall (euclideanBoxCenter (I.face j))
          (r * (R + ((n : ℝ) + 1))) ×ˢ
        Icc (I.lower j) (I.lower j + r ^ 2 * (L * ε + D)) := by
  have hface : J.face j ≤ I.face j := by
    simpa only [Box.face_forwardExtension] using Box.face_mono hJI j
  have hcenter := norm_sub_euclideanBoxCenter_le (I.face j) (hrJ.trans hr)
    hside ((Box.le_iff_Icc.mp hface) (euclideanBoxCenter_mem_Icc (J.face j)))
  have hlower := Box.antitone_lower hJI j
  change (I.forwardExtension j (-1) L hL).lower j ≤ J.lower j at hlower
  rw [Box.lower_forwardExtension_neg_one] at hlower
  have hupper := Box.monotone_upper hJI j
  change J.upper j ≤ (I.forwardExtension j (-1) L hL).upper j at hupper
  rw [Box.upper_forwardExtension_neg_one, htime] at hupper
  have hsquare : rJ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hrJ hr 2
  intro p hp
  refine ⟨?_, hlower.trans hp.2.1, ?_⟩
  · have hdist := dist_triangle p.1 (euclideanBoxCenter (J.face j))
      (euclideanBoxCenter (I.face j))
    have hball : dist p.1 (euclideanBoxCenter (J.face j)) ≤ rJ * R := hp.1
    have hc : dist (euclideanBoxCenter (J.face j)) (euclideanBoxCenter (I.face j)) ≤
        ((n : ℝ) + 1) * r := by simpa only [dist_eq_norm] using hcenter
    change dist p.1 (euclideanBoxCenter (I.face j)) ≤ _
    nlinarith only [hdist, hball, hc, mul_le_mul_of_nonneg_right hr hR]
  · nlinarith only [hp.2.2, J.lower_le_upper j, hupper,
      mul_le_mul_of_nonneg_right hsquare hD]

end PDE.Analysis
