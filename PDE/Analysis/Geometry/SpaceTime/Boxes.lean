/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.BoxIntegral.Partition.Anisotropic
public import PDE.Analysis.BoxIntegral.Box.ForwardExtension
public import PDE.Analysis.Geometry.EuclideanBox
import CAS.ExactTactic

/-!
# Euclidean spacetime and Mathlib boxes

Inserting time into one coordinate identifies Euclidean spacetime with the
coordinate space used by Mathlib's boxes. This identification preserves volume.
The remaining coordinates give the spatial face, so inscribed balls and
parabolic side lengths come from the Euclidean geometry of the box.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open BoxIntegral Set Metric MeasureTheory

variable {n : ℕ}

/-- Inserting time into a coordinate preserves volume for every set, including
sets not known to be measurable and zero-dimensional spatial factors. -/
theorem volume_preimage_insertNth_ofLp (j : Fin (n + 1))
    (S : Set (Fin (n + 1) → ℝ)) :
    volume ((fun p : ℝ^n × ℝ ↦ j.insertNth p.2 (WithLp.ofLp p.1)) ⁻¹' S) =
      volume S := by
  let e :=
    ((MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.prodCongr
      (MeasurableEquiv.refl ℝ)).trans
      ((MeasurableEquiv.prodComm (α := Fin n → ℝ) (β := ℝ)).trans
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) j).symm)
  have hpres : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) j).symm.comp
      (Measure.measurePreserving_swap.comp
        ((PiLp.volume_preserving_ofLp (Fin n)).prod (MeasurePreserving.id volume)))
  change volume (e ⁻¹' S) = volume S
  rw [← e.map_apply S, hpres.map_eq]

/-- The spacetime realization of a box is the product of its spatial
face and its time interval. -/
theorem preimage_insertNth_ofLp_box (I : Box (Fin (n + 1))) (j : Fin (n + 1)) :
    (fun p : ℝ^n × ℝ ↦ j.insertNth p.2 (WithLp.ofLp p.1)) ⁻¹'
        (I : Set (Fin (n + 1) → ℝ)) =
      (WithLp.ofLp ⁻¹' (I.face j : Set (Fin n → ℝ))) ×ˢ Ioc (I.lower j) (I.upper j) := by
  ext p
  change j.insertNth p.2 (WithLp.ofLp p.1) ∈ I ↔ _
  rw [Box.mem_def, j.forall_iff_succAbove]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  exact and_comm

/-- The inscribed spatial ball times the full time interval lies in a
parabolic box. -/
theorem ball_prod_Ioc_subset_insertNth_ofLp_box
    (I : Box (Fin (n + 1))) (j : Fin (n + 1)) {r : ℝ}
    (hside : ∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r) :
    ball (euclideanBoxCenter (I.face j)) r ×ˢ Ioc (I.lower j) (I.upper j) ⊆
      (fun p : ℝ^n × ℝ ↦ j.insertNth p.2 (WithLp.ofLp p.1)) ⁻¹'
        (I : Set (Fin (n + 1) → ℝ)) := by
  rw [preimage_insertNth_ofLp_box]
  exact Set.prod_mono (ball_euclideanBoxCenter_subset _ hside) Subset.rfl

/-- Volume of a box with equal spatial sides and a prescribed time length. -/
theorem volume_real_box_space_time_of_side
    (I : Box (Fin (n + 1))) (j : Fin (n + 1)) {r h : ℝ}
    (hside : ∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r)
    (htime : I.upper j - I.lower j = h) :
    volume.real (I : Set (Fin (n + 1) → ℝ)) = (2 * r) ^ n * h := by
  rw [measureReal_def, I.volume_apply', ← Box.volume_face_mul j I]
  simp only [hside, htime, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Prescribed center, spatial radius, and positive time length determine an
ordinary Mathlib box with the required parabolic face geometry. -/
theorem exists_box_space_time_of_center (j : Fin (n + 1))
    (z : ℝ^n) (s : ℝ) {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    ∃ I : Box (Fin (n + 1)), euclideanBoxCenter (I.face j) = z ∧
      I.lower j = s ∧ I.upper j = s + h ∧
      ∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r := by
  let I : Box (Fin (n + 1)) :=
    ⟨j.insertNth s (fun i ↦ z i - r), j.insertNth (s + h) (fun i ↦ z i + r), by
      rw [j.forall_iff_succAbove]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
      exact ⟨lt_add_of_pos_right _ hh, fun _ ↦ by linarith only [hr]⟩⟩
  refine ⟨I, ?_, ?_, ?_, ?_⟩
  · ext i
    simp only [euclideanBoxCenter, I, Box.face]
    cas
  · simp only [I, Fin.insertNth_apply_same]
  · simp only [I, Fin.insertNth_apply_same]
  · intro i
    simp only [I, Box.face]
    cas

/-- Restricting coordinate volume to a decoded superlevel set agrees with
the spacetime volume of that superlevel set inside the realized box. No
measurability assumption on the function is needed. -/
theorem volume_real_restrict_box_insertNth
    (I : Box (Fin (n + 1))) (j : Fin (n + 1)) (u : ℝ^n → ℝ → ℝ) (ℓ : ℝ) :
    (volume.restrict {x : Fin (n + 1) → ℝ |
      ℓ < u (WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) (x j)}).real I =
    volume.real
      (((fun p : ℝ^n × ℝ ↦ j.insertNth p.2 (WithLp.ofLp p.1)) ⁻¹'
        (I : Set (Fin (n + 1) → ℝ))) ∩ {p | ℓ < u p.1 p.2}) := by
  rw [measureReal_def, Measure.restrict_apply I.measurableSet_coe,
    ← volume_preimage_insertNth_ofLp j]
  congr 2
  ext p
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq,
    Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- The anisotropic split preserves the parabolic relation between
the time length and the square of the spatial radius. -/
theorem parabolic_sides_of_mem_splitCenterTwiceAt
    {I J : Box (Fin (n + 1))} (j : Fin (n + 1)) {r ε : ℝ}
    (hside : ∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r)
    (htime : I.upper j - I.lower j = ε * r ^ 2)
    (hJ : J ∈ Prepartition.splitCenterTwiceAt I j) :
    (∀ i, (J.face j).upper i - (J.face j).lower i = 2 * (r / 2)) ∧
      J.upper j - J.lower j = ε * (r / 2) ^ 2 := by
  constructor
  · intro i
    change J.upper (j.succAbove i) - J.lower (j.succAbove i) = _
    rw [Prepartition.upper_sub_lower_of_mem_splitCenterTwiceAt j hJ,
      ite_eq_right (Fin.succAbove_ne j i)]
    change ((I.face j).upper i - (I.face j).lower i) / 2 = _
    rw [hside]
    cas
  · rw [Prepartition.upper_sub_lower_of_mem_splitCenterTwiceAt j hJ, ite_eq_left rfl, htime]
    cas

/-- The closure of a parabolic box lies in its enclosing Euclidean cylinder. -/
theorem mapsTo_box_space_time_cylinder
    (I : Box (Fin (n + 1))) (j : Fin (n + 1)) {r ε R b : ℝ}
    (hr : 0 ≤ r) (hR : (n : ℝ) + 1 ≤ R) (hεb : ε ≤ b)
    (hside : ∀ i, (I.face j).upper i - (I.face j).lower i = 2 * r)
    (htime : I.upper j - I.lower j = ε * r ^ 2) :
    MapsTo (fun x : Fin (n + 1) → ℝ ↦
      (WithLp.toLp 2 (fun i ↦ x (j.succAbove i)), x j)) I.Icc
      (closedBall (euclideanBoxCenter (I.face j)) (r * R) ×ˢ
        Icc (I.lower j) (I.lower j + r ^ 2 * b)) := by
  intro x hx
  have hxface : (fun i ↦ x (j.succAbove i)) ∈ (I.face j).Icc :=
    ⟨fun i ↦ hx.1 _, fun i ↦ hx.2 _⟩
  have hxnorm := norm_sub_euclideanBoxCenter_le (I.face j) hr hside
    (x := WithLp.toLp 2 (fun i ↦ x (j.succAbove i))) hxface
  refine ⟨?_, hx.1 j, ?_⟩
  · change ‖WithLp.toLp 2 (fun i ↦ x (j.succAbove i)) -
      euclideanBoxCenter (I.face j)‖ ≤ r * R
    exact hxnorm.trans (by nlinarith)
  · have hxupper := hx.2 j
    nlinarith [mul_le_mul_of_nonneg_right hεb (sq_nonneg r)]

/-- A forward extension of a parent remains close to any parabolic child.
The lower time bound is measured from that child's initial face. -/
theorem forwardExtension_subset_child_cylinder
    {J K : Box (Fin (n + 1))} (j : Fin (n + 1))
    (hK : K ∈ Prepartition.splitCenterTwiceAt J j)
    {r ε lag m H : ℝ} (hr : 0 ≤ r) (hm : 0 < m)
    (hside : ∀ i, (K.face j).upper i - (K.face j).lower i = 2 * r)
    (htime : K.upper j - K.lower j = ε * r ^ 2)
    (hlagtime : lag * (4 * ε) = 1) (hH : H = 4 * ε * (1 + lag + m)) :
    MapsTo (fun x : Fin (n + 1) → ℝ ↦
      (WithLp.toLp 2 (fun i ↦ x (j.succAbove i)), x j))
      (J.forwardExtension j lag m hm : Set (Fin (n + 1) → ℝ))
      (closedBall (euclideanBoxCenter (K.face j)) (4 * ((n : ℝ) + 1) * r) ×ˢ
        Icc (K.lower j + r ^ 2) (K.lower j + r ^ 2 + r ^ 2 * H)) := by
  have hKJ : K ≤ J := (Prepartition.splitCenterTwiceAt J j).le_of_mem hK
  have hJside (i : Fin n) : (J.face j).upper i - (J.face j).lower i = 4 * r := by
    have h := Prepartition.upper_sub_lower_of_mem_splitCenterTwiceAt j hK (j.succAbove i)
    rw [ite_eq_right (Fin.succAbove_ne j i)] at h
    change (K.face j).upper i - (K.face j).lower i =
      ((J.face j).upper i - (J.face j).lower i) / 2 at h
    rw [hside] at h
    linarith
  have hJtime : J.upper j - J.lower j = 4 * ε * r ^ 2 := by
    have h := Prepartition.upper_sub_lower_of_mem_splitCenterTwiceAt j hK j
    rw [ite_eq_left rfl, htime] at h
    linarith
  intro x hx
  obtain ⟨hxface, hxtime⟩ := (J.mem_forwardExtension_iff j lag m hm x).mp hx
  have hxball := norm_sub_euclideanBoxCenter_le_of_mem_parent (Box.face_mono hKJ j)
    hr hJside (x := WithLp.toLp 2 (fun i ↦ x (j.succAbove i)))
    (Box.coe_subset_Icc hxface)
  refine ⟨?_, ?_, ?_⟩
  · change ‖WithLp.toLp 2 (fun i ↦ x (j.succAbove i)) -
      euclideanBoxCenter (K.face j)‖ ≤ 4 * ((n : ℝ) + 1) * r
    convert hxball using 1
    cas
  · have hstart : K.lower j ≤ J.upper j :=
      (K.lower_le_upper j).trans (Box.monotone_upper hKJ j)
    have hlagr : lag * (J.upper j - J.lower j) = r ^ 2 := by
      rw [hJtime, ← mul_assoc, hlagtime, one_mul]
    rw [hlagr] at hxtime
    linarith [hxtime.1]
  · have hend : J.upper j ≤ K.lower j + 4 * ε * r ^ 2 := by
      have := Box.antitone_lower hKJ j
      linarith
    have hwidth : 4 * ε * r ^ 2 + (lag + m) * (J.upper j - J.lower j) =
        r ^ 2 * H := by rw [hJtime, hH]; cas
    nlinarith [hxtime.2, sq_nonneg r]

end PDE.Analysis
