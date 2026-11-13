/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.BoxIntegral.Partition.Measure
public import PDE.Analysis.MeasureTheory.Covering.ForwardTime
import CAS.ExactTactic

/-!
# Forward extensions of boxes

One coordinate is shifted beyond its upper endpoint and lengthened; all other
coordinates retain their original intervals. Splitting off this coordinate by
Mathlib's measure-preserving equivalence transfers the product-cover estimate
to finite families of boxes, including a zero-dimensional face.
-/

@[expose] public noncomputable section

open Set Function MeasureTheory
open scoped ENNReal

namespace BoxIntegral.Box

variable {ι : Type*}

/-- Replace one side by its forward extension after `lag` original side lengths,
with new length `m` times the original. -/
@[simps]
def forwardExtension [DecidableEq ι] (I : Box ι) (j : ι) (lag m : ℝ)
    (hm : 0 < m) : Box ι where
  lower := update I.lower j (I.upper j + lag * (I.upper j - I.lower j))
  upper := update I.upper j (I.upper j + (lag + m) * (I.upper j - I.lower j))
  lower_lt_upper k := by
    by_cases hkj : k = j
    · subst k
      simp only [update_self]
      calc
        _ < (I.upper j + lag * (I.upper j - I.lower j)) +
            m * (I.upper j - I.lower j) :=
          lt_add_of_pos_right _ (mul_pos hm (sub_pos.mpr (I.lower_lt_upper j)))
        _ = _ := by cas
    · simpa only [update_of_ne hkj] using I.lower_lt_upper k

/-- All spatial faces are unchanged when their omitted coordinate is extended. -/
@[simp]
theorem face_forwardExtension {n : ℕ} (I : Box (Fin (n + 1)))
    (j : Fin (n + 1)) (lag m : ℝ) (hm : 0 < m) :
    (I.forwardExtension j lag m hm).face j = I.face j := by
  ext k
  simp [face, forwardExtension, Fin.succAbove_ne]

/-- Membership in a forward extension separates the original face and the new
interval in the selected coordinate. -/
theorem mem_forwardExtension_iff {n : ℕ} (I : Box (Fin (n + 1)))
    (j : Fin (n + 1)) (lag m : ℝ) (hm : 0 < m) (x : Fin (n + 1) → ℝ) :
    x ∈ I.forwardExtension j lag m hm ↔
      (fun k ↦ x (j.succAbove k)) ∈ I.face j ∧
        x j ∈ Ioc (I.upper j + lag * (I.upper j - I.lower j))
          (I.upper j + (lag + m) * (I.upper j - I.lower j)) := by
  rw [mem_def, j.forall_iff_succAbove]
  simp only [forwardExtension, update_self, update_of_ne (Fin.succAbove_ne j _)]
  exact and_comm

/-- The selected side is multiplied by the extension factor, independently
of the lag. -/
theorem upper_sub_lower_forwardExtension [DecidableEq ι]
    (I : Box ι) (j : ι) (lag m : ℝ) (hm : 0 < m) :
    (I.forwardExtension j lag m hm).upper j -
      (I.forwardExtension j lag m hm).lower j = m * (I.upper j - I.lower j) := by
  simp only [forwardExtension, update_self]
  cas

/-- Lag `-1` stretches the selected side while fixing every lower endpoint. -/
@[simp]
theorem lower_forwardExtension_neg_one [DecidableEq ι]
    (I : Box ι) (j : ι) (m : ℝ) (hm : 0 < m) :
    (I.forwardExtension j (-1) m hm).lower = I.lower := by
  ext i
  by_cases hij : i = j
  · subst i
    simp only [forwardExtension, update_self]
    cas
  · simp only [forwardExtension, update_of_ne hij]

/-- The upper endpoint of a stretch is measured from the original lower
endpoint. -/
theorem upper_forwardExtension_neg_one [DecidableEq ι]
    (I : Box ι) (j : ι) (m : ℝ) (hm : 0 < m) :
    (I.forwardExtension j (-1) m hm).upper j =
      I.lower j + m * (I.upper j - I.lower j) := by
  simp only [forwardExtension, update_self]
  cas

/-- Increasing the extension factor enlarges the box without moving its
lower corner. -/
theorem forwardExtension_mono [DecidableEq ι]
    (I : Box ι) (j : ι) (lag : ℝ) {m m' : ℝ}
    (hm : 0 < m) (hm' : 0 < m') (hmm' : m ≤ m') :
    I.forwardExtension j lag m hm ≤ I.forwardExtension j lag m' hm' := by
  apply le_iff_bounds.mpr
  refine ⟨le_rfl, ?_⟩
  intro i
  by_cases hij : i = j
  · subst i
    simp only [forwardExtension, update_self]
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (add_le_add le_rfl hmm')
        (sub_nonneg.mpr (I.lower_le_upper j)))
  · simp only [forwardExtension, update_of_ne hij, le_refl]

/-- A stretch by one preserves the original box. -/
@[simp]
theorem forwardExtension_neg_one_one [DecidableEq ι] (I : Box ι) (j : ι) :
    I.forwardExtension j (-1) 1 zero_lt_one = I := by
  apply le_antisymm
  · apply le_iff_bounds.mpr
    rw [lower_forwardExtension_neg_one]
    refine ⟨le_rfl, ?_⟩
    intro i
    simp only [forwardExtension, neg_add_cancel, zero_mul, add_zero, update_eq_self,
      le_refl]
  · apply le_iff_bounds.mpr
    rw [lower_forwardExtension_neg_one]
    refine ⟨le_rfl, ?_⟩
    intro i
    simp only [forwardExtension, neg_add_cancel, zero_mul, add_zero, update_eq_self,
      le_refl]

/-- A forward extension fits in the next stretched window when its original
side is at most one base side long. This permits successive windows to grow
linearly even when the boxes being extended have different sizes. -/
theorem forwardExtension_le_stretch [DecidableEq ι]
    {I J : Box ι} (j : ι) {lag m L L' : ℝ}
    (hlag : 0 ≤ lag) (hm : 0 < m) (hL : 0 < L) (hL' : 0 < L')
    (hJI : J ≤ I.forwardExtension j (-1) L hL)
    (hwidth : J.upper j - J.lower j ≤ I.upper j - I.lower j)
    (hstep : L + lag + m ≤ L') :
    J.forwardExtension j lag m hm ≤ I.forwardExtension j (-1) L' hL' := by
  have hbounds := le_iff_bounds.mp hJI
  rw [lower_forwardExtension_neg_one] at hbounds
  apply le_iff_bounds.mpr
  constructor
  · intro i
    by_cases hij : i = j
    · subst i
      rw [lower_forwardExtension_neg_one]
      simp only [forwardExtension, update_self]
      exact (hbounds.1 j).trans ((J.lower_le_upper j).trans
        (le_add_of_nonneg_right
          (mul_nonneg hlag (sub_nonneg.mpr (J.lower_le_upper j)))))
    · simpa only [forwardExtension, update_of_ne hij] using hbounds.1 i
  · intro i
    by_cases hij : i = j
    · subst i
      have hupper := hbounds.2 j
      rw [upper_forwardExtension_neg_one] at hupper
      rw [upper_forwardExtension_neg_one]
      simp only [forwardExtension, update_self]
      have hmul := mul_le_mul_of_nonneg_left hwidth (add_nonneg hlag hm.le)
      have hbudget := mul_le_mul_of_nonneg_right hstep
        (sub_nonneg.mpr (I.lower_le_upper j))
      nlinarith only [hupper, hmul, hbudget]
    · simpa only [forwardExtension, update_of_ne hij] using hbounds.2 i

/-- A forward extension of a small box remains in a controlled neighborhood.
This is the locality needed for stopping arguments on continuous superlevels. -/
theorem forwardExtension_subset_ball [Fintype ι] [DecidableEq ι]
    (I : Box ι) (j : ι) {lag m r : ℝ} (hlag : 0 ≤ lag) (hm : 0 < m)
    (hr : 0 < r) {z : ι → ℝ} (hI : I.Icc ⊆ Metric.ball z r) :
    (I.forwardExtension j lag m hm : Set (ι → ℝ)) ⊆
      Metric.ball z ((1 + 2 * (lag + m)) * r) := by
  have hl := (dist_pi_lt_iff hr).mp (hI I.lower_mem_Icc)
  have hu := (dist_pi_lt_iff hr).mp (hI I.upper_mem_Icc)
  have hK : 1 ≤ 1 + 2 * (lag + m) :=
    le_add_of_nonneg_right (mul_nonneg (by norm_num) (add_nonneg hlag hm.le))
  have hKr : r ≤ (1 + 2 * (lag + m)) * r := le_mul_of_one_le_left hr.le hK
  intro x hx
  apply (dist_pi_lt_iff (hr.trans_le hKr)).mpr
  intro k
  have hlk := abs_lt.mp (show |I.lower k - z k| < r from hl k)
  have huk := abs_lt.mp (show |I.upper k - z k| < r from hu k)
  have hxk := hx k
  rw [Real.dist_eq]
  by_cases hkj : k = j
  · subst k
    simp only [forwardExtension, update_self, mem_Ioc] at hxk
    have hwidth : I.upper j - I.lower j < 2 * r := by linarith
    have hmul := mul_lt_mul_of_pos_left hwidth (add_pos_of_nonneg_of_pos hlag hm)
    have hlagwidth := mul_nonneg hlag (sub_nonneg.mpr (I.lower_le_upper j))
    exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
  · simp only [forwardExtension, update_of_ne hkj, mem_Ioc] at hxk
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- Finite box covers are controlled in volume by their forward extensions.
Neither disjointness nor a common side length is required. -/
theorem volume_biUnion_le_forwardExtension {n : ℕ} {κ : Type*}
    (s : Finset κ) (I : κ → Box (Fin (n + 1))) (j : Fin (n + 1))
    {lag m : ℝ} (hlag : 0 ≤ lag) (hm : 0 < m) :
    volume (⋃ k ∈ s, (I k : Set (Fin (n + 1) → ℝ))) ≤
      ENNReal.ofReal (1 + (lag + 1) / m) *
        volume (⋃ k ∈ s, (I k |>.forwardExtension j lag m hm :
          Set (Fin (n + 1) → ℝ))) := by
  classical
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) j).trans
    (MeasurableEquiv.prodComm (α := ℝ) (β := Fin n → ℝ))
  have hpres : MeasurePreserving e :=
    Measure.measurePreserving_swap.comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) j)
  have hvolume (S : Set ((Fin n → ℝ) × ℝ)) : volume (e ⁻¹' S) = volume S := by
    rw [← e.map_apply S, hpres.map_eq]
  have hpreimage (J : Box (Fin (n + 1))) :
      e ⁻¹' ((J.face j : Set (Fin n → ℝ)) ×ˢ Ioc (J.lower j) (J.upper j)) =
        (J : Set (Fin (n + 1) → ℝ)) := by
    ext x
    change ((fun k ↦ x (j.succAbove k)) ∈ J.face j ∧
      x j ∈ Ioc (J.lower j) (J.upper j)) ↔ x ∈ J
    conv_rhs => rw [mem_def, j.forall_iff_succAbove]
    exact and_comm
  have hcover (J : κ → Box (Fin (n + 1))) :
      volume (⋃ k ∈ s, (J k : Set (Fin (n + 1) → ℝ))) =
        volume (⋃ k ∈ s, (J k |>.face j : Set (Fin n → ℝ)) ×ˢ
          Ioc ((J k).lower j) ((J k).upper j)) := by
    rw [← hvolume]
    simp only [preimage_iUnion, hpreimage]
  rw [hcover I, hcover (fun k ↦ (I k).forwardExtension j lag m hm)]
  simpa only [face_forwardExtension, forwardExtension_lower, forwardExtension_upper,
    update_self, Measure.volume_eq_prod] using
    PDE.Analysis.measure_prod_biUnion_Ioc_le_forward volume s
      (fun k ↦ ((I k).face j : Set (Fin n → ℝ)))
      (fun k _ ↦ ((I k).face j).measurableSet_coe)
      (fun k ↦ (I k).lower j) (fun k ↦ (I k).upper j)
      (fun k _ ↦ (I k).lower_le_upper j) hlag hm

/-- Real-valued volume comparison for finite box covers. Both unions have finite
volume, so no information is lost by passing from extended nonnegative reals. -/
theorem volume_real_biUnion_le_forwardExtension {n : ℕ} {κ : Type*}
    (s : Finset κ) (I : κ → Box (Fin (n + 1))) (j : Fin (n + 1))
    {lag m : ℝ} (hlag : 0 ≤ lag) (hm : 0 < m) :
    volume.real (⋃ k ∈ s, (I k : Set (Fin (n + 1) → ℝ))) ≤
      (1 + (lag + 1) / m) *
        volume.real (⋃ k ∈ s, (I k |>.forwardExtension j lag m hm :
          Set (Fin (n + 1) → ℝ))) := by
  have hfinite : volume (⋃ k ∈ s, (I k |>.forwardExtension j lag m hm :
      Set (Fin (n + 1) → ℝ))) ≠ ∞ :=
    measure_biUnion_ne_top s.finite_toSet fun k _ ↦
      ((I k).forwardExtension j lag m hm).measure_coe_lt_top volume |>.ne
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite)
    (volume_biUnion_le_forwardExtension s I j hlag hm)
  simpa only [measureReal_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ 1 + (lag + 1) / m by positivity)] using h

end BoxIntegral.Box
