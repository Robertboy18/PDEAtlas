/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime

/-!
# Calculus on a closed spacetime slab

Regularity within a closed time slab gives ordinary spatial derivatives at
both time endpoints. Bounds for the first two differentials give uniform
time variation of the field and its spatial differential. No extension
across either endpoint is required.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter Set PDE.Common
open scoped ContDiff Topology

variable {n : ℕ} {a b s t M : ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nondegenerate closed time slab has unique differentials, including
on its two boundary hyperplanes. -/
theorem uniqueDiffOn_closed_timeSlab (hab : a < b) :
    UniqueDiffOn ℝ {p : ℝ^(n + 1) | p 0 ∈ Icc a b} := by
  apply uniqueDiffOn_convex ((convex_Icc a b).linear_preimage
    (EuclideanSpace.proj 0).toLinearMap)
  refine ⟨timeSpaceCons ((a + b) / 2) (0 : ℝ^n), mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Filter.mem_of_superset
    ((isOpen_Ioo.preimage (EuclideanSpace.proj 0).continuous).mem_nhds
      (show (timeSpaceCons ((a + b) / 2) (0 : ℝ^n)) 0 ∈ Ioo a b by
        simp only [timeSpaceCons_zero]
        constructor <;> linarith))
  exact fun _ h ↦ Ioo_subset_Icc_self h

/-- A spatial slice of a field regular on a closed time slab is regular on
the whole spatial space, also at initial and terminal time. -/
theorem _root_.ContDiffOn.contDiff_timeSlice {k : ℕ∞} {f : ℝ^(n + 1) → E}
    (hf : ContDiffOn ℝ k f {p | p 0 ∈ Icc a b}) (ht : t ∈ Icc a b) :
    ContDiff ℝ k (fun x ↦ f (timeSpaceCons t x)) :=
  hf.comp_contDiff (contDiff_timeSpaceCons_spatial n t) (fun _ ↦ by simpa using ht)

/-- The spatial differential at a boundary time is the restriction of the
differential within the slab. -/
theorem _root_.ContDiffOn.hasFDerivAt_timeSlice {f : ℝ^(n + 1) → E}
    (hf : ContDiffOn ℝ 1 f {p | p 0 ∈ Icc a b}) (ht : t ∈ Icc a b) (x : ℝ^n) :
    HasFDerivAt (fun y ↦ f (timeSpaceCons t y))
      ((fderivWithin ℝ f {p | p 0 ∈ Icc a b} (timeSpaceCons t x)).comp
        (embedWithTimeZeroCLM n)) x := by
  have hd := (hf.differentiableOn_one (timeSpaceCons t x)
    (by simpa using ht)).hasFDerivWithinAt
  exact hd.comp_hasFDerivAt x (hasFDerivAt_timeSpaceCons_spatial n t x)
    (Eventually.of_forall fun _ ↦ by simpa using ht)

/-- Time displacement with fixed spatial coordinates has exactly the
one-dimensional Euclidean norm. -/
theorem norm_timeSpaceCons_sub_timeSpaceCons (s t : ℝ) (x : ℝ^n) :
    ‖timeSpaceCons s x - timeSpaceCons t x‖ = ‖s - t‖ := by
  have h : timeSpaceCons s x - timeSpaceCons t x =
      EuclideanSpace.single (0 : Fin (n + 1)) (s - t) := by
    ext i
    cases i using Fin.cases <;> simp
  rw [h, PiLp.norm_single]

/-- A uniform bound for the differential within a slab controls the
variation between arbitrary closed time slices. -/
theorem _root_.ContDiffOn.norm_timeSlice_sub_le {f : ℝ^(n + 1) → E}
    (hf : ContDiffOn ℝ 1 f {p | p 0 ∈ Icc a b})
    (hM : ∀ p, p 0 ∈ Icc a b →
      ‖fderivWithin ℝ f {q | q 0 ∈ Icc a b} p‖ ≤ M)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : ℝ^n) :
    ‖f (timeSpaceCons s x) - f (timeSpaceCons t x)‖ ≤ M * ‖s - t‖ := by
  have h := Convex.norm_image_sub_le_of_norm_fderivWithin_le hf.differentiableOn_one
    hM ((convex_Icc a b).linear_preimage (EuclideanSpace.proj 0).toLinearMap)
    (show (timeSpaceCons t x) 0 ∈ Icc a b by simpa using ht)
    (show (timeSpaceCons s x) 0 ∈ Icc a b by simpa using hs)
  simpa only [norm_timeSpaceCons_sub_timeSpaceCons] using h

/-- A bounded second differential controls the time variation of the full
first differential, without requiring a third derivative. -/
theorem _root_.ContDiffOn.norm_fderivWithin_timeSlice_sub_le
    {f : ℝ^(n + 1) → E} (hab : a < b)
    (hf : ContDiffOn ℝ 2 f {p | p 0 ∈ Icc a b})
    (hM : ∀ p, p 0 ∈ Icc a b →
      ‖iteratedFDerivWithin ℝ 2 f {q | q 0 ∈ Icc a b} p‖ ≤ M)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : ℝ^n) :
    ‖fderivWithin ℝ f {p | p 0 ∈ Icc a b} (timeSpaceCons s x) -
      fderivWithin ℝ f {p | p 0 ∈ Icc a b} (timeSpaceCons t x)‖ ≤ M * ‖s - t‖ := by
  have hS := uniqueDiffOn_closed_timeSlab (n := n) hab
  apply (hf.fderivWithin hS (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).norm_timeSlice_sub_le
    (fun p hp ↦ ?_) hs ht x
  rw [← norm_iteratedFDerivWithin_one _ (hS p hp),
    norm_iteratedFDerivWithin_fderivWithin hS hp]
  exact hM p hp

end PDE.Analysis
