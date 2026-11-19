/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Truncation
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Compact odd extension with unrestricted endpoint slopes

Clamp a positive-half function to `[0,L]` and subtract its reflection. If its
endpoint values vanish, this is precisely its odd extension on `[-L,L]` and
zero elsewhere. Lipschitz regularity needs no endpoint slope condition.
In particular a nonzero one-sided derivative at `L` is allowed.
-/

@[expose] public section

noncomputable section

open Set
open scoped NNReal
open scoped Topology

namespace PDE.Analysis.Calculus

/-- Odd reflection of the clamped function. Zero endpoint values make it a zero extension. -/
def compactOddExtension (f : ℝ → ℝ) (L x : ℝ) : ℝ :=
  f (intervalTruncation 0 L x) - f (intervalTruncation 0 L (-x))

/-- The clamped reflection construction is odd even before imposing endpoint conditions. -/
@[simp]
theorem compactOddExtension_neg (f : ℝ → ℝ) (L x : ℝ) :
    compactOddExtension f L (-x) = -compactOddExtension f L x := by
  simp [compactOddExtension, neg_sub]

/-- The origin is always fixed at zero. -/
@[simp]
theorem compactOddExtension_zero (f : ℝ → ℝ) (L : ℝ) :
    compactOddExtension f L 0 = 0 := by
  simp [compactOddExtension]

/-- On the positive closed interval the extension is the original function minus its value at
the origin. -/
theorem compactOddExtension_eq_sub_of_mem_Icc {f : ℝ → ℝ} {L x : ℝ} (hx : x ∈ Icc 0 L) :
    compactOddExtension f L x = f x - f 0 := by
  have hL : 0 ≤ L := hx.1.trans hx.2
  rw [compactOddExtension, intervalTruncation_eq_min_max hL,
    intervalTruncation_eq_min_max hL]
  simp [max_eq_right hx.1, min_eq_right hx.2,
    max_eq_left (neg_nonpos.mpr hx.1), min_eq_right hL]

/-- On the positive closed interval the extension preserves the original function. -/
theorem compactOddExtension_eq_of_mem_Icc {f : ℝ → ℝ} {L x : ℝ}
    (hfzero : f 0 = 0) (hx : x ∈ Icc 0 L) :
    compactOddExtension f L x = f x := by
  have hL : 0 ≤ L := hx.1.trans hx.2
  rw [compactOddExtension, intervalTruncation_eq_min_max hL,
    intervalTruncation_eq_min_max hL]
  simp [max_eq_right hx.1, min_eq_right hx.2,
    max_eq_left (neg_nonpos.mpr hx.1), min_eq_right hL, hfzero]

/-- On the negative interval this is the odd reflection of the positive-half function. -/
theorem compactOddExtension_eq_neg_of_mem_Icc {f : ℝ → ℝ} {L x : ℝ}
    (hfzero : f 0 = 0) (hx : x ∈ Icc (-L) 0) :
    compactOddExtension f L x = -f (-x) := by
  have hpos : -x ∈ Icc 0 L := ⟨neg_nonneg.mpr hx.2, by linarith [hx.1]⟩
  simpa using congrArg Neg.neg (compactOddExtension_eq_of_mem_Icc hfzero hpos)

/-- Inside the positive interval the extension agrees locally with the original function. -/
theorem compactOddExtension_eventuallyEq {f : ℝ → ℝ} {L x : ℝ}
    (hfzero : f 0 = 0) (hx : x ∈ Ioo 0 L) :
    compactOddExtension f L =ᶠ[𝓝 x] f := by
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact compactOddExtension_eq_of_mem_Icc hfzero ⟨hy.1.le, hy.2.le⟩

/-- Inside the negative interval the extension agrees locally with the reflected function. -/
theorem compactOddExtension_eventuallyEq_neg {f : ℝ → ℝ} {L x : ℝ}
    (hfzero : f 0 = 0) (hx : x ∈ Ioo (-L) 0) :
    compactOddExtension f L =ᶠ[𝓝 x] (fun y ↦ -f (-y)) := by
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact compactOddExtension_eq_neg_of_mem_Icc hfzero ⟨hy.1.le, hy.2.le⟩

/-- Smoothness is unchanged at points strictly inside the positive half: there the extension
is `f - f 0`. -/
theorem contDiffAt_compactOddExtension {f : ℝ → ℝ} {L x : ℝ} {n : ℕ}
    (hx : x ∈ Ioo 0 L) (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (compactOddExtension f L) x := by
  refine (hf.sub (contDiffAt_const (c := f 0))).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact compactOddExtension_eq_sub_of_mem_Icc ⟨hy.1.le, hy.2.le⟩

/-- Reflection preserves smoothness strictly inside the negative half: there the extension is
`y ↦ f 0 - f (-y)`. -/
theorem contDiffAt_compactOddExtension_neg {f : ℝ → ℝ} {L x : ℝ} {n : ℕ}
    (hx : x ∈ Ioo (-L) 0) (hf : ContDiffAt ℝ n f (-x)) :
    ContDiffAt ℝ n (compactOddExtension f L) x := by
  refine ((contDiffAt_const (c := f 0)).sub (hf.comp x contDiffAt_id.neg)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  have h := compactOddExtension_neg f L (-y)
  rw [neg_neg] at h
  rw [h, compactOddExtension_eq_sub_of_mem_Icc ⟨by linarith [hy.2], by linarith [hy.1]⟩,
    neg_sub]
  rfl

/-- Beyond the positive endpoint, the extension vanishes using only endpoint values. -/
theorem compactOddExtension_eq_zero_of_le {f : ℝ → ℝ} {L x : ℝ}
    (hL : 0 ≤ L) (hfzero : f 0 = 0) (hfL : f L = 0) (hx : L ≤ x) :
    compactOddExtension f L x = 0 := by
  have hxzero : 0 ≤ x := hL.trans hx
  rw [compactOddExtension, intervalTruncation_eq_min_max hL,
    intervalTruncation_eq_min_max hL]
  simp [max_eq_right hxzero, min_eq_left hx,
    max_eq_left (neg_nonpos.mpr hxzero), min_eq_right hL, hfzero, hfL]

/-- Both exterior rays, including their endpoints, have value zero. -/
theorem compactOddExtension_eq_zero_of_le_abs {f : ℝ → ℝ} {L x : ℝ}
    (hL : 0 ≤ L) (hfzero : f 0 = 0) (hfL : f L = 0) (hx : L ≤ |x|) :
    compactOddExtension f L x = 0 := by
  rcases le_or_gt 0 x with hpos | hneg
  · exact compactOddExtension_eq_zero_of_le hL hfzero hfL
      (by simpa only [abs_of_nonneg hpos] using hx)
  · have h := compactOddExtension_eq_zero_of_le hL hfzero hfL
        (by simpa only [abs_of_neg hneg] using hx : L ≤ -x)
    rw [compactOddExtension_neg] at h
    exact neg_eq_zero.mp h

/-- The topological support is contained in the intended compact symmetric interval. -/
theorem tsupport_compactOddExtension_subset {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hfzero : f 0 = 0) (hfL : f L = 0) :
    tsupport (compactOddExtension f L) ⊆ Icc (-L) L := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hmem
  have hbound : L ≤ |x| := by
    by_cases hleft : -L ≤ x
    · have hright : L < x := lt_of_not_ge (fun h ↦ hmem ⟨hleft, h⟩)
      exact hright.le.trans (le_abs_self x)
    · exact (neg_le_abs x).trans' (by linarith [lt_of_not_ge hleft])
  exact hx (compactOddExtension_eq_zero_of_le_abs hL hfzero hfL hbound)

/-- The extension has compact support; no endpoint derivative condition occurs. -/
theorem hasCompactSupport_compactOddExtension {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hfzero : f 0 = 0) (hfL : f L = 0) :
    HasCompactSupport (compactOddExtension f L) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure
    (tsupport_compactOddExtension_subset hL hfzero hfL)

private theorem intervalTruncation_mem_Icc {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    intervalTruncation 0 L x ∈ Icc 0 L := by
  rw [intervalTruncation_eq_min_max hL]
  exact ⟨le_min hL (le_max_left _ _), min_le_left _ _⟩

/-- A Lipschitz function on the positive interval gives a globally Lipschitz odd extension.
The bound `K + K` follows directly by subtracting two clamped copies. -/
theorem lipschitzWith_compactOddExtension {f : ℝ → ℝ} {L : ℝ} {K : ℝ≥0}
    (hL : 0 ≤ L) (hf : LipschitzOnWith K f (Icc 0 L)) :
    LipschitzWith (K + K) (compactOddExtension f L) := by
  have hclamp : LipschitzWith K (fun x ↦ f (intervalTruncation 0 L x)) := by
    intro x y
    calc
      edist (f (intervalTruncation 0 L x)) (f (intervalTruncation 0 L y)) ≤
          K * edist (intervalTruncation 0 L x) (intervalTruncation 0 L y) :=
        hf (intervalTruncation_mem_Icc hL x) (intervalTruncation_mem_Icc hL y)
      _ ≤ K * edist x y :=
        mul_le_mul' le_rfl (by simpa using (lipschitzWith_intervalTruncation hL) x y)
  have hreflect : LipschitzWith K (fun x ↦ f (intervalTruncation 0 L (-x))) := by
    intro x y
    simpa only [edist_neg_neg] using hclamp (-x) (-y)
  exact hclamp.sub hreflect

/-- `C¹` on the compact positive interval supplies the required finite Lipschitz bound. -/
theorem exists_lipschitzWith_compactOddExtension {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hf : ContDiffOn ℝ 1 f (Icc 0 L)) :
    ∃ K : ℝ≥0, LipschitzWith K (compactOddExtension f L) := by
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  exact ⟨K + K, lipschitzWith_compactOddExtension hL hK⟩

end PDE.Analysis.Calculus
