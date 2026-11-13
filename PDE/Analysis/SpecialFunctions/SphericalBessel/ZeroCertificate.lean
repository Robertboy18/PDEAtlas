/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Enclosure
public import PDE.Analysis.SpecialFunctions.SphericalBessel.Zeros

/-!
# Certified lists of zeros of spherical Bessel functions

A finite check that lists every zero of `j_l` in an interval `(a, b]`, each in a small rational
interval. The interval is covered by consecutive cells `[t_i, t_{i+1}]` of three kinds.

* A sign cell: the Lipschitz enclosure `sphericalBesselIntervalOn` of `j_l` on the cell excludes
  zero, so `j_l` has no zero there.
* An origin cell `[0, t]` with `t ^ 2 ≤ l (l + 1)`: `j_l` is positive on `(0, t]`
  (`sphericalBesselJ_pos_of_sq_le`).
* A root cell with a refinement `[lo, hi] ⊆ [t_i, t_{i+1}]`: `j_l` changes sign on the cell and on
  the refinement, and the derivative enclosure at the centre of the cell stays away from zero by
  more than the radius. Since `j_l'` is `1`-Lipschitz (`abs_deriv_sphericalBesselJ_sub_le`),
  `j_l` is strictly monotone on the cell, so the cell contains exactly one zero, and it lies in
  `(lo, hi)`.

`zeroCoverCheck l a cells b` checks such a cover, and `of_zeroCoverCheck` concludes that each
refinement contains exactly one zero and that every zero in `(a, b]` lies in one of them. This
is the certified analogue of a table of Bessel zeros: the refinements list the zeros in order.

## Main results

* `abs_deriv_sphericalBesselJ_sub_le`: `j_l'` is `1`-Lipschitz.
* `existsUnique_sphericalBesselJ_eq_zero_of_rootCellCheck`: one zero in a root cell.
* `of_zeroCoverCheck`, `of_zeroCoverCheck_list`: the list of zeros in `(a, b]` is complete.
-/

@[expose] public section

namespace PDE.Analysis.SpecialFunctions

open Set
open CAS.Continuum

/-- The derivative of `j_l` is `1`-Lipschitz, since `|j_l''| ≤ 1`. -/
theorem abs_deriv_sphericalBesselJ_sub_le (l : ℕ) (x y : ℝ) :
    |deriv (sphericalBesselJ l) x - deriv (sphericalBesselJ l) y| ≤ |x - y| := by
  have hd : Differentiable ℝ (deriv (sphericalBesselJ l)) := by
    have h := (contDiff_sphericalBesselJ l (n := 2)).differentiable_iteratedDeriv 1
      (by norm_num)
    simpa only [iteratedDeriv_one] using h
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv (sphericalBesselJ l))
    (s := univ) (C := 1) (fun z _ ↦ hd z) (fun z _ ↦ by
      have hz := abs_iteratedDeriv_sphericalBesselJ_le l 2 z
      rw [iteratedDeriv_succ, iteratedDeriv_one] at hz
      simpa only [Real.norm_eq_abs] using hz) convex_univ (mem_univ y) (mem_univ x)
  simpa only [Real.norm_eq_abs, one_mul] using h

private theorem abs_sub_center_le {a b : ℚ} {y : ℝ} (hy : y ∈ Icc (a : ℝ) b) :
    |y - (((a + b) / 2 : ℚ) : ℝ)| ≤ (((b - a) / 2 : ℚ) : ℝ) := by
  push_cast
  rw [abs_le]
  constructor <;> linarith [hy.1, hy.2]

/-- A root cell: a sign change on `[a, b]`, and a derivative enclosure at the centre whose
distance from zero exceeds the radius. -/
def rootCellCheck (l : ℕ) (a b : ℚ) : Bool :=
  sphericalBesselSignChange l a b &&
    (decide ((b - a) / 2 < (sphericalBesselDerivInterval l ((a + b) / 2)).lo) ||
      decide ((sphericalBesselDerivInterval l ((a + b) / 2)).hi < -((b - a) / 2)))

/-- On a root cell, `j_l` is injective. -/
theorem injOn_sphericalBesselJ_of_rootCellCheck {l : ℕ} {a b : ℚ}
    (h : rootCellCheck l a b = true) : InjOn (sphericalBesselJ l) (Icc (a : ℝ) b) := by
  simp only [rootCellCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  have hcont := (continuous_sphericalBesselJ l).continuousOn (s := Icc (a : ℝ) b)
  have hmem := sphericalBesselDerivInterval_sound l ((a + b) / 2)
  rcases h.2 with hpos | hneg
  · refine (strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont fun y hy ↦ ?_).injOn
    have hy' := abs_sub_center_le (interior_subset hy)
    have hlip := abs_deriv_sphericalBesselJ_sub_le l y (((a + b) / 2 : ℚ) : ℝ)
    have hr : ((((b - a) / 2 : ℚ)) : ℝ) <
        ((sphericalBesselDerivInterval l ((a + b) / 2)).lo : ℝ) := by exact_mod_cast hpos
    have := (abs_le.mp (hlip.trans hy')).1
    linarith [hmem.1]
  · refine (strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont fun y hy ↦ ?_).injOn
    have hy' := abs_sub_center_le (interior_subset hy)
    have hlip := abs_deriv_sphericalBesselJ_sub_le l y (((a + b) / 2 : ℚ) : ℝ)
    have hr : ((sphericalBesselDerivInterval l ((a + b) / 2)).hi : ℝ) <
        -((((b - a) / 2 : ℚ)) : ℝ) := by exact_mod_cast hneg
    have := (abs_le.mp (hlip.trans hy')).2
    linarith [hmem.2]

/-- A root cell contains exactly one zero of `j_l`. -/
theorem existsUnique_sphericalBesselJ_eq_zero_of_rootCellCheck {l : ℕ} {a b : ℚ}
    (h : rootCellCheck l a b = true) :
    ∃! z, z ∈ Ioo (a : ℝ) b ∧ sphericalBesselJ l z = 0 := by
  have hsign : sphericalBesselSignChange l a b = true := by
    simp only [rootCellCheck, Bool.and_eq_true] at h
    exact h.1
  obtain ⟨z, hz, hz0⟩ := exists_sphericalBesselJ_eq_zero_of_sphericalBesselSignChange hsign
  refine ⟨z, ⟨hz, hz0⟩, fun w hw ↦ ?_⟩
  exact injOn_sphericalBesselJ_of_rootCellCheck h (Ioo_subset_Icc_self hw.1)
    (Ioo_subset_Icc_self hz) (hw.2.trans hz0.symm)

/-- A sign change certifies that both endpoints are not zeros. -/
theorem sphericalBesselJ_ne_zero_of_signChange {l : ℕ} {a b : ℚ}
    (h : sphericalBesselSignChange l a b = true) :
    sphericalBesselJ l a ≠ 0 ∧ sphericalBesselJ l b ≠ 0 := by
  simp only [sphericalBesselSignChange, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h.2 with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨(sphericalBesselJ_pos_of_lo_pos ha).ne', (sphericalBesselJ_neg_of_hi_neg hb).ne⟩
  · exact ⟨(sphericalBesselJ_neg_of_hi_neg ha).ne, (sphericalBesselJ_pos_of_lo_pos hb).ne'⟩

/-- A sign cell: the Lipschitz enclosure of `j_l` on `[a, b]` excludes zero. -/
def signCellCheck (l : ℕ) (a b : ℚ) : Bool :=
  decide (0 < (sphericalBesselIntervalOn l ((a + b) / 2) ((b - a) / 2)).lo) ||
    decide ((sphericalBesselIntervalOn l ((a + b) / 2) ((b - a) / 2)).hi < 0)

theorem sphericalBesselJ_ne_zero_of_signCellCheck {l : ℕ} {a b : ℚ}
    (h : signCellCheck l a b = true) {y : ℝ} (hy : y ∈ Icc (a : ℝ) b) :
    sphericalBesselJ l y ≠ 0 := by
  have hmem := sphericalBesselIntervalOn_sound l ((a + b) / 2) ((b - a) / 2)
    (abs_sub_center_le hy)
  simp only [signCellCheck, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with hpos | hneg
  · exact ((by exact_mod_cast hpos : (0 : ℝ) < _).trans_le hmem.1).ne'
  · exact (hmem.2.trans_lt (by exact_mod_cast hneg : _ < (0 : ℝ))).ne

/-- The kind of a cell of a zero cover. -/
inductive ZeroCell where
  /-- `j_l` has no zero on the cell. -/
  | sign
  /-- The cell is `[0, t]` with `t ^ 2 ≤ l (l + 1)`, where `j_l > 0` on `(0, t]`. -/
  | origin
  /-- The cell contains exactly one zero, which lies in `(lo, hi)`. -/
  | root (lo hi : ℚ)
  deriving DecidableEq, Repr

/-- The check of one cell `[a, t]`. -/
def zeroCellCheck (l : ℕ) (a t : ℚ) : ZeroCell → Bool
  | .sign => signCellCheck l a t
  | .origin => decide (a = 0) && decide (0 < t) && decide (t ^ 2 ≤ (l : ℚ) * (l + 1))
  | .root lo hi =>
      rootCellCheck l a t && decide (a ≤ lo) && decide (hi ≤ t) &&
        sphericalBesselSignChange l lo hi

/-- Consecutive cells `[a, t₁], [t₁, t₂], …` ending at `b`, each cell checked. -/
def zeroCoverCheck (l : ℕ) : ℚ → List (ℚ × ZeroCell) → ℚ → Bool
  | a, [], b => decide (a = b)
  | a, (t, cell) :: rest, b =>
      decide (a < t) && zeroCellCheck l a t cell && zeroCoverCheck l t rest b

/-- The refinements of the root cells, in order. -/
def zeroCoverRoots : List (ℚ × ZeroCell) → List (ℚ × ℚ)
  | [] => []
  | (_, .root lo hi) :: rest => (lo, hi) :: zeroCoverRoots rest
  | _ :: rest => zeroCoverRoots rest

/-- One root cell with refinement: exactly one zero in `(lo, hi)`, and every zero in the cell
lies there. -/
theorem of_zeroCellCheck_root {l : ℕ} {a t lo hi : ℚ}
    (h : zeroCellCheck l a t (.root lo hi) = true) :
    (∃! z, z ∈ Ioo (lo : ℝ) hi ∧ sphericalBesselJ l z = 0) ∧
      ∀ x ∈ Icc (a : ℝ) t, sphericalBesselJ l x = 0 → x ∈ Ioo (lo : ℝ) hi := by
  simp only [zeroCellCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hroot, hlo⟩, hhi⟩, hsign⟩ := h
  have hlo' : (a : ℝ) ≤ lo := by exact_mod_cast hlo
  have hhi' : (hi : ℝ) ≤ t := by exact_mod_cast hhi
  obtain ⟨z, hz, hz0⟩ := exists_sphericalBesselJ_eq_zero_of_sphericalBesselSignChange hsign
  have hzIcc : z ∈ Icc (a : ℝ) t := ⟨hlo'.trans hz.1.le, hz.2.le.trans hhi'⟩
  have hinj := injOn_sphericalBesselJ_of_rootCellCheck hroot
  refine ⟨⟨z, ⟨hz, hz0⟩, fun w hw ↦ ?_⟩, fun x hx hx0 ↦ ?_⟩
  · exact hinj ⟨hlo'.trans hw.1.1.le, hw.1.2.le.trans hhi'⟩ hzIcc (hw.2.trans hz0.symm)
  · have hxz : x = z := hinj hx hzIcc (hx0.trans hz0.symm)
    exact hxz ▸ hz

/-- A checked cover lists the zeros of `j_l` in `(a, b]`: each listed interval contains exactly
one zero, and every zero in `(a, b]` lies in a listed interval. -/
theorem of_zeroCoverCheck {l : ℕ} :
    ∀ {a b : ℚ} {cells : List (ℚ × ZeroCell)}, zeroCoverCheck l a cells b = true →
      (∀ I ∈ zeroCoverRoots cells, ∃! z, z ∈ Ioo (I.1 : ℝ) I.2 ∧ sphericalBesselJ l z = 0) ∧
      ∀ x ∈ Ioc (a : ℝ) b, sphericalBesselJ l x = 0 →
        ∃ I ∈ zeroCoverRoots cells, x ∈ Ioo (I.1 : ℝ) I.2
  | a, b, [], h => by
      simp only [zeroCoverCheck, decide_eq_true_eq] at h
      subst h
      refine ⟨by simp [zeroCoverRoots], fun x hx _ ↦ ?_⟩
      exact absurd (hx.1.trans_le hx.2) (lt_irrefl _)
  | a, b, (t, cell) :: rest, h => by
      simp only [zeroCoverCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hat, hcell⟩, hrest⟩ := h
      obtain ⟨ihRoots, ihZeros⟩ := of_zeroCoverCheck hrest
      have hat' : (a : ℝ) < t := by exact_mod_cast hat
      -- Zeros in the first cell `(a, t]`.
      have first : ∀ x ∈ Ioc (a : ℝ) t, sphericalBesselJ l x = 0 →
          ∃ I ∈ zeroCoverRoots ((t, cell) :: rest), x ∈ Ioo (I.1 : ℝ) I.2 := by
        intro x hx hx0
        cases cell with
        | sign =>
            exact absurd hx0
              (sphericalBesselJ_ne_zero_of_signCellCheck hcell ⟨hx.1.le, hx.2⟩)
        | origin =>
            simp only [zeroCellCheck, Bool.and_eq_true, decide_eq_true_eq] at hcell
            obtain ⟨⟨ha0, _⟩, ht⟩ := hcell
            have hxpos : 0 < x := by simpa [ha0] using hx.1
            have hsq : x ^ 2 ≤ (l : ℝ) * (l + 1) := by
              have ht' : ((t : ℝ)) ^ 2 ≤ (l : ℝ) * (l + 1) := by exact_mod_cast ht
              nlinarith [hx.2, hxpos]
            exact absurd hx0 (sphericalBesselJ_pos_of_sq_le hxpos hsq).ne'
        | root lo hi =>
            exact ⟨(lo, hi), by simp [zeroCoverRoots],
              (of_zeroCellCheck_root hcell).2 x ⟨hx.1.le, hx.2⟩ hx0⟩
      refine ⟨fun I hI ↦ ?_, fun x hx hx0 ↦ ?_⟩
      · cases cell with
        | root lo hi =>
            simp only [zeroCoverRoots, List.mem_cons] at hI
            rcases hI with rfl | hI
            · exact (of_zeroCellCheck_root hcell).1
            · exact ihRoots I hI
        | sign => exact ihRoots I (by simpa [zeroCoverRoots] using hI)
        | origin => exact ihRoots I (by simpa [zeroCoverRoots] using hI)
      · by_cases hxt : x ≤ t
        · exact first x ⟨hx.1, hxt⟩ hx0
        · obtain ⟨I, hI, hxI⟩ := ihZeros x ⟨lt_of_not_ge hxt, hx.2⟩ hx0
          refine ⟨I, ?_, hxI⟩
          cases cell with
          | root lo hi => exact List.mem_cons_of_mem _ hI
          | sign => simpa [zeroCoverRoots] using hI
          | origin => simpa [zeroCoverRoots] using hI

/-- `of_zeroCoverCheck` with the list of root intervals given explicitly. -/
theorem of_zeroCoverCheck_list (l : ℕ) (a b : ℚ) (cells : List (ℚ × ZeroCell))
    (roots : List (ℚ × ℚ))
    (h : (zeroCoverCheck l a cells b && decide (zeroCoverRoots cells = roots)) = true) :
    (∀ I ∈ roots, ∃! z, z ∈ Ioo (I.1 : ℝ) I.2 ∧ sphericalBesselJ l z = 0) ∧
      ∀ x ∈ Ioc (a : ℝ) b, sphericalBesselJ l x = 0 → ∃ I ∈ roots, x ∈ Ioo (I.1 : ℝ) I.2 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hcover, rfl⟩ := h
  exact of_zeroCoverCheck hcover

end PDE.Analysis.SpecialFunctions
