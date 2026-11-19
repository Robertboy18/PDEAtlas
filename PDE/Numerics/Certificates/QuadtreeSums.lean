/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.AxialPowerCells
public import PDE.Analysis.Integration.Rectangle.MixedPrimitive

/-!
# Upper bounds of plane integrals by quadtree sums

A quadtree of a rectangle is given by its preorder bits: `true` splits a cell into its four
quarters (`PlaneCell.quarter`, in the order south-west, south-east, north-west, north-east),
`false` is a leaf. `quadtreeWalk leaf fuel bits C` reads one tree for the cell `C` from the bits
and adds the integers `leaf` returns on its leaves; it fails (`none`) if a leaf fails, the bits run
out or the depth exceeds the fuel. `quadtreeWalk_sound`: if every leaf returning `some n` bounds
`∫⁻` of `F` over its closed rectangle by `n / 2^K` (in the scale `c`), the total bounds `∫⁻` over
`C`. The tree needs no checked covering: every tree covers its root. `hexBits` decodes the bits from
a hexadecimal string.

## Main definitions

* `PlaneCell.rect`: the closed rectangle of a cell.
* `PlaneCell.quarter`: the four quarters of a cell.
* `quadtreeWalk`: the sum of the leaf integers of one tree read from preorder bits, with the
  remaining bits.
* `hexBits`: the bits of a hexadecimal string.

## Main results

* `quadtreeWalk_sound`: if every leaf returning `some n` has `n ≥ 0` and
  `∫⁻ F ≤ ofReal (c n / 2^K)` over its rectangle, the walk bounds `∫⁻ F` over the root.
* `PlaneCell.rect_subset_quarters`: the rectangle of a cell is covered by those of its quarters.
* `PlaneCell.volume_rect`: the area of a cell.
* `PlaneCell.lintegral_le`: `∫⁻` over a cell of a function bounded by `ofReal M` is at most
  `ofReal (M · area)`.
-/

@[expose] public section

namespace CAS.Numerics

open MeasureTheory Set PDE.Analysis
open scoped ENNReal

/-- The closed rectangle of a cell. -/
def PlaneCell.rect (C : PlaneCell) : Set (EuclideanSpace ℝ (Fin 2)) :=
  coordinateRectangle C.left C.right C.bottom C.top

/-- The cell is an ordered rectangle of the closed quadrant. -/
def PlaneCell.Ordered (C : PlaneCell) : Prop :=
  0 ≤ C.left ∧ C.left ≤ C.right ∧ 0 ≤ C.bottom ∧ C.bottom ≤ C.top

/-- The four quarters of a cell, south-west, south-east, north-west and north-east. -/
def PlaneCell.quarter (C : PlaneCell) (i : Fin 4) : PlaneCell :=
  match i with
  | 0 => ⟨C.left, (C.left + C.right) / 2, C.bottom, (C.bottom + C.top) / 2⟩
  | 1 => ⟨(C.left + C.right) / 2, C.right, C.bottom, (C.bottom + C.top) / 2⟩
  | 2 => ⟨C.left, (C.left + C.right) / 2, (C.bottom + C.top) / 2, C.top⟩
  | 3 => ⟨(C.left + C.right) / 2, C.right, (C.bottom + C.top) / 2, C.top⟩

/-- The quarters of an ordered cell are ordered. -/
theorem PlaneCell.Ordered.quarter {C : PlaneCell} (h : C.Ordered) (i : Fin 4) :
    (C.quarter i).Ordered := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold PlaneCell.Ordered
  fin_cases i <;> simp only [PlaneCell.quarter] <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- The closed rectangle of a cell is covered by the rectangles of its four quarters. -/
theorem PlaneCell.rect_subset_quarters (C : PlaneCell) :
    C.rect ⊆ (C.quarter 0).rect ∪ (C.quarter 1).rect ∪ (C.quarter 2).rect ∪ (C.quarter 3).rect := by
  intro y hy
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hy
  have hm : (((C.left + C.right) / 2 : ℚ) : ℝ) = ((C.left : ℝ) + C.right) / 2 := by
    push_cast; ring
  have hn : (((C.bottom + C.top) / 2 : ℚ) : ℝ) = ((C.bottom : ℝ) + C.top) / 2 := by
    push_cast; ring
  rcases le_total (y 0) ((C.left + C.right) / 2) with hx | hx <;>
    rcases le_total (y 1) ((C.bottom + C.top) / 2) with hz | hz
  · refine Or.inl (Or.inl (Or.inl ?_))
    exact ⟨⟨h1, by simp only [PlaneCell.quarter]; rw [hm]; exact hx⟩,
      ⟨h3, by simp only [PlaneCell.quarter]; rw [hn]; exact hz⟩⟩
  · refine Or.inl (Or.inr ?_)
    exact ⟨⟨h1, by simp only [PlaneCell.quarter]; rw [hm]; exact hx⟩,
      ⟨by simp only [PlaneCell.quarter]; rw [hn]; exact hz, h4⟩⟩
  · refine Or.inl (Or.inl (Or.inr ?_))
    exact ⟨⟨by simp only [PlaneCell.quarter]; rw [hm]; exact hx, h2⟩,
      ⟨h3, by simp only [PlaneCell.quarter]; rw [hn]; exact hz⟩⟩
  · refine Or.inr ?_
    exact ⟨⟨by simp only [PlaneCell.quarter]; rw [hm]; exact hx, h2⟩,
      ⟨by simp only [PlaneCell.quarter]; rw [hn]; exact hz, h4⟩⟩

/-- The closed rectangle of a cell is the preimage of `[left, right] × [bottom, top]` under
`planeEquiv`. -/
theorem PlaneCell.rect_eq_preimage (C : PlaneCell) :
    C.rect = planeEquiv ⁻¹' (Icc (C.left : ℝ) C.right ×ˢ Icc (C.bottom : ℝ) C.top) := by
  ext y
  exact Iff.rfl

/-- The area of a cell. -/
theorem PlaneCell.volume_rect {C : PlaneCell} (h : C.Ordered) :
    volume C.rect = ENNReal.ofReal (((C.right - C.left) * (C.top - C.bottom) : ℚ) : ℝ) := by
  rw [PlaneCell.rect_eq_preimage, measurePreserving_planeEquiv.measure_preimage
    (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul]
  · push_cast; ring_nf
  · have : (C.left : ℝ) ≤ C.right := by exact_mod_cast h.2.1
    linarith

/-- `∫⁻` over a cell of a function bounded by `ofReal M` is at most `ofReal (M · area)`. -/
theorem PlaneCell.lintegral_le {C : PlaneCell} (h : C.Ordered)
    {F : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞} {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ y ∈ C.rect, F y ≤ ENNReal.ofReal M) :
    ∫⁻ y in C.rect, F y ≤
      ENNReal.ofReal (M * (((C.right - C.left) * (C.top - C.bottom) : ℚ) : ℝ)) := by
  calc ∫⁻ y in C.rect, F y ≤ ∫⁻ _ in C.rect, ENNReal.ofReal M :=
        setLIntegral_mono measurable_const hF
    _ = ENNReal.ofReal M * volume C.rect := setLIntegral_const _ _
    _ = _ := by
        rw [PlaneCell.volume_rect h, ← ENNReal.ofReal_mul hM]

/-- One tree for the cell `C`, read from the preorder bits: the sum of the leaf integers and the
remaining bits. -/
def quadtreeWalk (leaf : PlaneCell → Option ℤ) : ℕ → List Bool → PlaneCell →
    Option (ℤ × List Bool)
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | _ + 1, false :: rest, C => (leaf C).map fun n ↦ (n, rest)
  | fuel + 1, true :: rest, C =>
    match quadtreeWalk leaf fuel rest (C.quarter 0) with
    | none => none
    | some (n₀, r₀) =>
      match quadtreeWalk leaf fuel r₀ (C.quarter 1) with
      | none => none
      | some (n₁, r₁) =>
        match quadtreeWalk leaf fuel r₁ (C.quarter 2) with
        | none => none
        | some (n₂, r₂) =>
          match quadtreeWalk leaf fuel r₂ (C.quarter 3) with
          | none => none
          | some (n₃, r₃) => some (n₀ + n₁ + n₂ + n₃, r₃)

/-- **Soundness of the quadtree walk**: if every leaf returning `some n` has `n ≥ 0` and
`∫⁻ F ≤ ofReal (c n / 2^K)` over its rectangle, the walk bounds `∫⁻ F` over the root. -/
theorem quadtreeWalk_sound {leaf : PlaneCell → Option ℤ} {F : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞}
    {c : ℝ} (hc : 0 ≤ c) {K : ℕ}
    (hleaf : ∀ C : PlaneCell, C.Ordered → ∀ n, leaf C = some n →
      0 ≤ n ∧ ∫⁻ y in C.rect, F y ≤ ENNReal.ofReal (c * (n / 2 ^ K))) :
    ∀ (fuel : ℕ) (bits : List Bool) (C : PlaneCell) (n : ℤ) (rest : List Bool), C.Ordered →
      quadtreeWalk leaf fuel bits C = some (n, rest) →
      0 ≤ n ∧ ∫⁻ y in C.rect, F y ≤ ENNReal.ofReal (c * (n / 2 ^ K))
  | 0, _, _, _, _, _, h => by simp [quadtreeWalk] at h
  | _ + 1, [], _, _, _, _, h => by simp [quadtreeWalk] at h
  | _ + 1, false :: rest, C, n, rest', hC, h => by
    simp only [quadtreeWalk, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨m, hm, rfl, rfl⟩ := h
    exact hleaf C hC m hm
  | fuel + 1, true :: rest, C, n, rest', hC, h => by
    simp only [quadtreeWalk] at h
    split at h
    · cases h
    rename_i n₀ r₀ h₀
    split at h
    · cases h
    rename_i n₁ r₁ h₁
    split at h
    · cases h
    rename_i n₂ r₂ h₂
    split at h
    · cases h
    rename_i n₃ r₃ h₃
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨p₀, b₀⟩ := quadtreeWalk_sound hc hleaf fuel rest _ n₀ r₀ (hC.quarter 0) h₀
    obtain ⟨p₁, b₁⟩ := quadtreeWalk_sound hc hleaf fuel r₀ _ n₁ r₁ (hC.quarter 1) h₁
    obtain ⟨p₂, b₂⟩ := quadtreeWalk_sound hc hleaf fuel r₁ _ n₂ r₂ (hC.quarter 2) h₂
    obtain ⟨p₃, b₃⟩ := quadtreeWalk_sound hc hleaf fuel r₂ _ n₃ r₃ (hC.quarter 3) h₃
    refine ⟨by omega, ?_⟩
    have hnn : ∀ m : ℤ, 0 ≤ m → 0 ≤ c * ((m : ℝ) / 2 ^ K) := fun m hm ↦
      mul_nonneg hc (div_nonneg (by exact_mod_cast hm) (by positivity))
    calc ∫⁻ y in C.rect, F y
        ≤ ∫⁻ y in (C.quarter 0).rect ∪ (C.quarter 1).rect ∪ (C.quarter 2).rect ∪
            (C.quarter 3).rect, F y := lintegral_mono_set (C.rect_subset_quarters)
      _ ≤ (∫⁻ y in (C.quarter 0).rect, F y) + (∫⁻ y in (C.quarter 1).rect, F y) +
            (∫⁻ y in (C.quarter 2).rect, F y) + ∫⁻ y in (C.quarter 3).rect, F y := by
          refine (lintegral_union_le _ _ _).trans ?_
          gcongr
          refine (lintegral_union_le _ _ _).trans ?_
          gcongr
          exact lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal (c * (n₀ / 2 ^ K)) + ENNReal.ofReal (c * (n₁ / 2 ^ K)) +
            ENNReal.ofReal (c * (n₂ / 2 ^ K)) + ENNReal.ofReal (c * (n₃ / 2 ^ K)) := by
          gcongr
      _ = ENNReal.ofReal (c * (((n₀ + n₁ + n₂ + n₃ : ℤ) : ℝ) / 2 ^ K)) := by
          rw [← ENNReal.ofReal_add (hnn _ p₀) (hnn _ p₁),
            ← ENNReal.ofReal_add (add_nonneg (hnn _ p₀) (hnn _ p₁)) (hnn _ p₂),
            ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hnn _ p₀) (hnn _ p₁)) (hnn _ p₂))
              (hnn _ p₃)]
          congr 1
          push_cast
          ring

/-- The four bits of a hexadecimal digit `0-9`, `a-f`, most significant first; other characters
give some four bits, so the data must use these digits only. -/
def hexDigitBits (c : Char) : List Bool :=
  let n := if c.toNat ≤ '9'.toNat then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  [decide (n / 8 % 2 = 1), decide (n / 4 % 2 = 1), decide (n / 2 % 2 = 1), decide (n % 2 = 1)]

/-- The bits of a hexadecimal string, ignoring the newline character. -/
def hexBits (s : String) : List Bool :=
  (s.toList.filter fun c ↦ c ≠ '\n').flatMap hexDigitBits

end CAS.Numerics
