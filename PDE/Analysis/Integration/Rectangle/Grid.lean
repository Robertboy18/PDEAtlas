/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Rectangle.MixedPrimitive

/-!
# Integrals over grids of rectangles

The coordinate lines `{y₀ = b}` and `{y₁ = b}` of the plane are null, so the closed rectangles of
a grid overlap only in null sets: for `f` integrable on `[x₀, x_N] × [y₀, y_M]` with increasing
breakpoints, the integral is the sum over the `N M` cells.

## Main results

* `volume_coordinate_eq`: the coordinate line `{y | y i = b}` of the plane is Lebesgue-null.
* `setIntegral_coordinateRectangle_split_left`: the integral over a rectangle splits at
  `y₀ = b`.
* `setIntegral_coordinateRectangle_split_right`: the integral over a rectangle splits at
  `y₁ = b`.
* `setIntegral_coordinateRectangle_eq_sum`: the integral over `[x₀, x_N] × [y₀, y_M]` is the sum
  of the integrals over the cells of the grid.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Finset (range sum_range_succ mem_range sum_congr)

namespace PDE.Analysis

/-- The coordinate line `{y | y i = b}` of the plane is Lebesgue-null. -/
theorem volume_coordinate_eq (i : Fin 2) (b : ℝ) : volume {y : ℝ^2 | y i = b} = 0 := by
  have hpre : {y : ℝ^2 | y i = b} =
      (planeEquiv : ℝ^2 → ℝ × ℝ) ⁻¹' (if i = 0 then {b} ×ˢ Set.univ else Set.univ ×ˢ {b}) := by
    ext y
    fin_cases i <;> simp [planeEquiv_apply]
  rw [hpre, measurePreserving_planeEquiv.measure_preimage_equiv, Measure.volume_eq_prod]
  split_ifs <;> simp [Measure.prod_prod]

/-- For `a ≤ b ≤ c`, `[a, b] × [d, e] ∪ [b, c] × [d, e] = [a, c] × [d, e]`. -/
theorem coordinateRectangle_union_left {a b c d e : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    coordinateRectangle a b d e ∪ coordinateRectangle b c d e = coordinateRectangle a c d e := by
  ext y
  simp only [mem_union, mem_coordinateRectangle, mem_Icc]
  constructor
  · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) <;> exact ⟨⟨by linarith, by linarith⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    rcases le_total (y 0) b with h | h
    · exact Or.inl ⟨⟨h1, h⟩, h3⟩
    · exact Or.inr ⟨⟨h, h2⟩, h3⟩

/-- For `a ≤ b ≤ c`, `[d, e] × [a, b] ∪ [d, e] × [b, c] = [d, e] × [a, c]`. -/
theorem coordinateRectangle_union_right {a b c d e : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    coordinateRectangle d e a b ∪ coordinateRectangle d e b c = coordinateRectangle d e a c := by
  ext y
  simp only [mem_union, mem_coordinateRectangle, mem_Icc]
  constructor
  · rintro (⟨h3, ⟨h1, h2⟩⟩ | ⟨h3, ⟨h1, h2⟩⟩) <;> exact ⟨h3, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨h3, ⟨h1, h2⟩⟩
    rcases le_total (y 1) b with h | h
    · exact Or.inl ⟨h3, ⟨h1, h⟩⟩
    · exact Or.inr ⟨h3, ⟨h, h2⟩⟩

/-- **Splitting a rectangle at `y₀ = b`.** -/
theorem setIntegral_coordinateRectangle_split_left {f : ℝ^2 → ℝ} {a b c d e : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) (hf : IntegrableOn f (coordinateRectangle a c d e)) :
    ∫ y in coordinateRectangle a c d e, f y =
      (∫ y in coordinateRectangle a b d e, f y) + ∫ y in coordinateRectangle b c d e, f y := by
  rw [← coordinateRectangle_union_left hab hbc] at hf ⊢
  refine setIntegral_union₀ ?_ (measurableSet_coordinateRectangle _ _ _ _).nullMeasurableSet
    (hf.mono_set subset_union_left) (hf.mono_set subset_union_right)
  refine measure_mono_null (fun y hy ↦ ?_) (volume_coordinate_eq 0 b)
  obtain ⟨⟨⟨_, h1⟩, _⟩, ⟨⟨h2, _⟩, _⟩⟩ := hy
  exact le_antisymm h1 h2

/-- **Splitting a rectangle at `y₁ = b`.** -/
theorem setIntegral_coordinateRectangle_split_right {f : ℝ^2 → ℝ} {a b c d e : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) (hf : IntegrableOn f (coordinateRectangle d e a c)) :
    ∫ y in coordinateRectangle d e a c, f y =
      (∫ y in coordinateRectangle d e a b, f y) + ∫ y in coordinateRectangle d e b c, f y := by
  rw [← coordinateRectangle_union_right hab hbc] at hf ⊢
  refine setIntegral_union₀ ?_ (measurableSet_coordinateRectangle _ _ _ _).nullMeasurableSet
    (hf.mono_set subset_union_left) (hf.mono_set subset_union_right)
  refine measure_mono_null (fun y hy ↦ ?_) (volume_coordinate_eq 1 b)
  obtain ⟨⟨_, ⟨_, h1⟩⟩, ⟨_, ⟨h2, _⟩⟩⟩ := hy
  exact le_antisymm h1 h2

/-- `[a', b'] × [c', d'] ⊆ [a, b] × [c, d]` when `a ≤ a'`, `b' ≤ b`, `c ≤ c'` and `d' ≤ d`. -/
theorem coordinateRectangle_mono {a b c d a' b' c' d' : ℝ} (ha : a ≤ a') (hb : b' ≤ b)
    (hc : c ≤ c') (hd : d' ≤ d) : coordinateRectangle a' b' c' d' ⊆ coordinateRectangle a b c d :=
  fun y ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ ↦ ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- A rectangle cut at the breakpoints `x₀ ≤ ⋯ ≤ x_N` of the first coordinate. -/
theorem setIntegral_coordinateRectangle_eq_sum_left {f : ℝ^2 → ℝ} (x : ℕ → ℝ) (hx : Monotone x)
    (d e : ℝ) (N : ℕ) (hf : IntegrableOn f (coordinateRectangle (x 0) (x N) d e)) :
    ∫ y in coordinateRectangle (x 0) (x N) d e, f y =
      ∑ i ∈ range N, ∫ y in coordinateRectangle (x i) (x (i + 1)) d e, f y := by
  induction N with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    refine setIntegral_measure_zero _ (measure_mono_null (fun y hy ↦ ?_)
      (volume_coordinate_eq 0 (x 0)))
    exact le_antisymm hy.1.2 hy.1.1
  | succ N ih =>
    rw [setIntegral_coordinateRectangle_split_left (hx (Nat.zero_le N)) (hx (Nat.le_succ N)) hf,
      ih (hf.mono_set (coordinateRectangle_mono le_rfl (hx (Nat.le_succ N)) le_rfl le_rfl)),
      sum_range_succ]

/-- A rectangle cut at the breakpoints `y₀ ≤ ⋯ ≤ y_M` of the second coordinate. -/
theorem setIntegral_coordinateRectangle_eq_sum_right {f : ℝ^2 → ℝ} (y : ℕ → ℝ) (hy : Monotone y)
    (a b : ℝ) (M : ℕ) (hf : IntegrableOn f (coordinateRectangle a b (y 0) (y M))) :
    ∫ p in coordinateRectangle a b (y 0) (y M), f p =
      ∑ j ∈ range M, ∫ p in coordinateRectangle a b (y j) (y (j + 1)), f p := by
  induction M with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    refine setIntegral_measure_zero _ (measure_mono_null (fun p hp ↦ ?_)
      (volume_coordinate_eq 1 (y 0)))
    exact le_antisymm hp.2.2 hp.2.1
  | succ M ih =>
    rw [setIntegral_coordinateRectangle_split_right (hy (Nat.zero_le M)) (hy (Nat.le_succ M)) hf,
      ih (hf.mono_set (coordinateRectangle_mono le_rfl le_rfl le_rfl (hy (Nat.le_succ M)))),
      sum_range_succ]

/-- **A rectangle as the sum of the cells of a grid.** -/
theorem setIntegral_coordinateRectangle_eq_sum {f : ℝ^2 → ℝ} (x y : ℕ → ℝ) (hx : Monotone x)
    (hy : Monotone y) (N M : ℕ)
    (hf : IntegrableOn f (coordinateRectangle (x 0) (x N) (y 0) (y M))) :
    ∫ p in coordinateRectangle (x 0) (x N) (y 0) (y M), f p =
      ∑ i ∈ range N, ∑ j ∈ range M,
        ∫ p in coordinateRectangle (x i) (x (i + 1)) (y j) (y (j + 1)), f p := by
  rw [setIntegral_coordinateRectangle_eq_sum_left x hx _ _ N hf]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' := mem_range.mp hi
  exact setIntegral_coordinateRectangle_eq_sum_right y hy _ _ M (hf.mono_set
    (coordinateRectangle_mono (hx (Nat.zero_le i)) (hx (by omega)) le_rfl le_rfl))

end PDE.Analysis
