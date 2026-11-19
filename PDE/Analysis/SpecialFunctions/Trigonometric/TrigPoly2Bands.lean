/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigPoly2CellsApriori

/-!
# A cover of the quadrant by bands of cells

A band `(a₀, a₁, s, t)` covers `a₀ h ≤ β ≤ a₁ h` (`h = π / (2N)`) by cells of width `s h` in `β`
and `t g` in `θ` (`g = π / (2P)`, `t ∣ P`), with vertices at the nodes `(a₀ + s i) h` and
`t k g`. A list of bands covers `[0, π/2] × [0, π/2]` when consecutive bands meet, the first starts
at `0` and the last ends at `N` (`bandsCover`). With bounds of the quadratic form at the vertices of
every band and the cell inequality of `quadForm_le_sq_of_cell` for the widths of every band, the
form is at most `ρ² |u|²` on the quadrant (`quadForm_le_of_bands`).
-/

@[expose] public noncomputable section

namespace PDE.Analysis.TrigPoly2

open Finset Set

variable {Mβ Mθ d d' : ℕ}

/-- A band `(a₀, a₁, s, t)` is well formed: `a₀ < a₁`, `0 < s ∣ a₁ - a₀`, `0 < t ∣ P`. -/
def isWellFormedBand (P : ℕ) (band : ℕ × ℕ × ℕ × ℕ) : Bool :=
  Nat.blt band.1 band.2.1 && Nat.blt 0 band.2.2.1 && ((band.2.1 - band.1) % band.2.2.1 == 0) &&
    Nat.blt 0 band.2.2.2 && (P % band.2.2.2 == 0)

/-- The bands are well formed and cover `[a, N]` consecutively. -/
def bandsCoverFrom (N P : ℕ) : ℕ → List (ℕ × ℕ × ℕ × ℕ) → Bool
  | a, [] => a == N
  | a, band :: rest => (band.1 == a) && isWellFormedBand P band && bandsCoverFrom N P band.2.1 rest

/-- The bands cover `[0, N]`. -/
def bandsCover (N P : ℕ) (bands : List (ℕ × ℕ × ℕ × ℕ)) : Bool := bandsCoverFrom N P 0 bands

theorem isWellFormedBand_spec {P : ℕ} {band : ℕ × ℕ × ℕ × ℕ} (h : isWellFormedBand P band = true) :
    band.1 < band.2.1 ∧ 0 < band.2.2.1 ∧ band.2.2.1 ∣ band.2.1 - band.1 ∧ 0 < band.2.2.2 ∧
      band.2.2.2 ∣ P := by
  simp only [isWellFormedBand, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, Nat.dvd_of_mod_eq_zero h3, h4, Nat.dvd_of_mod_eq_zero h5⟩

/-- A point of `(a h, N h]` lies in one of the bands. -/
theorem exists_band_of_bandsCoverFrom {N P : ℕ} {h : ℝ} (hh : 0 < h) :
    ∀ (bands : List (ℕ × ℕ × ℕ × ℕ)) (a : ℕ), bandsCoverFrom N P a bands = true →
      ∀ β, (a : ℝ) * h < β → β ≤ (N : ℝ) * h → ∃ band ∈ bands, isWellFormedBand P band = true ∧
        β ∈ Icc ((band.1 : ℝ) * h) ((band.2.1 : ℝ) * h)
  | [], a, hc, β, h1, h2 => by
    simp only [bandsCoverFrom, beq_iff_eq] at hc
    subst hc
    exact absurd h2 (not_le.mpr h1)
  | band :: rest, a, hc, β, h1, h2 => by
    simp only [bandsCoverFrom, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨ha, hok⟩, hrest⟩ := hc
    by_cases hb : β ≤ (band.2.1 : ℝ) * h
    · exact ⟨band, List.mem_cons_self, hok, ⟨by rw [ha]; exact h1.le, hb⟩⟩
    · obtain ⟨b', hb', hok', hmem⟩ := exists_band_of_bandsCoverFrom hh rest band.2.1 hrest β
        (not_le.mp hb) h2
      exact ⟨b', List.mem_cons_of_mem _ hb', hok', hmem⟩

/-- A point of `[0, N h]` lies in one of the bands. -/
theorem exists_band_of_bandsCover {N P : ℕ} (hN : 0 < N) {h : ℝ} (hh : 0 < h)
    {bands : List (ℕ × ℕ × ℕ × ℕ)} (hc : bandsCover N P bands = true) {β : ℝ}
    (hβ : β ∈ Icc 0 ((N : ℝ) * h)) : ∃ band ∈ bands, isWellFormedBand P band = true ∧
      β ∈ Icc ((band.1 : ℝ) * h) ((band.2.1 : ℝ) * h) := by
  rcases eq_or_lt_of_le hβ.1 with h0 | h0
  · cases bands with
    | nil => simp [bandsCover, bandsCoverFrom] at hc; omega
    | cons band rest =>
      simp only [bandsCover, bandsCoverFrom, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨ha, hok⟩, -⟩ := hc
      obtain ⟨h1, -⟩ := isWellFormedBand_spec hok
      refine ⟨band, List.mem_cons_self, hok, ⟨by rw [ha, ← h0]; simp, ?_⟩⟩
      rw [← h0]; positivity
  · exact exists_band_of_bandsCoverFrom hh bands 0 hc β (by simpa using h0) hβ.2

/-- A point of `[x₀, x₀ + n w]` lies in a cell `[x₀ + i w, x₀ + (i + 1) w]`, `i < n`. -/
theorem exists_cell_index {x x₀ w : ℝ} {n : ℕ} (hw : 0 < w) (hn : 0 < n)
    (hx : x ∈ Icc x₀ (x₀ + n * w)) : ∃ i < n, x ∈ Icc (x₀ + i * w) (x₀ + (i + 1) * w) := by
  have hq : 0 ≤ (x - x₀) / w := div_nonneg (by linarith [hx.1]) hw.le
  refine ⟨min ⌊(x - x₀) / w⌋₊ (n - 1), by omega, ?_, ?_⟩
  · have h1 : ((min ⌊(x - x₀) / w⌋₊ (n - 1) : ℕ) : ℝ) ≤ (x - x₀) / w :=
      (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le hq)
    rw [le_div_iff₀ hw] at h1
    linarith
  · rcases le_total ⌊(x - x₀) / w⌋₊ (n - 1) with h | h
    · rw [min_eq_left h]
      have h2 := Nat.lt_floor_add_one ((x - x₀) / w)
      rw [div_lt_iff₀ hw] at h2
      linarith
    · rw [min_eq_right h]
      have : ((n - 1 : ℕ) : ℝ) + 1 = n := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]
      exact hx.2

/-- **A quadratic form from a cover by bands.** -/
theorem quadForm_le_of_bands (G : Fin d → Fin d' → TrigPoly2 Mβ Mθ ℝ)
    {R1 R2 S1 S2 : Fin d → Fin d' → ℝ}
    (hR1 : ∀ i k, (G i k).moment 1 0 ≤ R1 i k) (hR2 : ∀ i k, (G i k).moment 2 0 ≤ R2 i k)
    (hS1 : ∀ i k, (G i k).moment 0 1 ≤ S1 i k) (hS2 : ∀ i k, (G i k).moment 0 2 ≤ S2 i k)
    {A₁ A₂ B₁ B₂ : ℝ} (hA₁ : ∑ i, ∑ k, R1 i k ^ 2 ≤ A₁) (hA₂ : ∑ i, ∑ k, S1 i k ^ 2 ≤ A₂)
    (hB₁ : 0 ≤ B₁) (hB₁' : ∑ i, ∑ k, R2 i k ^ 2 ≤ B₁ ^ 2) (hB₂ : 0 ≤ B₂)
    (hB₂' : ∑ i, ∑ k, S2 i k ^ 2 ≤ B₂ ^ 2) {N P : ℕ} (hN : 0 < N) (hP : 0 < P)
    {bands : List (ℕ × ℕ × ℕ × ℕ)} (hcov : bandsCover N P bands = true)
    (V : ℕ × ℕ × ℕ × ℕ → ℝ) {ρ : ℝ}
    (hcell : ∀ band ∈ bands,
      V band + (((band.2.2.1 : ℝ) * (Real.pi / (2 * N))) ^ 2 * A₁ +
        ((band.2.2.2 : ℝ) * (Real.pi / (2 * P))) ^ 2 * A₂) / 4 +
      (((band.2.2.1 : ℝ) * (Real.pi / (2 * N))) ^ 2 * B₁ +
        ((band.2.2.2 : ℝ) * (Real.pi / (2 * P))) ^ 2 * B₂) / 4 * ρ ≤ ρ ^ 2 ∧
      (((band.2.2.1 : ℝ) * (Real.pi / (2 * N))) ^ 2 * B₁ +
        ((band.2.2.2 : ℝ) * (Real.pi / (2 * P))) ^ 2 * B₂) / 4 < ρ)
    (hvert : ∀ band ∈ bands, ∀ i ≤ (band.2.1 - band.1) / band.2.2.1, ∀ k ≤ P / band.2.2.2,
      ∀ u : Fin d' → ℝ, quadForm G (((band.1 + band.2.2.1 * i : ℕ) : ℝ) * (Real.pi / (2 * N)))
        (((band.2.2.2 * k : ℕ) : ℝ) * (Real.pi / (2 * P))) u ≤ V band * ∑ k, u k ^ 2)
    {β θ : ℝ} (hβ : β ∈ Icc 0 (Real.pi / 2)) (hθ : θ ∈ Icc 0 (Real.pi / 2)) (u : Fin d' → ℝ) :
    quadForm G β θ u ≤ ρ ^ 2 * ∑ k, u k ^ 2 := by
  set h := Real.pi / (2 * N)
  set g := Real.pi / (2 * P)
  have hh : 0 < h := by positivity
  have hg : 0 < g := by positivity
  have hNh : (N : ℝ) * h = Real.pi / 2 := by simp only [h]; field_simp
  have hPg : (P : ℝ) * g = Real.pi / 2 := by simp only [g]; field_simp
  obtain ⟨band, hb, hok, hβb⟩ := exists_band_of_bandsCover hN hh hcov (hNh ▸ hβ)
  obtain ⟨hlt, hs, ⟨q, hq⟩, ht, ⟨r, hr⟩⟩ := isWellFormedBand_spec hok
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hr0 : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hsub : (band.2.1 : ℝ) = band.2.2.1 * q + band.1 := by
    exact_mod_cast Nat.eq_add_of_sub_eq hlt.le hq
  have hPr : (P : ℝ) = band.2.2.2 * r := by exact_mod_cast hr
  obtain ⟨i, hi, hβi⟩ := exists_cell_index (by positivity) hq0
    (show β ∈ Icc ((band.1 : ℝ) * h) ((band.1 : ℝ) * h + q * ((band.2.2.1 : ℝ) * h)) from
      ⟨hβb.1, hβb.2.trans_eq (by rw [hsub]; ring)⟩)
  obtain ⟨k, hk, hθk⟩ := exists_cell_index (by positivity) hr0
    (show θ ∈ Icc 0 (0 + r * ((band.2.2.2 : ℝ) * g)) from
      ⟨hθ.1, hθ.2.trans_eq (by rw [← hPg, hPr]; ring)⟩)
  have hv : ∀ i ≤ q, ∀ k ≤ r, quadForm G ((band.1 : ℝ) * h + i * ((band.2.2.1 : ℝ) * h))
      (0 + k * ((band.2.2.2 : ℝ) * g)) u ≤ V band * ∑ k, u k ^ 2 := fun i hi k hk ↦ by
    have := hvert band hb i (by rwa [hq, Nat.mul_div_cancel_left _ hs]) k
      (by rwa [hr, Nat.mul_div_cancel_left _ ht]) u
    convert this using 2 <;> push_cast <;> ring
  obtain ⟨hV, hB⟩ := hcell band hb
  refine quadForm_le_sq_of_cell G hR1 hR2 hS1 hS2 hA₁ hA₂ hB₁ hB₁' hB₂ hB₂'
    (by linarith [mul_pos (Nat.cast_pos.2 hs : (0 : ℝ) < band.2.2.1) hh])
    (by linarith [mul_pos (Nat.cast_pos.2 ht : (0 : ℝ) < band.2.2.2) hg]) (V := V band) (ρ := ρ)
    (by convert hV using 3 <;> ring) (by convert hB using 2; ring) u ?_ hβi hθk
  rintro x (rfl | rfl) y (rfl | rfl)
  · exact hv i hi.le k hk.le
  · simpa only [Nat.cast_add, Nat.cast_one] using hv i hi.le (k + 1) hk
  · simpa only [Nat.cast_add, Nat.cast_one] using hv (i + 1) hi k hk.le
  · simpa only [Nat.cast_add, Nat.cast_one] using hv (i + 1) hi (k + 1) hk

end PDE.Analysis.TrigPoly2
