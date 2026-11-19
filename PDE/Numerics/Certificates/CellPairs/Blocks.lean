/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.CellPairs.Checks

/-!
# Hierarchical block pairs

Checking a two-point inequality on every pair of cells within physical distance `R` costs one
check per pair: Chen and Hou's case (a.1) of Supplementary material I, Section 8 (pairs with
`|x - z| ≤ R₁ = 5000`, cell index gaps up to `n_{R₁}` with `y_{n_{R₁}} > R₁`) is of the order of
`10^10` cell pairs on the 748-point mesh. Grouping cells into blocks of `2^ℓ × 2^ℓ` cells covers
all pairs with a number of block pairs proportional to the number of cells, as in the
interaction lists of multipole methods: a pair of cells is checked as a cell pair if its cells
are less than `w` cells apart in each coordinate (level `0`), and otherwise as the pair of its
blocks at the unique level `ℓ` where the blocks are `w` or more blocks apart but their parent
blocks (level `ℓ + 1`) are not (`forall_of_blockPairs`).

The blocks of level `ℓ` are the cells of the coarse mesh `coarsen y ℓ`, every `2^ℓ`-th point of
`y`, with `n / 2^ℓ` inner cells and its own outer cell (`mem_cell_coarsen`), so a block pair is
checked exactly like a cell pair, with block data (for instance maxima of the cell data over the
cells of the block, `exists_mem_cell_of_mem_cell_coarsen`) and the block geometry. The outer
block of level `ℓ` starts at `y_{(n / 2^ℓ) 2^ℓ}`, so it contains finite cells besides the outer
cell of `y`, and its data must cover both. `levelCheck` enumerates the block pairs of one block
by index arithmetic: the offsets below `2w` in each coordinate (`lt_add_of_nearAt_one`) filtered
by the interaction test `isInteraction` (`isInteraction_iff`); `forall_of_levelChecks` assembles
the near-pair checks of level `0` and the block-pair checks of all levels into the two-point
statement.

## Main definitions

* `coarsen`: the mesh of level `ℓ`, every `2^ℓ`-th point of `y`.
* `NearAt`: two cells lie in blocks of level `ℓ` less than `w` blocks apart in each coordinate.
* `isInteraction`: the Boolean interaction test of block pairs, not near but parents near.
* `levelCheck`: the block-pair checks of one block of a level, enumerated over offsets below `2w`.

## Main results

* `mem_cell_coarsen`: a cell of `y` lies in its block, the cell `a / 2^ℓ` of the mesh of level `ℓ`.
* `exists_mem_cell_of_mem_cell_coarsen`: a point of a block lies in one of the cells of the block.
* `forall_of_blockPairs`: a two-point statement holds on all pairs with `x₀ ≤ z₀` once it holds on
  the near cell pairs and on the interaction block pairs of every level `ℓ < L`.
* `isInteraction_iff`: the interaction test is exactly "not near, parents near".
* `levelCheck_spec`: what a passed `levelCheck` certifies about the interaction pairs of a block.
* `forall_of_levelChecks`: sound near-pair and block-pair checks that pass for every cell and block
  give the two-point statement on all pairs of `D` with `x₀ ≤ z₀`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Supplementary
  material I, Section 8, case (a.1), (8.4).
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace CAS.Numerics.CellPairs

open Set

/-- The mesh of level `ℓ`: every `2^ℓ`-th point of `y`. Its cell `A` contains the cells
`A 2^ℓ, …, (A + 1) 2^ℓ - 1` of `y`, and its outer cell, of index `n / 2^ℓ`, all cells of `y` from
`(n / 2^ℓ) 2^ℓ` on. -/
def coarsen (y : ℕ → ℝ) (ℓ : ℕ) : ℕ → ℝ := fun k ↦ y (k * 2 ^ ℓ)

variable {y : ℕ → ℝ} {n ℓ a : ℕ} {t : ℝ}

/-- The coarsened mesh of a monotone mesh is monotone. -/
theorem monotone_coarsen (hy : Monotone y) : Monotone (coarsen y ℓ) :=
  fun _ _ h ↦ hy (Nat.mul_le_mul_right _ h)

/-- A cell of `y` lies in its block, the cell `a / 2^ℓ` of the mesh of level `ℓ`. -/
theorem mem_cell_coarsen (hy : Monotone y) (ha : a ≤ n) (ht : t ∈ cell y n a) :
    t ∈ cell (coarsen y ℓ) (n / 2 ^ ℓ) (a / 2 ^ ℓ) := by
  have hpos : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  refine ⟨(hy (Nat.div_mul_le_self a _)).trans ht.1, fun hlt ↦ ?_⟩
  have han : a < n := by
    rcases ha.lt_or_eq with h | h
    · exact h
    · exact absurd hlt (by rw [h]; exact lt_irrefl _)
  have hsucc : a + 1 ≤ (a / 2 ^ ℓ + 1) * 2 ^ ℓ := by
    have := Nat.lt_div_mul_add (a := a) hpos
    rw [Nat.add_mul, Nat.one_mul]
    omega
  exact (ht.2 han).trans (hy hsucc)

/-- A point of a block of level `ℓ` lies in one of the cells of the block: the converse of
`mem_cell_coarsen`, so maxima of cell data over the cells of a block bound the block. -/
theorem exists_mem_cell_of_mem_cell_coarsen {A : ℕ} (hA : A ≤ n / 2 ^ ℓ)
    (ht : t ∈ cell (coarsen y ℓ) (n / 2 ^ ℓ) A) : ∃ a ≤ n, a / 2 ^ ℓ = A ∧ t ∈ cell y n a := by
  classical
  have hs : 0 < 2 ^ ℓ := Nat.two_pow_pos ℓ
  set s := 2 ^ ℓ with hsdef
  have hAs : A * s ≤ n := (Nat.mul_le_mul_right s hA).trans (Nat.div_mul_le_self n s)
  set hi := if A < n / s then (A + 1) * s - 1 else n with hhi
  have hlohi : A * s ≤ hi := by
    simp only [hhi]
    split_ifs with h
    · rw [Nat.add_mul, Nat.one_mul]
      omega
    · exact hAs
  have hhin : hi ≤ n := by
    simp only [hhi]
    split_ifs with h
    · have : (A + 1) * s ≤ n / s * s := Nat.mul_le_mul_right s h
      have := Nat.div_mul_le_self n s
      omega
    · exact le_rfl
  have hhis : hi < (A + 1) * s := by
    simp only [hhi]
    split_ifs with h
    · have : 0 < (A + 1) * s := Nat.mul_pos (Nat.succ_pos A) hs
      omega
    · have hA' : A = n / s := le_antisymm hA (not_lt.1 h)
      rw [hA']
      exact Nat.lt_div_mul_add hs |>.trans_le (by rw [Nat.add_mul, Nat.one_mul])
  have hP : y (A * s) ≤ t := ht.1
  set a := Nat.findGreatest (fun k ↦ y k ≤ t) hi with ha
  have ha₁ : A * s ≤ a := Nat.le_findGreatest (P := fun k ↦ y k ≤ t) hlohi hP
  have ha₂ : a ≤ hi := Nat.findGreatest_le hi
  have hya : y a ≤ t := Nat.findGreatest_spec (P := fun k ↦ y k ≤ t) hlohi hP
  have hdiv : a / s = A := by
    refine le_antisymm ?_ ?_
    · have : a < (A + 1) * s := lt_of_le_of_lt ha₂ hhis
      exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hs).2 this)
    · exact (Nat.le_div_iff_mul_le hs).2 ha₁
  refine ⟨a, ha₂.trans hhin, hdiv, hya, fun han ↦ ?_⟩
  rcases lt_or_eq_of_le ha₂ with hlt | heq
  · have := Nat.findGreatest_is_greatest (P := fun k ↦ y k ≤ t) (lt_add_one a) hlt
    exact (not_le.1 this).le
  · -- the last cell of an inner block ends at the next block point
    have hAlt : A < n / s := by
      by_contra h
      simp only [hhi, h, ite_false] at heq
      omega
    simp only [hhi, hAlt, ite_true] at heq
    have h1 : a + 1 = (A + 1) * s := by
      have : 0 < (A + 1) * s := Nat.mul_pos (Nat.succ_pos A) hs
      omega
    rw [h1]
    exact ht.2 hAlt

/-- The cells `(a, b)` and `(c, d)` lie in blocks of level `ℓ` less than `w` blocks apart in each
coordinate. -/
def NearAt (w ℓ a b c d : ℕ) : Prop :=
  c / 2 ^ ℓ < a / 2 ^ ℓ + w ∧ a / 2 ^ ℓ < c / 2 ^ ℓ + w ∧
    d / 2 ^ ℓ < b / 2 ^ ℓ + w ∧ b / 2 ^ ℓ < d / 2 ^ ℓ + w

/-- Nearness at level `0` is nearness of the indices. -/
theorem nearAt_zero_iff {w a b c d : ℕ} :
    NearAt w 0 a b c d ↔ c < a + w ∧ a < c + w ∧ d < b + w ∧ b < d + w := by
  simp [NearAt]

/-- Nearness at level `ℓ + 1` is nearness at level `1` of the blocks of level `ℓ`. -/
theorem nearAt_succ_iff {w ℓ a b c d : ℕ} :
    NearAt w (ℓ + 1) a b c d ↔
      NearAt w 1 (a / 2 ^ ℓ) (b / 2 ^ ℓ) (c / 2 ^ ℓ) (d / 2 ^ ℓ) := by
  simp only [NearAt, Nat.div_div_eq_div_mul, pow_one, ← pow_succ]

/-- Nearness at level `ℓ` is nearness at level `0` of the blocks of level `ℓ`. -/
theorem nearAt_iff_zero {w ℓ a b c d : ℕ} :
    NearAt w ℓ a b c d ↔
      NearAt w 0 (a / 2 ^ ℓ) (b / 2 ^ ℓ) (c / 2 ^ ℓ) (d / 2 ^ ℓ) := by
  simp [NearAt]

/-- All cells are near at a level `L` with `n, m < 2^L`. -/
theorem nearAt_of_lt_pow {w L n m a b c d : ℕ} (hw : 1 ≤ w) (hn : n < 2 ^ L) (hm : m < 2 ^ L)
    (ha : a ≤ n) (hc : c ≤ n) (hb : b ≤ m) (hd : d ≤ m) : NearAt w L a b c d := by
  have h0 : ∀ k, k < 2 ^ L → k / 2 ^ L = 0 := fun k hk ↦ Nat.div_eq_of_lt hk
  simp only [NearAt, h0 a (by omega), h0 c (by omega), h0 b (by omega), h0 d (by omega)]
  omega

/-- **Covering by hierarchical block pairs.** A two-point statement `Φ x z` holds for all
`x, z ∈ D` with `x₀ ≤ z₀` if it holds on the cell pairs less than `w` cells apart in each
coordinate, and, for every level `ℓ < L`, on the pairs of blocks of level `ℓ` (cells of the
coarse meshes) that are `w` or more blocks apart while their parent blocks are less than `w`
apart. Here `w ≥ 1` and `n, m < 2^L`. -/
theorem forall_of_blockPairs {y y' : ℕ → ℝ} {n m w L : ℕ} (hy : Monotone y)
    (hy' : Monotone y') (hw : 1 ≤ w) (hn : n < 2 ^ L) (hm : m < 2 ^ L) {D : Set (ℝ^2)}
    (hD : ∀ x ∈ D, y 0 ≤ x 0 ∧ y' 0 ≤ x 1) {Φ : ℝ^2 → ℝ^2 → Prop}
    (near : ∀ a c, a ≤ c → c ≤ n → ∀ b ≤ m, ∀ d ≤ m, NearAt w 0 a b c d →
      ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → x ∈ box y y' n m a b → z ∈ box y y' n m c d → Φ x z)
    (blocks : ∀ ℓ < L, ∀ A C, A ≤ C → C ≤ n / 2 ^ ℓ → ∀ B ≤ m / 2 ^ ℓ, ∀ E ≤ m / 2 ^ ℓ,
      ¬ NearAt w 0 A B C E → NearAt w 1 A B C E →
      ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 →
        x ∈ box (coarsen y ℓ) (coarsen y' ℓ) (n / 2 ^ ℓ) (m / 2 ^ ℓ) A B →
        z ∈ box (coarsen y ℓ) (coarsen y' ℓ) (n / 2 ^ ℓ) (m / 2 ^ ℓ) C E → Φ x z) :
    ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → Φ x z := by
  classical
  intro x hx z hz hxz
  obtain ⟨a, c, hac, hcn, ha, hc⟩ := exists_mem_cell_le (n := n) hy (hD x hx).1 hxz
  obtain ⟨b, hbm, hb⟩ := exists_mem_cell (n := m) (y := y') (hD x hx).2
  obtain ⟨d, hdm, hd⟩ := exists_mem_cell (n := m) (y := y') (hD z hz).2
  have hex : ∃ ℓ, NearAt w ℓ a b c d :=
    ⟨L, nearAt_of_lt_pow hw hn hm (hac.trans hcn) hcn hbm hdm⟩
  set ℓ₀ := Nat.find hex with hℓ₀
  have hnear₀ : NearAt w ℓ₀ a b c d := Nat.find_spec hex
  have hℓL : ℓ₀ ≤ L := Nat.find_min' hex (nearAt_of_lt_pow hw hn hm (hac.trans hcn) hcn hbm hdm)
  rcases Nat.eq_zero_or_pos ℓ₀ with h0 | hpos
  · rw [h0] at hnear₀
    exact near a c hac hcn b hbm d hdm hnear₀ x hx z hz hxz ⟨ha, hb⟩ ⟨hc, hd⟩
  · set ℓ := ℓ₀ - 1
    have hℓ : ℓ + 1 = ℓ₀ := Nat.sub_add_cancel hpos
    have hfar : ¬ NearAt w ℓ a b c d := Nat.find_min hex (by omega)
    have hnear₁ : NearAt w (ℓ + 1) a b c d := hℓ ▸ hnear₀
    refine blocks ℓ (by omega) (a / 2 ^ ℓ) (c / 2 ^ ℓ) (Nat.div_le_div_right hac)
      (Nat.div_le_div_right hcn) (b / 2 ^ ℓ) (Nat.div_le_div_right hbm) (d / 2 ^ ℓ)
      (Nat.div_le_div_right hdm) (fun h ↦ hfar (nearAt_iff_zero.2 h))
      (nearAt_succ_iff.1 hnear₁) x hx z hz hxz
      ⟨mem_cell_coarsen hy (hac.trans hcn) ha, mem_cell_coarsen hy' hbm hb⟩
      ⟨mem_cell_coarsen hy hcn hc, mem_cell_coarsen hy' hdm hd⟩

/-- Blocks whose parents are near lie less than `2w` blocks apart: `C < A + 2w` for `A ≤ C`. -/
theorem lt_add_of_nearAt_one {w A B C E : ℕ} (h : NearAt w 1 A B C E) :
    C < A + 2 * w ∧ E < B + 2 * w ∧ B < E + 2 * w := by
  simp only [NearAt, pow_one] at h
  omega

/-- The Boolean interaction test of block pairs: not near, parents near. -/
def isInteraction (w A B C E : ℕ) : Bool :=
  !(Nat.blt C (A + w) && Nat.blt A (C + w) && Nat.blt E (B + w) && Nat.blt B (E + w)) &&
    (Nat.blt (C / 2) (A / 2 + w) && Nat.blt (A / 2) (C / 2 + w) &&
      Nat.blt (E / 2) (B / 2 + w) && Nat.blt (B / 2) (E / 2 + w))

/-- A pair of blocks that is not near at level `0` but near at level `1` passes the Boolean
interaction test. -/
theorem isInteraction_of {w A B C E : ℕ} (hfar : ¬ NearAt w 0 A B C E)
    (hnear : NearAt w 1 A B C E) : isInteraction w A B C E = true := by
  simp only [NearAt, pow_zero, Nat.div_one, pow_one] at hfar hnear
  obtain ⟨h1, h2, h3, h4⟩ := hnear
  have e1 : (Nat.blt C (A + w) && Nat.blt A (C + w) && Nat.blt E (B + w) &&
      Nat.blt B (E + w)) = false := by
    cases h : (Nat.blt C (A + w) && Nat.blt A (C + w) && Nat.blt E (B + w) && Nat.blt B (E + w))
    · rfl
    · simp only [Bool.and_eq_true, Nat.blt_eq] at h
      exact absurd ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩ hfar
  have e2 : (Nat.blt (C / 2) (A / 2 + w) && Nat.blt (A / 2) (C / 2 + w) &&
      Nat.blt (E / 2) (B / 2 + w) && Nat.blt (B / 2) (E / 2 + w)) = true := by
    simp [Nat.blt_eq, h1, h2, h3, h4]
  rw [isInteraction, e1, e2]
  rfl

/-- The interaction test is exactly "not near, parents near". -/
theorem isInteraction_iff {w A B C E : ℕ} :
    isInteraction w A B C E = true ↔ ¬ NearAt w 0 A B C E ∧ NearAt w 1 A B C E := by
  refine ⟨fun h ↦ ?_, fun h ↦ isInteraction_of h.1 h.2⟩
  simp only [isInteraction, Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at h
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨fun hn ↦ ?_, by
    simp only [NearAt, pow_one]
    exact ⟨h₂.1.1.1, h₂.1.1.2, h₂.1.2, h₂.2⟩⟩
  simp only [NearAt, pow_zero, Nat.div_one] at hn
  obtain ⟨n₁, n₂, n₃, n₄⟩ := hn
  have : (Nat.blt C (A + w) && Nat.blt A (C + w) && Nat.blt E (B + w) &&
      Nat.blt B (E + w)) = true := by
    simp only [Bool.and_eq_true, Nat.blt_eq]
    exact ⟨⟨⟨n₁, n₂⟩, n₃⟩, n₄⟩
  rw [this] at h₁
  exact Bool.noConfusion h₁

/-- The block-pair checks of the block `(A, B)` of a level with `n` and `m` inner blocks: every
interaction pair `(A, B), (C, E)` with `C ≥ A` passes `check`, enumerated over the offsets
below `2w`. -/
def levelCheck (n m w : ℕ) (check : ℕ → ℕ → ℕ → ℕ → Bool) (A B : ℕ) : Bool :=
  nearCheck n m (2 * w) (fun A B C E ↦ !isInteraction w A B C E || check A B C E) A B

/-- What `levelCheck` certifies. -/
theorem levelCheck_spec {n m w : ℕ} {check : ℕ → ℕ → ℕ → ℕ → Bool} {A B : ℕ}
    (h : levelCheck n m w check A B = true) (hB : B ≤ m) {C E : ℕ} (hAC : A ≤ C) (hC : C ≤ n)
    (hE : E ≤ m)
    (hfar : ¬ NearAt w 0 A B C E) (hnear : NearAt w 1 A B C E) : check A B C E = true := by
  have hbd := lt_add_of_nearAt_one hnear
  have hI := isInteraction_of hfar hnear
  have hC' : C = A + (C - A) := by omega
  rcases le_total B E with hBE | hEB
  · have hE' : E = B + (E - B) := by omega
    have := (nearCheck_spec h hB (d := C - A) (e := E - B) (by omega) (by omega) (by omega)).1
      (by omega)
    rw [← hC', ← hE'] at this
    simpa [hI] using this
  · have hE' : E = B - (B - E) := by omega
    have := (nearCheck_spec h hB (d := C - A) (e := B - E) (by omega) (by omega) (by omega)).2
      (by omega)
    rw [← hC', ← hE'] at this
    simpa [hI] using this

/-- **Two-point statements from level checks.** If the near-pair checks of level `0` (window `w`)
and the block-pair checks of the levels `ℓ < L` pass for every cell and block, and the checks are
sound for the cells and the blocks (cells of the coarse meshes), then `Φ x z` holds on all pairs
of `D` with `x₀ ≤ z₀`. -/
theorem forall_of_levelChecks {y y' : ℕ → ℝ} {n m w L : ℕ} (hy : Monotone y)
    (hy' : Monotone y') (hw : 1 ≤ w) (hn : n < 2 ^ L) (hm : m < 2 ^ L) {D : Set (ℝ^2)}
    (hD : ∀ x ∈ D, y 0 ≤ x 0 ∧ y' 0 ≤ x 1) {Φ : ℝ^2 → ℝ^2 → Prop}
    {check₀ : ℕ → ℕ → ℕ → ℕ → Bool} {check : ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    (sound₀ : ∀ a b c d, check₀ a b c d = true → ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 →
      x ∈ box y y' n m a b → z ∈ box y y' n m c d → Φ x z)
    (near : ∀ a ≤ n, ∀ b ≤ m, nearCheck n m w check₀ a b = true)
    (sound : ∀ ℓ < L, ∀ A B C E, check ℓ A B C E = true → ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 →
      x ∈ box (coarsen y ℓ) (coarsen y' ℓ) (n / 2 ^ ℓ) (m / 2 ^ ℓ) A B →
      z ∈ box (coarsen y ℓ) (coarsen y' ℓ) (n / 2 ^ ℓ) (m / 2 ^ ℓ) C E → Φ x z)
    (levels : ∀ ℓ < L, ∀ A ≤ n / 2 ^ ℓ, ∀ B ≤ m / 2 ^ ℓ,
      levelCheck (n / 2 ^ ℓ) (m / 2 ^ ℓ) w (check ℓ) A B = true) :
    ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → Φ x z := by
  refine forall_of_blockPairs hy hy' hw hn hm hD ?_ ?_
  · intro a c hac hcn b hbm d hdm hnear x hx z hz hxz hxb hzb
    rw [nearAt_zero_iff] at hnear
    have hc' : c = a + (c - a) := by omega
    rcases le_total b d with hbd | hdb
    · have hd' : d = b + (d - b) := by omega
      have := (nearCheck_spec (near a (hac.trans hcn) b hbm) hbm (d := c - a) (e := d - b)
        (by omega) (by omega) (by omega)).1 (by omega)
      rw [← hc', ← hd'] at this
      exact sound₀ a b c d this x hx z hz hxz hxb hzb
    · have hd' : d = b - (b - d) := by omega
      have := (nearCheck_spec (near a (hac.trans hcn) b hbm) hbm (d := c - a) (e := b - d)
        (by omega) (by omega) (by omega)).2 (by omega)
      rw [← hc', ← hd'] at this
      exact sound₀ a b c d this x hx z hz hxz hxb hzb
  · intro ℓ hℓ A C hAC hCn B hBm E hEm hfar hnear x hx z hz hxz hxb hzb
    exact sound ℓ hℓ A B C E (levelCheck_spec (levels ℓ hℓ A (hAC.trans hCn) B hBm) hBm hAC hCn hEm
      hfar hnear) x hx z hz hxz hxb hzb

end CAS.Numerics.CellPairs
