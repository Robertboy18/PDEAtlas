/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Numerics.Certificates.CellPairs.Pairs

/-!
# Certificate loops over near cell pairs and ratio pieces

The near pairs of `CellPairs.forall_of_cellPairs` are checked by index arithmetic, never stored.
For the cell `(a, b)` of the product mesh, `nearCheck` runs one `natAll` loop over the flat
offset index `k < W²`, `(d, e) = (k / W, k % W)`, and calls a Boolean `check a b c d'` on the
cells `(a + d, b + e)` and `(a + d, b - e)` that exist; `cellsCheck` runs it over a range of
flat cell indices `p ↦ (p mod (n + 1), p / (n + 1))`, so a certificate module covers one range and
the ranges glue by `forall_lt_add`. `forall_of_nearChecks` turns a sound `check` and the loops
into the conclusion of `forall_of_cellPairs`, leaving only the far pairs.

Inside a cell-pair check the increment ratio `|h₂| / |h₁|` lies in an interval computed from the
cells; `piecesCheck` runs a check on every piece `[b_k, b_{k+1}]` of a partition that meets the
interval and skips the others (`piecesCheck_spec`, `exists_piece_of_piecesCheck`), with the
intersection test `ratioMeets` in natural-number arithmetic (`ratioMeets_of_mem`), which is how
Chen and Hou reduce the `h₁/h₂` dimension (Part I, Section 5.4.5, "Verifying the stability
conditions": pieces outside `[r_l, r_u]` are marked as satisfied).

## Main definitions

* `nearCheck`: the near-pair check of one cell `(a, b)` with window `W`, one loop over `W * W`.
* `cellsCheck`: the near-pair checks of a range of flat cell indices.
* `piecesCheck`: the loop over the ratio pieces that meet the ratio interval of a cell pair.
* `ratioMeets`: the intersection test of a piece with the ratio interval in natural numbers.

## Main results

* `forall_of_nearChecks`: from a sound `check` and passing near-pair checks of every cell,
  `Φ x z` holds on all pairs of `D` with `x₀ ≤ z₀`, given the far pairs.
* `nearCheck_spec`, `cellsCheck_spec`: what the two loops certify.
* `nearCheck_of_forall_flat`: near-pair checks of all flat cell indices give the checks of all
  cells.
* `piecesCheck_spec`: a piece that meets the ratio interval passed its check.
* `exists_piece_of_piecesCheck`: a ratio `t` in `[b₀, b_N]` lies in a piece whose check passed.
* `ratioMeets_of_mem`: `ratioMeets` holds on every piece that contains a ratio of the interval.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 5.4.5.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

namespace CAS.Numerics.CellPairs

open Set

/-- The near-pair check of the cell `(a, b)` with window `W`: for all offsets `d, e < W`, the
pairs with the cells `(a + d, b + e)` and, for `0 < e`, `(a + d, b - e)` that exist in the mesh
(`a + d ≤ n`, `b + e ≤ m`, `e ≤ b`) pass `check`. One loop over `k < W * W` with `d = k / W`,
`e = k % W`. -/
def nearCheck (n m W : ℕ) (check : ℕ → ℕ → ℕ → ℕ → Bool) (a b : ℕ) : Bool :=
  natAll (W * W) fun k ↦
    !Nat.ble (a + k / W) n ||
      ((!Nat.ble (b + k % W) m || check a b (a + k / W) (b + k % W)) &&
        (!(Nat.blt 0 (k % W) && Nat.ble (k % W) b) || check a b (a + k / W) (b - k % W)))

/-- The near-pair checks of the flat cell indices `start, …, start + count - 1`, where the flat
index `p` stands for the cell `(p mod (n + 1), p / (n + 1))`. -/
def cellsCheck (n m W : ℕ) (check : ℕ → ℕ → ℕ → ℕ → Bool) (start count : ℕ) : Bool :=
  natAll count fun k ↦ nearCheck n m W check ((start + k) % (n + 1)) ((start + k) / (n + 1))

variable {n m W : ℕ} {check : ℕ → ℕ → ℕ → ℕ → Bool}

/-- `!(x ≤ y)` as a Boolean test. -/
theorem not_ble_eq_true {x y : ℕ} : ((!Nat.ble x y) = true) ↔ y < x := by
  rw [Bool.not_eq_true', ← Bool.not_eq_true, Nat.ble_eq, not_le]

/-- What `nearCheck` certifies for the cell `(a, b)`, `b ≤ m`. -/
theorem nearCheck_spec {a b : ℕ} (h : nearCheck n m W check a b = true) (hb : b ≤ m) {d e : ℕ}
    (hd : d < W) (he : e < W) (hdn : a + d ≤ n) :
    (b + e ≤ m → check a b (a + d) (b + e) = true) ∧
      (e ≤ b → check a b (a + d) (b - e) = true) := by
  have := natAll_div_mod_spec (p := fun d e ↦
    !Nat.ble (a + d) n ||
      ((!Nat.ble (b + e) m || check a b (a + d) (b + e)) &&
        (!(Nat.blt 0 e && Nat.ble e b) || check a b (a + d) (b - e)))) h hd he
  simp only [Bool.or_eq_true, Bool.and_eq_true, not_ble_eq_true] at this
  rcases this with h' | ⟨h₁, h₂⟩
  · exact absurd hdn (not_le.2 h')
  have up : b + e ≤ m → check a b (a + d) (b + e) = true := fun hem ↦ by
    rcases h₁ with h' | h'
    · exact absurd hem (not_le.2 h')
    · exact h'
  refine ⟨up, fun heb ↦ ?_⟩
  rcases Nat.eq_zero_or_pos e with he0 | he0
  · subst he0
    simpa using up (by simpa using hb)
  · have hg : (Nat.blt 0 e && Nat.ble e b) = true := by
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
      exact ⟨he0, heb⟩
    rcases h₂ with h' | h'
    · simp [hg] at h'
    · exact h'

/-- What `cellsCheck` certifies for a flat cell index in its range. -/
theorem cellsCheck_spec {start count : ℕ} (h : cellsCheck n m W check start count = true)
    {p : ℕ} (hp₁ : start ≤ p) (hp₂ : p < start + count) :
    nearCheck n m W check (p % (n + 1)) (p / (n + 1)) = true := by
  have := natAll_spec h (j := p - start) (by omega)
  simpa only [Nat.add_sub_cancel' hp₁] using this

/-- Near-pair checks of all flat cell indices give the checks of all cells. -/
theorem nearCheck_of_forall_flat
    (h : ∀ p < (n + 1) * (m + 1), nearCheck n m W check (p % (n + 1)) (p / (n + 1)) = true)
    {a b : ℕ} (ha : a ≤ n) (hb : b ≤ m) : nearCheck n m W check a b = true := by
  have hlt : b * (n + 1) + a < (n + 1) * (m + 1) := by
    calc b * (n + 1) + a < b * (n + 1) + (n + 1) := by omega
      _ = (b + 1) * (n + 1) := by ring
      _ ≤ (m + 1) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = (n + 1) * (m + 1) := by ring
  have := h _ hlt
  have hmod : (b * (n + 1) + a) % (n + 1) = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hdiv : (b * (n + 1) + a) / (n + 1) = b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  rwa [hmod, hdiv] at this

/-- **Two-point statements from near-pair checks.** If `check a b c d = true` implies `Φ x z`
for `x` in the cell `(a, b)` and `z` in the cell `(c, d)` with `x₀ ≤ z₀`, and the near-pair
check of every cell passes, then `Φ x z` holds on all pairs of `D` with `x₀ ≤ z₀`, given the far
pairs. -/
theorem forall_of_nearChecks {y y' : ℕ → ℝ} (hy : Monotone y) {D : Set (ℝ^2)}
    (hD : ∀ x ∈ D, y 0 ≤ x 0 ∧ y' 0 ≤ x 1) {Φ : ℝ^2 → ℝ^2 → Prop}
    (sound : ∀ a b c d, check a b c d = true → ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 →
      x ∈ box y y' n m a b → z ∈ box y y' n m c d → Φ x z)
    (hcheck : ∀ a ≤ n, ∀ b ≤ m, nearCheck n m W check a b = true)
    (far : ∀ a c, a ≤ c → c ≤ n → ∀ b ≤ m, ∀ d ≤ m, (a + W ≤ c ∨ b + W ≤ d ∨ d + W ≤ b) →
      ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → x ∈ box y y' n m a b → z ∈ box y y' n m c d → Φ x z) :
    ∀ x ∈ D, ∀ z ∈ D, x 0 ≤ z 0 → Φ x z :=
  forall_of_cellPairs hy hD
    (fun a ha b hb d hd e he hdn hem ↦ sound a b (a + d) (b + e)
      ((nearCheck_spec (hcheck a ha b hb) hb hd he hdn).1 hem))
    (fun a ha b hb d hd e he hdn heb ↦ sound a b (a + d) (b - e)
      ((nearCheck_spec (hcheck a ha b hb) hb hd he hdn).2 heb))
    far

/-! ### Ratio pieces -/

/-- The ratio-piece loop: every piece `k < N` for which `meets k` holds passes `pieceCheck k`;
the other pieces are skipped. `meets k` is a test that the piece meets the ratio interval of the
cell pair, for instance `ratioMeets`. -/
def piecesCheck (N : ℕ) (meets pieceCheck : ℕ → Bool) : Bool :=
  natAll N fun k ↦ !meets k || pieceCheck k

/-- What `piecesCheck` certifies: a piece that meets the ratio interval passed its check. -/
theorem piecesCheck_spec {N : ℕ} {meets pieceCheck : ℕ → Bool}
    (h : piecesCheck N meets pieceCheck = true) {k : ℕ} (hk : k < N) (hm : meets k = true) :
    pieceCheck k = true := by
  have := natAll_spec h hk
  simpa [hm] using this

/-- A ratio `t` in `[b₀, b_N]` lies in a piece whose check passed, if `meets` holds on every piece
containing `t`. -/
theorem exists_piece_of_piecesCheck {N : ℕ} {meets pieceCheck : ℕ → Bool}
    (h : piecesCheck N meets pieceCheck = true) (hN : 0 < N) {b : ℕ → ℝ} {t : ℝ}
    (htb : t ∈ Icc (b 0) (b N)) (hmeets : ∀ k < N, t ∈ Icc (b k) (b (k + 1)) → meets k = true) :
    ∃ k < N, t ∈ Icc (b k) (b (k + 1)) ∧ pieceCheck k = true := by
  obtain ⟨k, hk, htk⟩ := PDE.Analysis.Approximation.exists_mem_mesh_piece hN htb
  exact ⟨k, hk, htk, piecesCheck_spec h hk (hmeets k hk htk)⟩

/-- The intersection test of the piece `[B_k / 2^s, B_{k+1} / 2^s]` with the ratio interval
`[u / U, v / V]` in natural-number arithmetic: `B_k V ≤ v 2^s` and `u 2^s ≤ B_{k+1} U`. With
`V = 0` (no lower bound of the denominator) the upper end is `∞` and the first test holds. -/
def ratioMeets (B : ℕ → ℕ) (s u U v V k : ℕ) : Bool :=
  Nat.ble (B k * V) (v * 2 ^ s) && Nat.ble (u * 2 ^ s) (B (k + 1) * U)

/-- `ratioMeets` holds on every piece that contains a ratio `t` of the interval. -/
theorem ratioMeets_of_mem {B : ℕ → ℕ} {s u U v V k : ℕ} {t : ℝ} (hU : 0 < U)
    (hlo : (u : ℝ) / U ≤ t) (hhi : t * V ≤ v)
    (htk : t ∈ Icc ((B k : ℝ) / 2 ^ s) ((B (k + 1) : ℝ) / 2 ^ s)) :
    ratioMeets B s u U v V k = true := by
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have ht0 : (0 : ℝ) ≤ t := (div_nonneg (Nat.cast_nonneg _) h2.le).trans htk.1
  simp only [ratioMeets, Bool.and_eq_true, Nat.ble_eq]
  constructor
  · have h₁ : (B k : ℝ) ≤ t * 2 ^ s := (div_le_iff₀ h2).1 htk.1
    have : (B k : ℝ) * V ≤ v * 2 ^ s := by
      calc (B k : ℝ) * V ≤ t * 2 ^ s * V := mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg _)
        _ = t * V * 2 ^ s := by ring
        _ ≤ v * 2 ^ s := mul_le_mul_of_nonneg_right hhi h2.le
    exact_mod_cast this
  · have h₁ : t * 2 ^ s ≤ B (k + 1) := (le_div_iff₀ h2).1 htk.2
    have h₂ : (u : ℝ) ≤ t * U := (div_le_iff₀ hU').1 hlo
    have : (u : ℝ) * 2 ^ s ≤ B (k + 1) * U := by
      calc (u : ℝ) * 2 ^ s ≤ t * U * 2 ^ s := mul_le_mul_of_nonneg_right h₂ h2.le
        _ = t * 2 ^ s * U := by ring
        _ ≤ B (k + 1) * U := mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg _)
    exact_mod_cast this

end CAS.Numerics.CellPairs
