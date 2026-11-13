/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.RootSigns
public import PDE.Fluid.Stokes.Ball.MeridionalRoots
public import PDE.Fluid.Stokes.Ball.AzimuthalRoots

/-!
# Certificates for the roots of the boundary functions below `100`

An enclosure list `E : List (ℕ × ℕ)` stands for the open intervals `(a / 2 ^ 40, b / 2 ^ 40)`
of its entries `(a, b)`. `JZeroEnclosures l E` states that the intervals increase, lie in
`(0, 100)`, contain one zero of `j_l` each, and contain every zero of `j_l` in `(0, 100]`.

The finite checks below use only the signs of `rootPointSigns` at the endpoints of the
intervals and at `100`. The lemmas at the end read `enclosuresSorted` as inequalities between
the real endpoints `enclosureLo` and `enclosureHi`.

* `chainCheck l E F`: the zeros of `j_{l+1}` interlace with those of `j_l`. At a zero of
  `j_{l+1}` its derivative is `j_l`, so on each interval between consecutive zeros of `j_l` the
  function `j_{l+1}` crosses zero in one direction only, and a sign change locates the zero.
  `JZeroEnclosures l E` and the check give `JZeroEnclosures (l + 1) F`.
* `azimuthalCheck l E F`: one root of the azimuthal boundary function in each interval between
  consecutive zeros of `j_l` (and before the first), located by a sign change; if the last
  interval has no enclosure, the sign at `100` shows that its root lies beyond `100`.
* `meridionalCheck l E F`: the same for the meridional boundary function, with the zeros of `j_l`
  and the point `γ = √(l (l - 1)(l + 2))` as breakpoints.
-/

@[expose] public section

open PDE.Analysis.SpecialFunctions

namespace PDE.Fluid.Stokes.Ball

/-- The left endpoint `a / 2 ^ 40` of entry `k` of an enclosure list. -/
noncomputable def enclosureLo (E : List (ℕ × ℕ)) (k : ℕ) : ℝ := (E.getD k (0, 0)).1 / 2 ^ 40

/-- The right endpoint `b / 2 ^ 40` of entry `k` of an enclosure list. -/
noncomputable def enclosureHi (E : List (ℕ × ℕ)) (k : ℕ) : ℝ := (E.getD k (0, 0)).2 / 2 ^ 40

/-- The numerator `100 · 2 ^ 40` of the cut `100`. -/
def cutNumerator : ℕ := 100 * 2 ^ 40

/-- The entries of an enclosure list are nonempty, increasing and disjoint, and lie in
`(0, 100)`. -/
def enclosuresSorted (E : List (ℕ × ℕ)) : Bool :=
  (List.range E.length).all fun k ↦
    decide (0 < (E.getD k (0, 0)).1) && decide ((E.getD k (0, 0)).1 < (E.getD k (0, 0)).2) &&
      decide ((E.getD k (0, 0)).2 < cutNumerator) &&
      (decide (E.length ≤ k + 1) || decide ((E.getD k (0, 0)).2 < (E.getD (k + 1) (0, 0)).1))

/-- The zeros of `j_l` in `(0, 100]`: one in each interval of `E`, and no others. -/
structure JZeroEnclosures (l : ℕ) (E : List (ℕ × ℕ)) : Prop where
  sorted : enclosuresSorted E = true
  existsUnique : ∀ k < E.length,
    ∃! z, z ∈ Set.Ioo (enclosureLo E k) (enclosureHi E k) ∧ sphericalBesselJ l z = 0
  complete : ∀ x ∈ Set.Ioc (0 : ℝ) 100, sphericalBesselJ l x = 0 →
    ∃ k < E.length, x ∈ Set.Ioo (enclosureLo E k) (enclosureHi E k)

/-- The signs `(g_l, g_{l+1}, b_Y, b_Z)` at the point `100`. -/
def cutSigns (l : ℕ) : ℤ × ℤ × ℤ × ℤ := rootPointSigns l cutNumerator

/-- The zeros of `j_{l+1}` from those of `j_l`: entry `k` of `F` lies between entries `k` and
`k + 1` of `E` (or between the last entry of `E` and `100`); `j_{l+1}` has the sign of `-j_l` at
its left end and of `j_l` at its right end; `F` has as many entries as `E` or one fewer, and in
the second case `j_{l+1}` and `j_l` have opposite signs at `100`. -/
def chainCheck (l : ℕ) (E F : List (ℕ × ℕ)) : Bool :=
  enclosuresSorted F &&
    (decide (E.length = 0 ∧ F.length = 0) ||
      (decide (F.length = E.length ∨ F.length + 1 = E.length) &&
        (List.range F.length).all (fun k ↦
          decide ((E.getD k (0, 0)).2 ≤ (F.getD k (0, 0)).1) &&
            (decide (E.length ≤ k + 1) ||
              decide ((F.getD k (0, 0)).2 ≤ (E.getD (k + 1) (0, 0)).1)) &&
            (match rootPointSigns l (F.getD k (0, 0)).1, rootPointSigns l (F.getD k (0, 0)).2 with
            | (a, b, _, _), (c, d, _, _) =>
              decide (a ≠ 0 ∧ c = a ∧ b = -a ∧ d = a))) &&
        (match cutSigns l with
          | (a, b, _, _) => decide (a ≠ 0 ∧ b ≠ 0 ∧ (F.length + 1 = E.length → b = -a)))))

/-- The azimuthal roots of degree `l` from the zeros of `j_l`: entry `k` of `F` lies in the
interval between zeros `k - 1` and `k` of `j_l` (from `0` for `k = 0`, up to `100` for
`k = E.length`); the azimuthal function has the sign of `j_l` at the left end and the opposite
sign at the right end; `F` has as many entries as `E` or one more, and in the first case the
azimuthal function and `j_l` have the same sign at `100`. -/
def azimuthalCheck (l : ℕ) (E F : List (ℕ × ℕ)) : Bool :=
  enclosuresSorted F && decide (F.length = E.length ∨ F.length = E.length + 1) &&
    (List.range F.length).all (fun k ↦
      (decide (k = 0) || decide ((E.getD (k - 1) (0, 0)).2 ≤ (F.getD k (0, 0)).1)) &&
        (decide (E.length ≤ k) || decide ((F.getD k (0, 0)).2 ≤ (E.getD k (0, 0)).1)) &&
        (match rootPointSigns l (F.getD k (0, 0)).1, rootPointSigns l (F.getD k (0, 0)).2 with
        | (a, _, _, z), (c, _, _, w) => decide (a ≠ 0 ∧ c = a ∧ z = a ∧ w = -a))) &&
    (match cutSigns l with
      | (a, _, _, z) => decide (a ≠ 0 ∧ z ≠ 0 ∧ (F.length = E.length → z = a)))

/-- `γ² = l (l - 1)(l + 2)` as a natural number. -/
def gammaSq (l : ℕ) : ℕ := l * (l - 1) * (l + 2)

/-- `γ` is a breakpoint of the meridional regions when `l ≥ 2` and `γ < 100`. -/
def gammaActive (l : ℕ) : Bool := decide (2 ≤ l ∧ gammaSq l < 10 ^ 4)

/-- The number of zeros of `j_l` in `E` below `γ`. -/
def gammaPosition (l : ℕ) (E : List (ℕ × ℕ)) : ℕ :=
  ((List.range E.length).filter fun k ↦
    decide ((E.getD k (0, 0)).2 ^ 2 < gammaSq l * 2 ^ 80)).length

/-- The sign of `x² - γ²` at `x = n / 2 ^ 40` (`1` for `x > γ`, else `-1`). -/
def gammaSign (l n : ℕ) : ℤ := if gammaSq l * 2 ^ 80 < n ^ 2 then 1 else -1

/-- Breakpoint `i` (counted from `1`) of the meridional regions: `none` for `γ`, `some k` for
zero `k` of `j_l`. -/
def meridionalBreakpoint (l : ℕ) (E : List (ℕ × ℕ)) (i : ℕ) : Option ℕ :=
  if gammaActive l then
    if i ≤ gammaPosition l E then some (i - 1)
    else if i = gammaPosition l E + 1 then none
    else some (i - 2)
  else some (i - 1)

/-- The number of interior breakpoints of the meridional regions. -/
def meridionalBreakpointCount (l : ℕ) (E : List (ℕ × ℕ)) : ℕ :=
  E.length + if gammaActive l then 1 else 0

/-- The left end of entry `k` lies above breakpoint `k` (`k ≥ 1`). -/
def meridionalLeftCheck (l : ℕ) (E : List (ℕ × ℕ)) (k a : ℕ) : Bool :=
  decide (k = 0) ||
    match meridionalBreakpoint l E k with
    | some j => decide ((E.getD j (0, 0)).2 ≤ a)
    | none => decide (gammaSq l * 2 ^ 80 < a ^ 2)

/-- The right end of entry `k` lies below breakpoint `k + 1` (or below `100`). -/
def meridionalRightCheck (l : ℕ) (E : List (ℕ × ℕ)) (k b : ℕ) : Bool :=
  decide (meridionalBreakpointCount l E ≤ k) ||
    match meridionalBreakpoint l E (k + 1) with
    | some j => decide (b ≤ (E.getD j (0, 0)).1)
    | none => decide (b ^ 2 < gammaSq l * 2 ^ 80)

/-- The meridional roots of degree `l`: entry `k` of `F` lies in region `k` between consecutive
breakpoints (the zeros of `j_l` and, when active, `γ`, which lies outside the intervals of `E`);
the function `j_l (x² - γ²) b_Y` is negative at the left end and positive at the right end;
`F` has one entry per region or one fewer, and in the second case `j_l (x² - γ²) b_Y` is
negative at `100`. -/
def meridionalCheck (l : ℕ) (E F : List (ℕ × ℕ)) : Bool :=
  enclosuresSorted F &&
    decide (F.length = meridionalBreakpointCount l E + 1 ∨
      F.length = meridionalBreakpointCount l E) &&
    (!gammaActive l || (List.range E.length).all fun k ↦
      decide ((E.getD k (0, 0)).2 ^ 2 < gammaSq l * 2 ^ 80 ∨
        gammaSq l * 2 ^ 80 < (E.getD k (0, 0)).1 ^ 2)) &&
    (List.range F.length).all (fun k ↦
      meridionalLeftCheck l E k (F.getD k (0, 0)).1 &&
        meridionalRightCheck l E k (F.getD k (0, 0)).2 &&
        (match rootPointSigns l (F.getD k (0, 0)).1, rootPointSigns l (F.getD k (0, 0)).2 with
        | (a, _, y, _), (c, _, v, _) =>
          let σ := a * gammaSign l (F.getD k (0, 0)).1
          decide (a ≠ 0 ∧ c * gammaSign l (F.getD k (0, 0)).2 = σ ∧ y = -σ ∧ v = σ))) &&
    (match cutSigns l with
      | (a, _, y, _) => decide (a ≠ 0 ∧ y ≠ 0 ∧
        (F.length = meridionalBreakpointCount l E → y = -(a * gammaSign l cutNumerator))))

/-! ### Enclosure lists -/

/-- Division by `2 ^ 40` of a strict inequality between naturals. -/
theorem natCast_div_two_pow_forty_lt {a b : ℕ} (h : a < b) : (a : ℝ) / 2 ^ 40 < b / 2 ^ 40 :=
  div_lt_div_of_pos_right (by exact_mod_cast h) (by positivity)

/-- Division by `2 ^ 40` of an inequality between naturals. -/
theorem natCast_div_two_pow_forty_le {a b : ℕ} (h : a ≤ b) : (a : ℝ) / 2 ^ 40 ≤ b / 2 ^ 40 :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

/-- A dyadic point with positive numerator is positive. -/
theorem natCast_div_two_pow_forty_pos {a : ℕ} (h : 0 < a) : 0 < (a : ℝ) / 2 ^ 40 := by
  have : (0 : ℝ) < a := by exact_mod_cast h
  positivity

/-- The cut `cutNumerator / 2 ^ 40` is the point `100`. -/
theorem cutNumerator_div_two_pow_forty : (cutNumerator : ℝ) / 2 ^ 40 = 100 := by
  unfold cutNumerator
  push_cast
  norm_num

/-- The conditions of `enclosuresSorted` at entry `k`. -/
theorem enclosuresSorted_spec {E : List (ℕ × ℕ)} (h : enclosuresSorted E = true) {k : ℕ}
    (hk : k < E.length) :
    0 < (E.getD k (0, 0)).1 ∧ (E.getD k (0, 0)).1 < (E.getD k (0, 0)).2 ∧
      (E.getD k (0, 0)).2 < cutNumerator ∧
      (E.length ≤ k + 1 ∨ (E.getD k (0, 0)).2 < (E.getD (k + 1) (0, 0)).1) := by
  have h' := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h'
  exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

/-- In a sorted enclosure list, entry `i` ends before entry `j` starts when `i < j`. -/
theorem getD_snd_lt_getD_fst_of_enclosuresSorted {E : List (ℕ × ℕ)}
    (h : enclosuresSorted E = true) {i j : ℕ} (hij : i < j) (hj : j < E.length) :
    (E.getD i (0, 0)).2 < (E.getD j (0, 0)).1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  induction d with
  | zero =>
    rcases (enclosuresSorted_spec h (show i < E.length by omega)).2.2.2 with h₁ | h₁
    · omega
    · simpa using h₁
  | succ d ih =>
    have h₁ := ih (by omega) (by omega)
    have h₂ := enclosuresSorted_spec h (show i + d + 1 < E.length by omega)
    rcases h₂.2.2.2 with h₃ | h₃
    · omega
    · have h₄ : i + (d + 1) + 1 = i + d + 1 + 1 := by omega
      rw [h₄]
      exact (h₁.trans h₂.2.1).trans h₃

/-- The left endpoints of a sorted enclosure list are positive. -/
theorem enclosureLo_pos {E : List (ℕ × ℕ)} (h : enclosuresSorted E = true) {k : ℕ}
    (hk : k < E.length) : 0 < enclosureLo E k :=
  natCast_div_two_pow_forty_pos (enclosuresSorted_spec h hk).1

/-- Each entry of a sorted enclosure list is a nonempty interval. -/
theorem enclosureLo_lt_enclosureHi {E : List (ℕ × ℕ)} (h : enclosuresSorted E = true) {k : ℕ}
    (hk : k < E.length) : enclosureLo E k < enclosureHi E k :=
  natCast_div_two_pow_forty_lt (enclosuresSorted_spec h hk).2.1

/-- The right endpoints of a sorted enclosure list lie below `100`. -/
theorem enclosureHi_lt_hundred {E : List (ℕ × ℕ)} (h : enclosuresSorted E = true) {k : ℕ}
    (hk : k < E.length) : enclosureHi E k < 100 := by
  rw [← cutNumerator_div_two_pow_forty]
  exact natCast_div_two_pow_forty_lt (enclosuresSorted_spec h hk).2.2.1

/-- In a sorted enclosure list, interval `i` lies to the left of interval `j` when `i < j`. -/
theorem enclosureHi_lt_enclosureLo {E : List (ℕ × ℕ)} (h : enclosuresSorted E = true)
    {i j : ℕ} (hij : i < j) (hj : j < E.length) : enclosureHi E i < enclosureLo E j :=
  natCast_div_two_pow_forty_lt (getD_snd_lt_getD_fst_of_enclosuresSorted h hij hj)

/-- The intervals of a sorted enclosure list are disjoint. -/
theorem eq_of_mem_enclosure {E : List (ℕ × ℕ)} (h : enclosuresSorted E = true) {i j : ℕ}
    (hi : i < E.length) (hj : j < E.length) {x : ℝ}
    (hxi : x ∈ Set.Ioo (enclosureLo E i) (enclosureHi E i))
    (hxj : x ∈ Set.Ioo (enclosureLo E j) (enclosureHi E j)) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd ((hxj.1.trans hxi.2).trans (enclosureHi_lt_enclosureLo h hij hj)) (lt_irrefl _)
  · exact hij
  · exact absurd ((hxi.1.trans hxj.2).trans (enclosureHi_lt_enclosureLo h hij hi)) (lt_irrefl _)

end PDE.Fluid.Stokes.Ball
