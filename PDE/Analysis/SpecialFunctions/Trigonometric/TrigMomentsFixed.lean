/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigTerms

/-!
# Fixed-point moments of products of two trigonometric terms

The moment `∫₀^π cos (F θ) sin θ dθ` is `cosMoment F = (1 + (-1)^F) / (1 - F²)`: `2 / (1 - F²)`
for even `F` and `0` for odd `F`. The moment of `sin (F θ)` is `π` times `sinMomentPi F`, which
is `± 1/2` at `F = ± 1` and `0` otherwise. The moments of the product of `a trig (f θ)` and
`trig (B θ)` are `a` times combinations of these values at `f ± B` (`pairRatMoment`,
`pairPiMoment`, `ratMoment_sum_mul`, `piMoment_sum_mul`).

On the grid `2 ^ (-w)` the rational moment is rounded to the nearest integer with one
natural-number division (`cosMomentFixed`, within `1/2`: `abs_cosMomentFixed_sub_le`), so the
rational part of a pair moment on the grid `2 ^ (-(w + 1))` is within `1` (`pairRatFixed`), and
four times its `π` part is an integer (`pairPiInt`).
-/

@[expose] public section

namespace PDE.Analysis

open Real

/-- The moment `∫₀^π cos (F θ) sin θ dθ = (1 + (-1)^F) / (1 - F²)`. -/
def cosMoment (F : ℤ) : ℚ := (1 + (-1) ^ F.natAbs) / (1 - (F : ℚ) ^ 2)

/-- The `π` coefficient of `∫₀^π sin (F θ) sin θ dθ`. -/
def sinMomentPi (F : ℤ) : ℚ := (if F = 1 then 1 / 2 else 0) - (if F = -1 then 1 / 2 else 0)

/-- The rational part of the moment of `trig (f θ) trig (B θ)` (`s`, `s'` select sines). -/
def pairRatMoment (s s' : Bool) (f B : ℤ) : ℚ :=
  match s, s' with
  | false, false => (cosMoment (f - B) + cosMoment (f + B)) / 2
  | true, true => (cosMoment (f - B) - cosMoment (f + B)) / 2
  | _, _ => 0

/-- The `π` part of the moment of `trig (f θ) trig (B θ)`. -/
def pairPiMoment (s s' : Bool) (f B : ℤ) : ℚ :=
  match s, s' with
  | false, true => (sinMomentPi (f + B) - sinMomentPi (f - B)) / 2
  | true, false => (sinMomentPi (f + B) + sinMomentPi (f - B)) / 2
  | _, _ => 0

theorem ratMoment_sum_mul (s t : TrigTerm) :
    ((s.mul t).map TrigTerm.ratMoment).sum =
      s.coeff * t.coeff * pairRatMoment s.isSin t.isSin s.freq t.freq := by
  rcases s with ⟨a, f, bs⟩
  rcases t with ⟨b, g, bt⟩
  cases bs <;> cases bt <;>
    simp only [TrigTerm.mul, TrigTerm.ratMoment, pairRatMoment, cosMoment, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte] <;> ring

theorem piMoment_sum_mul (s t : TrigTerm) :
    ((s.mul t).map TrigTerm.piMoment).sum =
      s.coeff * t.coeff * pairPiMoment s.isSin t.isSin s.freq t.freq := by
  rcases s with ⟨a, f, bs⟩
  rcases t with ⟨b, g, bt⟩
  cases bs <;> cases bt <;>
    simp only [TrigTerm.mul, TrigTerm.piMoment, pairPiMoment, sinMomentPi, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- The rational moments of a list times one term, term by term. -/
theorem ratMoment_sum_trigTermsMul_singleton (l : List TrigTerm) (t : TrigTerm) :
    ((trigTermsMul l [t]).map TrigTerm.ratMoment).sum =
      (l.map fun s ↦ s.coeff * t.coeff * pairRatMoment s.isSin t.isSin s.freq t.freq).sum := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    simp only [trigTermsMul, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append, List.sum_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ratMoment_sum_mul, ih]

/-- The `π` moments of a list times one term, term by term. -/
theorem piMoment_sum_trigTermsMul_singleton (l : List TrigTerm) (t : TrigTerm) :
    ((trigTermsMul l [t]).map TrigTerm.piMoment).sum =
      (l.map fun s ↦ s.coeff * t.coeff * pairPiMoment s.isSin t.isSin s.freq t.freq).sum := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    simp only [trigTermsMul, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append, List.sum_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [piMoment_sum_mul, ih]

/-- `2 ^ w cosMoment F` rounded to the nearest integer: `2 ^ (w + 1)` at `F = 0`, `0` at odd
`F`, and `-⌊(2 ^ (w + 1) + ⌊d / 2⌋) / d⌋` with `d = F² - 1` at even `F ≠ 0`. -/
def cosMomentFixed (w : ℕ) (F : ℤ) : ℤ :=
  if F = 0 then 2 ^ (w + 1)
  else if F.natAbs % 2 = 1 then 0
  else -(((2 ^ (w + 1) + (F.natAbs ^ 2 - 1) / 2) / (F.natAbs ^ 2 - 1) : ℕ) : ℤ)

/-- Rounding `N / d` by `⌊(N + ⌊d / 2⌋) / d⌋` is within `1/2`. -/
theorem abs_nat_div_round_sub_le (N d : ℕ) (hd : 0 < d) :
    |(((N + d / 2) / d : ℕ) : ℚ) - N / d| ≤ 1 / 2 := by
  have hdiv := Nat.div_add_mod (N + d / 2) d
  have hmod := Nat.mod_lt (N + d / 2) hd
  have h2 := Nat.div_add_mod d 2
  have h2' := Nat.mod_lt d (show 0 < 2 by norm_num)
  set q := (N + d / 2) / d
  set m := d * q with hm
  have key : (2 * (m : ℤ) - 2 * N ≤ d) ∧ (2 * (N : ℤ) - 2 * m ≤ d) := by omega
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hmq : (m : ℚ) = d * q := by exact_mod_cast hm
  have k1 : 2 * (m : ℚ) - 2 * N ≤ d := by exact_mod_cast key.1
  have k2 : 2 * (N : ℚ) - 2 * m ≤ d := by exact_mod_cast key.2
  have e : (q : ℚ) - N / d = ((m : ℚ) - N) / d := by
    rw [hmq]
    field_simp
  rw [e, abs_div, abs_of_pos hdq, div_le_iff₀ hdq, abs_le]
  constructor <;> linarith

theorem abs_cosMomentFixed_sub_le (w : ℕ) (F : ℤ) :
    |(cosMomentFixed w F : ℚ) - 2 ^ w * cosMoment F| ≤ 1 / 2 := by
  unfold cosMomentFixed cosMoment
  by_cases h0 : F = 0
  · subst h0
    norm_num [pow_succ]
  by_cases hodd : F.natAbs % 2 = 1
  · have hneg : ((-1 : ℚ) ^ F.natAbs) = -1 := by
      rw [← Nat.odd_iff] at hodd
      exact hodd.neg_one_pow
    simp only [h0, hodd, ↓reduceIte, hneg]
    norm_num
  have heven : ((-1 : ℚ) ^ F.natAbs) = 1 := by
    have : Even F.natAbs := Nat.even_iff.mpr (by omega)
    exact this.neg_one_pow
  have hn : 2 ≤ F.natAbs := by
    have := Int.natAbs_pos.mpr h0
    omega
  set n := F.natAbs with hndef
  have hF2 : (F : ℚ) ^ 2 = (n : ℚ) ^ 2 := by
    rw [hndef, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have hd : 0 < n ^ 2 - 1 := by
    have : 4 ≤ n ^ 2 := by nlinarith
    omega
  have hdcast : (((n ^ 2 - 1 : ℕ)) : ℚ) = (n : ℚ) ^ 2 - 1 := by
    rw [Nat.cast_sub (by nlinarith), Nat.cast_pow, Nat.cast_one]
  have hround := abs_nat_div_round_sub_le (2 ^ (w + 1)) (n ^ 2 - 1) hd
  simp only [h0, hodd, ↓reduceIte, heven, hF2]
  push_cast
  rw [hdcast] at hround
  have hpos : (0 : ℚ) < (n : ℚ) ^ 2 - 1 := by
    have : (4 : ℚ) ≤ (n : ℚ) ^ 2 := by
      have : (2 : ℚ) ≤ n := by exact_mod_cast hn
      nlinarith
    linarith
  have e : (2 : ℚ) ^ w * ((1 + 1) / (1 - (n : ℚ) ^ 2)) =
      -((2 : ℚ) ^ (w + 1) / ((n : ℚ) ^ 2 - 1)) := by
    rw [pow_succ]
    field_simp
    rw [show (1 : ℚ) - (n : ℚ) ^ 2 = -((n : ℚ) ^ 2 - 1) by ring]
    field_simp
    ring
  rw [e, show ∀ x y : ℚ, -x - -y = -(x - y) from fun x y ↦ by ring, abs_neg]
  exact_mod_cast hround

/-- The rational part of a pair moment on the grid `2 ^ (-(w + 1))`. -/
def pairRatFixed (w : ℕ) (s s' : Bool) (f B : ℤ) : ℤ :=
  match s, s' with
  | false, false => cosMomentFixed w (f - B) + cosMomentFixed w (f + B)
  | true, true => cosMomentFixed w (f - B) - cosMomentFixed w (f + B)
  | _, _ => 0

theorem abs_pairRatFixed_sub_le (w : ℕ) (s s' : Bool) (f B : ℤ) :
    |(pairRatFixed w s s' f B : ℚ) - 2 ^ (w + 1) * pairRatMoment s s' f B| ≤ 1 := by
  have h1 := abs_cosMomentFixed_sub_le w (f - B)
  have h2 := abs_cosMomentFixed_sub_le w (f + B)
  rw [abs_le] at h1 h2 ⊢
  cases s <;> cases s' <;> simp only [pairRatFixed, pairRatMoment] <;> push_cast <;>
    ring_nf at h1 h2 ⊢ <;> constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Twice `sinMomentPi`: `± 1` at `F = ± 1`, `0` otherwise. -/
def sinPiInt (F : ℤ) : ℤ := (if F = 1 then 1 else 0) - (if F = -1 then 1 else 0)

/-- Four times the `π` part of a pair moment. -/
def pairPiInt (s s' : Bool) (f B : ℤ) : ℤ :=
  match s, s' with
  | false, true => sinPiInt (f + B) - sinPiInt (f - B)
  | true, false => sinPiInt (f + B) + sinPiInt (f - B)
  | _, _ => 0

theorem pairPiInt_eq (s s' : Bool) (f B : ℤ) :
    (pairPiInt s s' f B : ℚ) = 4 * pairPiMoment s s' f B := by
  have hs (F : ℤ) : (sinPiInt F : ℚ) = 2 * sinMomentPi F := by
    unfold sinPiInt sinMomentPi
    split_ifs <;> push_cast <;> norm_num
  cases s <;> cases s' <;> simp only [pairPiInt, pairPiMoment] <;> push_cast <;>
    first | (simp only [hs]; ring) | ring

end PDE.Analysis
