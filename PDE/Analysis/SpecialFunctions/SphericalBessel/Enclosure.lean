/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Bounds
public import PDE.Analysis.SpecialFunctions.SphericalBessel.Rayleigh
public import PDE.Analysis.SpecialFunctions.SphericalBessel.Series
public import CAS.Continuum.Interval.Elementary.Trig

/-!
# Certified evaluation of spherical Bessel functions

`sphericalBesselInterval l x` is a rational interval that contains `j_l x` for every rational
`x`. Its switch rule follows the size of the argument relative to the order.

* For `|x| ≤ l + 10` or `|x| ≤ 128` it sums `K = l / 2 + 2 ⌈|x|⌉ + 30` terms of the series
  normalized by `(2l + 1)‼`, on the binary grid `2 ^ (-p)` with `p = 2 ⌈|x|⌉ + 192`, and
  encloses the remainder by the alternating bracket between the partial sums with `K` and
  `K + 1` terms. This covers the regime `|x| ≲ l` in which the Rayleigh form cancels: for
  `l = 100` at `x = 1` its two terms have size about `10 ^ 187` while `j_100 1` is about
  `10 ^ (-189)`. The normalization makes the first term one, so the grid error is relative to
  `|x| ^ l / (2l + 1)‼`, and the extra `2 ⌈|x|⌉` bits absorb the cancellation of the series,
  whose terms reach about `e ^ |x|`.
* Otherwise it evaluates the Rayleigh form `P_l (x⁻¹) sin x + Q_l (x⁻¹) cos x` with exact
  rational polynomial values and the 128-bit sine and cosine enclosures.

Every branch is sound for every rational argument, so the switch rule needs no further proof.
The grid state uses integer arithmetic only: each step multiplies two integer bounds by the
numerator of `-x ^ 2` and divides by an integer, so the work per term does not grow with the
number of terms. The exact rational evaluator `sphericalBesselSeriesInterval l K x`, the grid
evaluator `sphericalBesselGridInterval p l K x` and the Rayleigh evaluator
`sphericalBesselRayleighInterval l x` are available separately. Since `j_l` is `1`-Lipschitz,
`sphericalBesselIntervalOn l c r` encloses `j_l` on `[c - r, c + r]`.

Checked comparisons of these endpoints are closed finite propositions, proved with
`cega [fast]`; the kernel profile checks the same propositions by kernel computation.

## Main definitions

* `sphericalBesselSeriesState l x K`: the exact partial sum with `K` terms and the `K`-th term.
* `reducedSphericalBesselSeriesInterval l K x`, `sphericalBesselSeriesInterval l K x`.
* `sphericalBesselGridState p l a e K`, `sphericalBesselGridInterval p l K x`.
* `sphericalBesselRayleighInterval l x`.
* `sphericalBesselInterval l x`, `sphericalBesselIntervalOn l c r`.
* `sphericalBesselSignChange l a b`, `sphericalBesselDerivInterval l x`.

## Main results

* `sphericalBesselSeriesInterval_sound`, `sphericalBesselGridInterval_sound`,
  `sphericalBesselRayleighInterval_sound`, `sphericalBesselInterval_sound`,
  `sphericalBesselIntervalOn_sound`.
* `sphericalBesselJ_mem_Icc_of_le`, `sphericalBesselJ_pos_of_lo_pos`,
  `sphericalBesselJ_neg_of_hi_neg`: rational endpoint checks give bounds and signs.
* `exists_sphericalBesselJ_eq_zero_of_sign_change`,
  `exists_sphericalBesselJ_eq_zero_of_sphericalBesselSignChange`: a certified sign change gives
  a zero; the Boolean form suits batched checks.
* `sphericalBesselDerivInterval_sound`: an enclosure of `j_l'`.
-/

@[expose] public section

namespace PDE.Analysis.SpecialFunctions

open Nat
open CAS.Continuum

/-- Consecutive terms of the reduced series have ratio `-(x ^ 2) / (2 (k + 1) (2l + 2k + 3))`. -/
theorem sphericalBesselTerm_succ_eq_mul (l k : ℕ) (x : ℝ) :
    sphericalBesselTerm l (k + 1) x =
      sphericalBesselTerm l k x * (-(x ^ 2) / 2) / (((k : ℝ) + 1) * (2 * l + 2 * k + 3)) := by
  have hk : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  have hd : (0 : ℝ) < ((2 * l + 2 * k + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  unfold sphericalBesselTerm
  rw [doubleFactorial_succ_index, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The partial sum with `K` terms and the `K`-th term of the reduced series at a rational
point, computed by the term recurrence. -/
def sphericalBesselSeriesState (l : ℕ) (x : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 1 / ((2 * l + 1)‼ : ℕ))
  | K + 1 =>
    let p := sphericalBesselSeriesState l x K
    (p.1 + p.2, p.2 * (-(x ^ 2) / 2) / (((K : ℚ) + 1) * (2 * l + 2 * K + 3)))

/-- `sphericalBesselSeriesState` computes the partial sum and the next term. -/
theorem sphericalBesselSeriesState_cast (l : ℕ) (x : ℚ) (K : ℕ) :
    ((sphericalBesselSeriesState l x K).1 : ℝ) =
        ∑ k ∈ Finset.range K, sphericalBesselTerm l k x ∧
      ((sphericalBesselSeriesState l x K).2 : ℝ) = sphericalBesselTerm l K x := by
  induction K with
  | zero => simp [sphericalBesselSeriesState, sphericalBesselTerm]
  | succ K ih =>
    simp only [sphericalBesselSeriesState]
    constructor
    · push_cast
      rw [ih.1, ih.2, Finset.sum_range_succ]
    · push_cast
      rw [ih.2, sphericalBesselTerm_succ_eq_mul]

/-- Real membership in an interval with given ordered endpoints. -/
private theorem memReal_ofBounds_iff {a b : ℚ} (hab : a ≤ b) (y : ℝ) :
    (RationalInterval.ofBounds a b hab).MemReal y ↔ (a : ℝ) ≤ y ∧ y ≤ b :=
  Iff.rfl

/-- The interval between `s` and `s + t` for a partial sum `s` and the next term `t`. -/
def partialSumBracket (p : ℚ × ℚ) : RationalInterval :=
  RationalInterval.ofBounds (min p.1 (p.1 + p.2)) (max p.1 (p.1 + p.2)) min_le_max

/-- The enclosure of `g_l x` from `K` terms of the series: the bracket between the partial
sums with `K` and `K + 1` terms when the magnitudes decrease from index `K`, and the bound
`|g_l x| ≤ 1 / (2l + 1)‼` otherwise. -/
def reducedSphericalBesselSeriesInterval (l K : ℕ) (x : ℚ) : RationalInterval :=
  if x ^ 2 ≤ 2 * ((K : ℚ) + 1) * (2 * l + 2 * K + 3) then
    partialSumBracket (sphericalBesselSeriesState l x K)
  else
    RationalInterval.ofBounds (-(1 / ((2 * l + 1)‼ : ℕ))) (1 / ((2 * l + 1)‼ : ℕ))
      (neg_le_self (by have := Nat.doubleFactorial_pos (2 * l + 1); positivity))

/-- If the magnitudes decrease from index `K`, then `g_l x` lies between the partial sums with
`K` and `K + 1` terms. -/
theorem reducedSphericalBesselJ_mem_bracket {l K : ℕ} {x : ℝ}
    (h : x ^ 2 ≤ 2 * ((K : ℝ) + 1) * (2 * l + 2 * K + 3)) :
    min (∑ k ∈ Finset.range K, sphericalBesselTerm l k x)
        (∑ k ∈ Finset.range K, sphericalBesselTerm l k x + sphericalBesselTerm l K x) ≤
          reducedSphericalBesselJ l x ∧
      reducedSphericalBesselJ l x ≤ max (∑ k ∈ Finset.range K, sphericalBesselTerm l k x)
        (∑ k ∈ Finset.range K, sphericalBesselTerm l k x + sphericalBesselTerm l K x) := by
  obtain ⟨h₁, h₂⟩ := reducedSphericalBesselJ_sub_sum_mem h
  rw [sphericalBesselTerm_eq_neg_one_pow_mul]
  rcases Nat.even_or_odd K with he | ho
  · rw [he.neg_one_pow] at h₁ h₂ ⊢
    constructor
    · exact min_le_of_left_le (by linarith)
    · exact le_max_of_le_right (by linarith)
  · rw [ho.neg_one_pow] at h₁ h₂ ⊢
    constructor
    · exact min_le_of_right_le (by linarith)
    · exact le_max_of_le_left (by linarith)

/-- `reducedSphericalBesselSeriesInterval l K x` contains `g_l x`. -/
theorem reducedSphericalBesselSeriesInterval_sound (l K : ℕ) (x : ℚ) :
    (reducedSphericalBesselSeriesInterval l K x).MemReal (reducedSphericalBesselJ l x) := by
  unfold reducedSphericalBesselSeriesInterval
  obtain ⟨hS, hT⟩ := sphericalBesselSeriesState_cast l x K
  split_ifs with h
  · have hR : (x : ℝ) ^ 2 ≤ 2 * ((K : ℝ) + 1) * (2 * l + 2 * K + 3) := by exact_mod_cast h
    rw [partialSumBracket, memReal_ofBounds_iff, Rat.cast_min, Rat.cast_max, Rat.cast_add, hS,
      hT]
    exact reducedSphericalBesselJ_mem_bracket hR
  · have := abs_le.mp (abs_reducedSphericalBesselJ_le l x)
    rw [memReal_ofBounds_iff]
    push_cast
    exact this

/-- The enclosure of `j_l x` from `K` terms of the series. -/
def sphericalBesselSeriesInterval (l K : ℕ) (x : ℚ) : RationalInterval :=
  (RationalInterval.const (x ^ l)).mul (reducedSphericalBesselSeriesInterval l K x)

/-- `sphericalBesselSeriesInterval l K x` contains `j_l x`. -/
theorem sphericalBesselSeriesInterval_sound (l K : ℕ) (x : ℚ) :
    (sphericalBesselSeriesInterval l K x).MemReal (sphericalBesselJ l x) := by
  have h := RationalInterval.mul_sound (RationalInterval.memReal_const (x ^ l))
    (reducedSphericalBesselSeriesInterval_sound l K x)
  rw [Rat.cast_pow, ← sphericalBesselJ_eq_pow_mul] at h
  exact h

/-- Floor division by a positive integer bounds the real quotient from below. -/
private theorem intCast_ediv_le_div {m b : ℤ} (hb : 0 < b) : ((m / b : ℤ) : ℝ) ≤ (m : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb : (0 : ℝ) < b)]
  exact_mod_cast Int.ediv_mul_le m hb.ne'

/-- The negated floor quotient `-(m / b)` bounds `-m / b` from above. -/
private theorem neg_div_le_intCast_neg_ediv {m b : ℤ} (hb : 0 < b) :
    -(m : ℝ) / b ≤ ((-(m / b) : ℤ) : ℝ) := by
  have h := intCast_ediv_le_div (m := m) hb
  push_cast
  rw [neg_div]
  linarith

/-- The series on the grid `2 ^ (-p)`, for `x ^ 2 = a / e`: integer bounds
`(S_lo, S_hi, T_lo, T_hi)` on `2 ^ p (2l + 1)‼ S_K` and `2 ^ p (2l + 1)‼ t_{l,K}`, where `S_K` is
the partial sum with `K` terms. Each step multiplies the term bounds by
`-a / (2 e (K + 1) (2l + 2K + 3))` and rounds them outward to integers, so no number grows
beyond the grid and no greatest common divisor is computed. -/
def sphericalBesselGridState (p l : ℕ) (a e : ℤ) : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (0, 0, 2 ^ p, 2 ^ p)
  | K + 1 =>
    let s := sphericalBesselGridState p l a e K
    let b : ℤ := 2 * e * (K + 1) * (2 * l + 2 * K + 3)
    (s.1 + s.2.2.1, s.2.1 + s.2.2.2, (-(s.2.2.2 * a)) / b, -((s.2.2.1 * a) / b))

/-- The grid state bounds the scaled partial sum and the scaled next term. -/
theorem sphericalBesselGridState_sound (p l : ℕ) {x : ℝ} {a e : ℤ} (ha : 0 ≤ a) (he : 0 < e)
    (hx : x ^ 2 = a / e) (K : ℕ) :
    ((sphericalBesselGridState p l a e K).1 : ℝ) ≤
        2 ^ p * (((2 * l + 1)‼ : ℕ) : ℝ) * ∑ k ∈ Finset.range K, sphericalBesselTerm l k x ∧
      2 ^ p * (((2 * l + 1)‼ : ℕ) : ℝ) * ∑ k ∈ Finset.range K, sphericalBesselTerm l k x ≤
        (sphericalBesselGridState p l a e K).2.1 ∧
      ((sphericalBesselGridState p l a e K).2.2.1 : ℝ) ≤
        2 ^ p * (((2 * l + 1)‼ : ℕ) : ℝ) * sphericalBesselTerm l K x ∧
      2 ^ p * (((2 * l + 1)‼ : ℕ) : ℝ) * sphericalBesselTerm l K x ≤
        (sphericalBesselGridState p l a e K).2.2.2 := by
  induction K with
  | zero =>
    have hd : (((2 * l + 1)‼ : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.doubleFactorial_pos _).ne'
    have h₀ : 2 ^ p * (((2 * l + 1)‼ : ℕ) : ℝ) * sphericalBesselTerm l 0 x = 2 ^ p := by
      simp [sphericalBesselTerm, hd]
    simp only [sphericalBesselGridState, Finset.range_zero, Finset.sum_empty, mul_zero,
      Int.cast_zero, le_refl, h₀, Int.cast_pow, Int.cast_ofNat, and_self]
  | succ K ih =>
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih
    set τ := 2 ^ p * (((2 * l + 1)‼ : ℕ) : ℝ) * sphericalBesselTerm l K x
    set b : ℤ := 2 * e * (K + 1) * (2 * l + 2 * K + 3) with hbdef
    have hb : 0 < b := by positivity
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    have hτ : 2 ^ p * (((2 * l + 1)‼ : ℕ) : ℝ) * sphericalBesselTerm l (K + 1) x =
        -(τ * a) / b := by
      have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
      rw [sphericalBesselTerm_succ_eq_mul, hx, hbdef]
      push_cast
      field_simp
      ring
    have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
    simp only [sphericalBesselGridState]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Finset.sum_range_succ, mul_add]
      push_cast
      linarith
    · rw [Finset.sum_range_succ, mul_add]
      push_cast
      linarith
    · rw [hτ]
      refine (intCast_ediv_le_div hb).trans ?_
      push_cast
      gcongr
    · rw [hτ]
      refine le_trans ?_ (neg_div_le_intCast_neg_ediv hb)
      have hm : (((sphericalBesselGridState p l a e K).2.2.1 * a : ℤ) : ℝ) ≤ τ * a := by
        push_cast
        exact mul_le_mul_of_nonneg_right h₃ haR
      exact div_le_div_of_nonneg_right (neg_le_neg hm) hbR.le

/-- The `K`-term series enclosure of `j_l x` computed on the grid `2 ^ (-p)`. -/
def sphericalBesselGridInterval (p l K : ℕ) (x : ℚ) : RationalInterval :=
  let s := sphericalBesselGridState p l (x.num ^ 2) ((x.den : ℤ) ^ 2) K
  (RationalInterval.const (x ^ l / ((2 * l + 1)‼ : ℕ) / 2 ^ p)).mul
    (if x ^ 2 ≤ 2 * ((K : ℚ) + 1) * (2 * l + 2 * K + 3) then
      (RationalInterval.const (min s.1 (s.1 + s.2.2.1))).hull
        (RationalInterval.const (max s.2.1 (s.2.1 + s.2.2.2)))
    else (RationalInterval.const (-2 ^ p)).hull (RationalInterval.const (2 ^ p)))

/-- A real number between `q₁` and `q₂` lies in the hull of the two singletons. -/
private theorem memReal_hull_const {q₁ q₂ : ℚ} {y : ℝ} (h₁ : (q₁ : ℝ) ≤ y) (h₂ : y ≤ q₂) :
    ((RationalInterval.const q₁).hull (RationalInterval.const q₂)).MemReal y := by
  constructor
  · rw [RationalInterval.hull_lo, RationalInterval.const_lo, RationalInterval.const_lo,
      Rat.cast_min]
    exact min_le_of_left_le h₁
  · rw [RationalInterval.hull_hi, RationalInterval.const_hi, RationalInterval.const_hi,
      Rat.cast_max]
    exact le_max_of_le_right h₂

/-- `sphericalBesselGridInterval p l K x` contains `j_l x`. -/
theorem sphericalBesselGridInterval_sound (p l K : ℕ) (x : ℚ) :
    (sphericalBesselGridInterval p l K x).MemReal (sphericalBesselJ l x) := by
  have hdpos : (0 : ℝ) < ((2 * l + 1)‼ : ℕ) := by exact_mod_cast Nat.doubleFactorial_pos _
  set D : ℝ := 2 ^ p * (((2 * l + 1)‼ : ℕ) : ℝ) with hD
  have hDpos : 0 < D := by positivity
  have hj : sphericalBesselJ l x = ((x ^ l / ((2 * l + 1)‼ : ℕ) / 2 ^ p : ℚ) : ℝ) *
      (D * reducedSphericalBesselJ l x) := by
    rw [sphericalBesselJ_eq_pow_mul, hD]
    push_cast
    field_simp
  unfold sphericalBesselGridInterval
  rw [hj]
  refine RationalInterval.mul_sound (RationalInterval.memReal_const _) ?_
  split_ifs with h
  · have hR : (x : ℝ) ^ 2 ≤ 2 * ((K : ℝ) + 1) * (2 * l + 2 * K + 3) := by exact_mod_cast h
    have hx : (x : ℝ) ^ 2 = ((x.num ^ 2 : ℤ) : ℝ) / (((x.den : ℤ) ^ 2 : ℤ) : ℝ) := by
      rw [Rat.cast_def x]
      push_cast
      ring
    obtain ⟨h₁, h₂, h₃, h₄⟩ := sphericalBesselGridState_sound p l (sq_nonneg x.num)
      (by have := x.den_pos; positivity) hx K
    obtain ⟨hlo, hhi⟩ := reducedSphericalBesselJ_mem_bracket hR
    set S := ∑ k ∈ Finset.range K, sphericalBesselTerm l k x
    set T := sphericalBesselTerm l K x
    have hlo' : min (D * S) (D * S + D * T) ≤ D * reducedSphericalBesselJ l x := by
      rw [← mul_add, ← mul_min_of_nonneg _ _ hDpos.le]
      exact mul_le_mul_of_nonneg_left hlo hDpos.le
    have hhi' : D * reducedSphericalBesselJ l x ≤ max (D * S) (D * S + D * T) := by
      rw [← mul_add, ← mul_max_of_nonneg _ _ hDpos.le]
      exact mul_le_mul_of_nonneg_left hhi hDpos.le
    rw [hD] at hlo' hhi'
    apply memReal_hull_const
    · push_cast
      refine le_trans ?_ hlo'
      exact min_le_min h₁ (by linarith)
    · push_cast
      refine hhi'.trans ?_
      exact max_le_max h₂ (by linarith)
  · have habs := abs_reducedSphericalBesselJ_le l x
    have hle : |D * reducedSphericalBesselJ l x| ≤ 2 ^ p := by
      rw [abs_mul, abs_of_pos hDpos, hD]
      calc 2 ^ p * (((2 * l + 1)‼ : ℕ) : ℝ) * |reducedSphericalBesselJ l x|
          ≤ 2 ^ p * (((2 * l + 1)‼ : ℕ) : ℝ) * (1 / (((2 * l + 1)‼ : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = 2 ^ p := by field_simp
    obtain ⟨hl, hu⟩ := abs_le.mp hle
    apply memReal_hull_const
    · push_cast
      exact hl
    · push_cast
      exact hu

/-- The Rayleigh polynomial values at a rational point cast to their real values. -/
theorem rayleighPair_cast (u : ℚ) (l : ℕ) :
    (((rayleighPair u l).1.1 : ℚ) : ℝ) = Polynomial.aeval (u : ℝ) (rayleighSin l) ∧
      (((rayleighPair u l).1.2 : ℚ) : ℝ) = Polynomial.aeval (u : ℝ) (rayleighCos l) := by
  have h := map_rayleighPair (Rat.castHom ℝ) u l
  rw [rayleighPair_eq] at h
  simp only [Rat.coe_castHom, Prod.mk.injEq] at h
  exact ⟨h.1.1.symm, h.1.2.symm⟩

/-- The Rayleigh form enclosure `P_l (x⁻¹) [sin x] + Q_l (x⁻¹) [cos x]`. -/
def sphericalBesselRayleighInterval (l : ℕ) (x : ℚ) : RationalInterval :=
  let p := (rayleighPair x⁻¹ l).1
  ((RationalInterval.const p.1).mul (RationalInterval.sinPoint x)).add
    ((RationalInterval.const p.2).mul (RationalInterval.cosPoint x))

/-- `sphericalBesselRayleighInterval l x` contains `j_l x` for `x ≠ 0`. -/
theorem sphericalBesselRayleighInterval_sound (l : ℕ) {x : ℚ} (hx : x ≠ 0) :
    (sphericalBesselRayleighInterval l x).MemReal (sphericalBesselJ l x) := by
  have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
  obtain ⟨hP, hQ⟩ := rayleighPair_cast x⁻¹ l
  rw [Rat.cast_inv] at hP hQ
  rw [sphericalBesselJ_eq_rayleigh l hx', ← hP, ← hQ]
  exact RationalInterval.add_sound
    (RationalInterval.mul_sound (RationalInterval.memReal_const _)
      (RationalInterval.sinPoint_sound x))
    (RationalInterval.mul_sound (RationalInterval.memReal_const _)
      (RationalInterval.cosPoint_sound x))

/-- The number of series terms used by `sphericalBesselInterval`. -/
def sphericalBesselSeriesTerms (l : ℕ) (x : ℚ) : ℕ :=
  l / 2 + 2 * ⌈|x|⌉.toNat + 30

/-- The grid exponent used by `sphericalBesselInterval`: `192` bits beyond the size `e ^ |x|`
of the largest term of the normalized series. -/
def sphericalBesselGridBits (x : ℚ) : ℕ :=
  2 * ⌈|x|⌉.toNat + 192

/-- A rational interval containing `j_l x`: the series on a binary grid for `|x| ≤ l + 10` or
`|x| ≤ 128`, and the Rayleigh form otherwise. -/
def sphericalBesselInterval (l : ℕ) (x : ℚ) : RationalInterval :=
  if |x| ≤ l + 10 ∨ |x| ≤ 128 then
    sphericalBesselGridInterval (sphericalBesselGridBits x) l (sphericalBesselSeriesTerms l x) x
  else sphericalBesselRayleighInterval l x

/-- `sphericalBesselInterval l x` contains `j_l x`. -/
theorem sphericalBesselInterval_sound (l : ℕ) (x : ℚ) :
    (sphericalBesselInterval l x).MemReal (sphericalBesselJ l x) := by
  unfold sphericalBesselInterval
  split_ifs with h
  · exact sphericalBesselGridInterval_sound _ _ _ _
  · refine sphericalBesselRayleighInterval_sound l fun hx ↦ h (Or.inr ?_)
    rw [hx, abs_zero]
    positivity

/-- The enclosure of `j_l` on `[c - r, c + r]`, from the value at `c` and the Lipschitz bound. -/
def sphericalBesselIntervalOn (l : ℕ) (c r : ℚ) : RationalInterval :=
  (sphericalBesselInterval l c).add
    (RationalInterval.ofBounds (-|r|) |r| (neg_le_self (abs_nonneg r)))

/-- `sphericalBesselIntervalOn l c r` contains `j_l y` for every `y` with `|y - c| ≤ r`. -/
theorem sphericalBesselIntervalOn_sound (l : ℕ) (c r : ℚ) {y : ℝ} (hy : |y - c| ≤ r) :
    (sphericalBesselIntervalOn l c r).MemReal (sphericalBesselJ l y) := by
  have hlip := abs_sphericalBesselJ_sub_le l y c
  have hr : |y - c| ≤ |(r : ℝ)| := hy.trans (le_abs_self _)
  have hmem : (RationalInterval.ofBounds (-|r|) |r| (neg_le_self (abs_nonneg r))).MemReal
      (sphericalBesselJ l y - sphericalBesselJ l c) := by
    rw [memReal_ofBounds_iff]
    push_cast
    exact abs_le.mp (hlip.trans hr)
  have h := RationalInterval.add_sound (sphericalBesselInterval_sound l c) hmem
  rwa [add_sub_cancel] at h

/-- Rational bounds on the endpoints of `sphericalBesselInterval l x` bound `j_l x`. -/
theorem sphericalBesselJ_mem_Icc_of_le {l : ℕ} {x a b : ℚ}
    (ha : a ≤ (sphericalBesselInterval l x).lo) (hb : (sphericalBesselInterval l x).hi ≤ b) :
    sphericalBesselJ l x ∈ Set.Icc (a : ℝ) b := by
  obtain ⟨h₁, h₂⟩ := sphericalBesselInterval_sound l x
  exact ⟨(by exact_mod_cast ha : (a : ℝ) ≤ _).trans h₁, h₂.trans (by exact_mod_cast hb)⟩

/-- A positive lower endpoint certifies `0 < j_l x`. -/
theorem sphericalBesselJ_pos_of_lo_pos {l : ℕ} {x : ℚ}
    (h : 0 < (sphericalBesselInterval l x).lo) : 0 < sphericalBesselJ l x :=
  (by exact_mod_cast h : (0 : ℝ) < _).trans_le (sphericalBesselInterval_sound l x).1

/-- A negative upper endpoint certifies `j_l x < 0`. -/
theorem sphericalBesselJ_neg_of_hi_neg {l : ℕ} {x : ℚ}
    (h : (sphericalBesselInterval l x).hi < 0) : sphericalBesselJ l x < 0 :=
  (sphericalBesselInterval_sound l x).2.trans_lt (by exact_mod_cast h)

/-- A certified sign change of `j_l` between rational points `a ≤ b` gives a zero of `j_l` in
`(a, b)`. -/
theorem exists_sphericalBesselJ_eq_zero_of_sign_change {l : ℕ} {a b : ℚ} (hab : a ≤ b)
    (h : (0 < (sphericalBesselInterval l a).lo ∧ (sphericalBesselInterval l b).hi < 0) ∨
      ((sphericalBesselInterval l a).hi < 0 ∧ 0 < (sphericalBesselInterval l b).lo)) :
    ∃ x ∈ Set.Ioo (a : ℝ) b, sphericalBesselJ l x = 0 := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hcont := (continuous_sphericalBesselJ l).continuousOn (s := Set.Icc (a : ℝ) b)
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact intermediate_value_Ioo' hab' hcont
      ⟨sphericalBesselJ_neg_of_hi_neg hb, sphericalBesselJ_pos_of_lo_pos ha⟩
  · exact intermediate_value_Ioo hab' hcont
      ⟨sphericalBesselJ_neg_of_hi_neg ha, sphericalBesselJ_pos_of_lo_pos hb⟩

/-- The Boolean check that `j_l` changes sign between the rational points `a ≤ b`, for batched
certificates. -/
def sphericalBesselSignChange (l : ℕ) (a b : ℚ) : Bool :=
  decide (a ≤ b) &&
    ((decide (0 < (sphericalBesselInterval l a).lo) &&
        decide ((sphericalBesselInterval l b).hi < 0)) ||
      (decide ((sphericalBesselInterval l a).hi < 0) &&
        decide (0 < (sphericalBesselInterval l b).lo)))

/-- A successful sign-change check gives a zero of `j_l` in `(a, b)`. -/
theorem exists_sphericalBesselJ_eq_zero_of_sphericalBesselSignChange {l : ℕ} {a b : ℚ}
    (h : sphericalBesselSignChange l a b = true) :
    ∃ x ∈ Set.Ioo (a : ℝ) b, sphericalBesselJ l x = 0 := by
  simp only [sphericalBesselSignChange, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq] at h
  exact exists_sphericalBesselJ_eq_zero_of_sign_change h.1 h.2

/-- An enclosure of the derivative `j_l' x`: the exact value `δ_{l,1} / 3` at the origin and
`(l / x) j_l x - j_{l+1} x` otherwise. -/
def sphericalBesselDerivInterval (l : ℕ) (x : ℚ) : RationalInterval :=
  if x = 0 then RationalInterval.const (if l = 1 then 1 / 3 else 0)
  else ((RationalInterval.const (l / x)).mul (sphericalBesselInterval l x)).sub
    (sphericalBesselInterval (l + 1) x)

/-- The derivative of `j_l` at the origin is `1 / 3` for `l = 1` and zero otherwise. -/
theorem deriv_sphericalBesselJ_zero_point (l : ℕ) :
    deriv (sphericalBesselJ l) 0 = if l = 1 then 1 / 3 else 0 := by
  rw [(hasDerivAt_sphericalBesselJ l 0).deriv]
  rcases l with _ | _ | l
  · simp
  · simp [reducedSphericalBesselJ_zero]
  · simp

/-- `sphericalBesselDerivInterval l x` contains `j_l' x`. -/
theorem sphericalBesselDerivInterval_sound (l : ℕ) (x : ℚ) :
    (sphericalBesselDerivInterval l x).MemReal (deriv (sphericalBesselJ l) x) := by
  unfold sphericalBesselDerivInterval
  by_cases hx : x = 0
  · rw [ite_eq_left hx, hx, Rat.cast_zero, deriv_sphericalBesselJ_zero_point]
    by_cases hl : l = 1
    · rw [ite_eq_left hl, ite_eq_left hl]
      simpa using RationalInterval.memReal_const (1 / 3)
    · rw [ite_eq_right hl, ite_eq_right hl]
      simpa using RationalInterval.memReal_const 0
  · rw [ite_eq_right hx]
    have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    have heq : deriv (sphericalBesselJ l) x =
        ((l / x : ℚ) : ℝ) * sphericalBesselJ l x - sphericalBesselJ (l + 1) x := by
      have h := mul_deriv_sphericalBesselJ l x
      push_cast
      field_simp
      linarith
    rw [heq]
    exact RationalInterval.sub_sound
      (RationalInterval.mul_sound (RationalInterval.memReal_const _)
        (sphericalBesselInterval_sound l x)) (sphericalBesselInterval_sound (l + 1) x)

end PDE.Analysis.SpecialFunctions
