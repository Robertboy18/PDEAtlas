/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.SphericalBessel.Series

/-!
# The series of `g_l` on a binary grid in natural-number arithmetic

For `x ^ 2 / 2 = a / 2 ^ s` the normalized series `(2m + 1)‼ g_m x = ∑ (-1)^k τ_k` has the
terms `τ_0 = 1` and `τ_{k+1} = τ_k a / (2 ^ s (k + 1) (2m + 2k + 3))`. The state
`sphericalBesselNatGridState p m a s K` keeps lower and upper bounds `L_K ≤ 2 ^ p τ_K ≤ U_K`,
rounded down and up by shifts and natural divisions, and bounds on the sums of the terms of the
same parity as `K` and of the other parity (`sphericalBesselParityParts`).

`sphericalBesselGridState` of `Enclosure.lean` computes the same series on the same kind of grid,
but with integer arithmetic and one signed partial sum. Kernel evaluation unfolds the integer
operations and their instances at every step, so certificates that evaluate thousands of points
in the kernel profile use this natural-number form: each step is a few `Nat.mul`, `Nat.div` and
shifts on literals, which the kernel performs with its arbitrary-precision extensions, and no
integer, rational or `gcd` operation occurs in the loop. Measured on the ball root certificates,
one point costs about 40 ms of kernel time for both orders `l` and `l + 1`.

`sphericalBesselNatGridBounds p m a s K` reads off integer bounds on
`2 ^ p (2m + 1)‼ (-1)^K g_m x`, and `sphericalBesselNatGridBounds_sound` proves them from the
alternating tail bound of the series, which needs `x ^ 2 ≤ 2 (K + 1) (2m + 2K + 3)`.
-/

@[expose] public section

namespace PDE.Analysis.SpecialFunctions

open Nat

/-- The grid state after `K` terms: `(L, U, xl, xh, yl, yh)` with `L ≤ 2 ^ p τ_K ≤ U`, and
`[xl, xh]`, `[yl, yh]` containing `2 ^ p` times the sums of the terms `τ_k`, `k < K`, of the
parity of `K` and of the other parity. -/
def sphericalBesselNatGridState (p m a s : ℕ) : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ × ℕ
  | 0 => (Nat.shiftLeft 1 p, Nat.shiftLeft 1 p, 0, 0, 0, 0)
  | K + 1 =>
    match sphericalBesselNatGridState p m a s K with
    | (L, U, xl, xh, yl, yh) =>
      let d := Nat.mul (Nat.succ K) (Nat.add (Nat.add (Nat.mul 2 m) (Nat.mul 2 K)) 3)
      (Nat.div (Nat.shiftRight (Nat.mul L a) s) d,
        Nat.div (Nat.add (Nat.shiftRight (Nat.add (Nat.mul U a) (Nat.sub (Nat.shiftLeft 1 s) 1))
          s) (Nat.sub d 1)) d, yl, yh, Nat.add xl L, Nat.add xh U)

/-- Integer bounds on `2 ^ p (2m + 1)‼ (-1)^K g_m x` after `K` terms. -/
def sphericalBesselNatGridBounds (p m a s K : ℕ) : ℤ × ℤ :=
  match sphericalBesselNatGridState p m a s K with
  | (_, U, xl, xh, yl, yh) => ((xl : ℤ) - yh, (xh : ℤ) - yl + U)

/-- The pair of real sums of the terms `f k`, `k < K`, of the parity of `K` and of the other
parity. -/
def sphericalBesselParityParts (f : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | K + 1 => ((sphericalBesselParityParts f K).2, (sphericalBesselParityParts f K).1 + f K)

/-- The difference of the two parts is `(-1)^K ∑_{k < K} (-1)^k f k`. -/
theorem sphericalBesselParityParts_sub (f : ℕ → ℝ) (K : ℕ) :
    (sphericalBesselParityParts f K).1 - (sphericalBesselParityParts f K).2 =
      (-1) ^ K * ∑ k ∈ Finset.range K, (-1) ^ k * f k := by
  induction K with
  | zero => simp [sphericalBesselParityParts]
  | succ K ih =>
    have h1 : (-1 : ℝ) ^ K * (-1) ^ K = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨K, rfl⟩
    have h2 : (-1 : ℝ) ^ K * (-1) * ((-1) ^ K * f K) = -(f K) := by
      rw [show (-1 : ℝ) ^ K * (-1) * ((-1) ^ K * f K) = -(((-1) ^ K * (-1) ^ K) * f K) by ring,
        h1, one_mul]
    rw [Finset.sum_range_succ, pow_succ, mul_add, h2]
    simp only [sphericalBesselParityParts]
    linarith

/-- Shifting `1` left by `b` gives `2 ^ b`. -/
private theorem natShiftLeft_one (b : ℕ) : Nat.shiftLeft 1 b = 2 ^ b := by
  rw [show Nat.shiftLeft 1 b = 1 <<< b from rfl, Nat.one_shiftLeft]

/-- Floor division by a shift and a positive natural number bounds the real quotient from
below. -/
private theorem cast_div_shiftRight_le (y s d : ℕ) :
    ((Nat.div (Nat.shiftRight y s) d : ℕ) : ℝ) ≤ (y : ℝ) / (2 ^ s * d) := by
  rw [show Nat.div (Nat.shiftRight y s) d = Nat.shiftRight y s / d from rfl, Nat.shiftRight_eq]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have h₁ : ((y >>> s : ℕ) : ℝ) ≤ (y : ℝ) / 2 ^ s := by
    rw [Nat.shiftRight_eq_div_pow]
    exact_mod_cast Nat.cast_div_le
  calc (((y >>> s) / d : ℕ) : ℝ) ≤ ((y >>> s : ℕ) : ℝ) / d := Nat.cast_div_le
    _ ≤ (y : ℝ) / 2 ^ s / d := by gcongr
    _ = (y : ℝ) / (2 ^ s * d) := by rw [div_div]

/-- Rounding up by a shift and a positive natural number bounds the real quotient from
above. -/
private theorem le_cast_ceil_div_shiftRight (y s d : ℕ) (hd : 0 < d) :
    (y : ℝ) / (2 ^ s * d) ≤ ((Nat.div (Nat.add (Nat.shiftRight (Nat.add y
      (Nat.sub (Nat.shiftLeft 1 s) 1)) s) (Nat.sub d 1)) d : ℕ) : ℝ) := by
  have hceil : ∀ z c : ℕ, 0 < c → (z : ℝ) / c ≤ (((z + (c - 1)) / c : ℕ) : ℝ) := by
    intro z c hc
    have hlt := Nat.lt_div_mul_add (a := z + (c - 1)) hc
    have hle : z ≤ (z + (c - 1)) / c * c := by omega
    rw [div_le_iff₀ (by exact_mod_cast hc)]
    exact_mod_cast hle
  have hs : 0 < 2 ^ s := Nat.two_pow_pos s
  have h₁ : (y : ℝ) / 2 ^ s ≤ (((y + (2 ^ s - 1)) >>> s : ℕ) : ℝ) := by
    rw [Nat.shiftRight_eq_div_pow]
    have := hceil y (2 ^ s) hs
    push_cast at this ⊢
    exact this
  have h₂ := hceil ((y + (2 ^ s - 1)) >>> s) d hd
  calc (y : ℝ) / (2 ^ s * d) = (y : ℝ) / 2 ^ s / d := by rw [div_div]
    _ ≤ (((y + (2 ^ s - 1)) >>> s : ℕ) : ℝ) / d := by gcongr
    _ ≤ ((((y + (2 ^ s - 1)) >>> s) + (d - 1)) / d : ℕ) := h₂
    _ = _ := by
      congr 1
      simp only [Nat.add_eq, Nat.sub_eq, show ∀ a b : ℕ, Nat.div a b = a / b from fun _ _ ↦ rfl,
        Nat.shiftRight_eq, natShiftLeft_one]

/-- The grid state bounds the scaled term and the scaled parity sums. -/
theorem sphericalBesselNatGridState_sound (p m a s : ℕ) {x : ℝ} (hx : x ^ 2 / 2 = a / 2 ^ s)
    (K : ℕ) :
    let D : ℝ := 2 ^ p * ((2 * m + 1)‼ : ℕ)
    let t := fun k ↦ sphericalBesselTermAbs m k x
    let S := sphericalBesselNatGridState p m a s K
    (S.1 : ℝ) ≤ D * t K ∧ D * t K ≤ S.2.1 ∧
      (S.2.2.1 : ℝ) ≤ D * (sphericalBesselParityParts t K).1 ∧
        D * (sphericalBesselParityParts t K).1 ≤ S.2.2.2.1 ∧
      (S.2.2.2.2.1 : ℝ) ≤ D * (sphericalBesselParityParts t K).2 ∧
        D * (sphericalBesselParityParts t K).2 ≤ S.2.2.2.2.2 := by
  intro D t S
  have hD : D * t 0 = 2 ^ p := by
    have hd : (((2 * m + 1)‼ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.doubleFactorial_pos _).ne'
    simp only [D, t, sphericalBesselTermAbs, pow_zero, Nat.factorial_zero, Nat.cast_one,
      one_mul, Nat.mul_zero, Nat.add_zero, one_div]
    field_simp
  induction K with
  | zero =>
    have h1 : ((Nat.shiftLeft 1 p : ℕ) : ℝ) = 2 ^ p := by
      rw [natShiftLeft_one]; push_cast; rfl
    simp only [S, sphericalBesselNatGridState, sphericalBesselParityParts, h1, hD, mul_zero,
      Nat.cast_zero, le_refl, and_self]
  | succ K ih =>
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := ih
    set S₀ := sphericalBesselNatGridState p m a s K with hS₀
    obtain ⟨L, U, xl, xh, yl, yh⟩ := S₀
    have hstate : sphericalBesselNatGridState p m a s (K + 1) =
        (let d := Nat.mul (Nat.succ K) (Nat.add (Nat.add (Nat.mul 2 m) (Nat.mul 2 K)) 3)
        (Nat.div (Nat.shiftRight (Nat.mul L a) s) d,
          Nat.div (Nat.add (Nat.shiftRight (Nat.add (Nat.mul U a)
            (Nat.sub (Nat.shiftLeft 1 s) 1)) s) (Nat.sub d 1)) d, yl, yh, Nat.add xl L,
            Nat.add xh U)) := by
      rw [sphericalBesselNatGridState, ← hS₀]
    set d := Nat.mul (Nat.succ K) (Nat.add (Nat.add (Nat.mul 2 m) (Nat.mul 2 K)) 3) with hd
    have hdpos : 0 < d := by
      simp only [hd, Nat.mul_eq, Nat.add_eq, Nat.succ_eq_add_one]
      positivity
    have hdR : (d : ℝ) = (K + 1) * (2 * m + 2 * K + 3) := by
      simp only [hd, Nat.mul_eq, Nat.add_eq, Nat.succ_eq_add_one]
      push_cast
      ring
    have hstep : D * t (K + 1) = D * t K * a / (2 ^ s * d) := by
      simp only [t]
      rw [sphericalBesselTermAbs_succ, hdR]
      have h2 : x ^ 2 = 2 * (a / 2 ^ s) := by linarith
      rw [h2]
      field_simp
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    have hden : (0 : ℝ) < 2 ^ s * d := by positivity
    simp only [S, hstate, sphericalBesselParityParts]
    refine ⟨?_, ?_, h₅, h₆, ?_, ?_⟩
    · refine (cast_div_shiftRight_le _ s d).trans ?_
      rw [hstep, Nat.mul_eq]
      push_cast
      gcongr
    · refine le_trans ?_ (le_cast_ceil_div_shiftRight _ s d hdpos)
      rw [hstep, Nat.mul_eq]
      push_cast
      gcongr
    · simp only [Nat.add_eq]
      push_cast
      rw [mul_add]
      exact add_le_add h₃ h₁
    · simp only [Nat.add_eq]
      push_cast
      rw [mul_add]
      exact add_le_add h₄ h₂

/-- `sphericalBesselNatGridBounds p m a s K` bounds `2 ^ p (2m + 1)‼ (-1)^K g_m x` when
`x ^ 2 / 2 = a / 2 ^ s` and `x ^ 2 ≤ 2 (K + 1) (2m + 2K + 3)`. -/
theorem sphericalBesselNatGridBounds_sound (p m a s K : ℕ) {x : ℝ} (hx : x ^ 2 / 2 = a / 2 ^ s)
    (hK : x ^ 2 ≤ 2 * (K + 1) * (2 * m + 2 * K + 3)) :
    ((sphericalBesselNatGridBounds p m a s K).1 : ℝ) ≤
        2 ^ p * ((2 * m + 1)‼ : ℕ) * ((-1) ^ K * reducedSphericalBesselJ m x) ∧
      2 ^ p * ((2 * m + 1)‼ : ℕ) * ((-1) ^ K * reducedSphericalBesselJ m x) ≤
        (sphericalBesselNatGridBounds p m a s K).2 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := sphericalBesselNatGridState_sound p m a s hx K
  obtain ⟨hr₁, hr₂⟩ := reducedSphericalBesselJ_sub_sum_mem (l := m) hK
  set t := fun k ↦ sphericalBesselTermAbs m k x with ht
  have hsum : ∑ k ∈ Finset.range K, sphericalBesselTerm m k x =
      ∑ k ∈ Finset.range K, (-1) ^ k * t k := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [sphericalBesselTerm_eq_neg_one_pow_mul]
  have hparts := sphericalBesselParityParts_sub t K
  set D : ℝ := 2 ^ p * ((2 * m + 1)‼ : ℕ) with hD
  have hDpos : 0 < D := by
    have := Nat.doubleFactorial_pos (2 * m + 1)
    positivity
  rw [hsum] at hr₁ hr₂
  set g := reducedSphericalBesselJ m x
  set P := sphericalBesselParityParts t K
  have heq : (-1) ^ K * g =
      P.1 - P.2 + (-1) ^ K * (g - ∑ k ∈ Finset.range K, (-1) ^ k * t k) := by
    rw [hparts]
    ring
  have hlo : D * (P.1 - P.2) ≤ D * ((-1) ^ K * g) := by
    rw [heq]
    exact mul_le_mul_of_nonneg_left (by linarith) hDpos.le
  have hhi : D * ((-1) ^ K * g) ≤ D * (P.1 - P.2) + D * t K := by
    rw [heq, ← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) hDpos.le
  unfold sphericalBesselNatGridBounds
  set S := sphericalBesselNatGridState p m a s K
  obtain ⟨L, U, xl, xh, yl, yh⟩ := S
  simp only at h₁ h₂ h₃ h₄ h₅ h₆ ⊢
  push_cast
  constructor
  · nlinarith
  · nlinarith

end PDE.Analysis.SpecialFunctions
