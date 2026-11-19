/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Legendre polynomials as finite cosine series

Write `a k = ∏_{i < k} (1 - 1 / (2 (i + 1)))` for the normalized double factorial
`(2k - 1)!! / (2k)!!`. Grouping the frequencies `±(n - 2k)` in the classical expansion
`P_n (cos θ) = ∑_{k ≤ n} a k * a (n - k) * cos ((n - 2k) θ)` gives the even series
`P_{2N} (cos θ) = ∑_{j ≤ N} c_j cos (2jθ)`, with `c_0 = a N ^ 2` and
`c_j = 2 a (N + j) a (N - j)` otherwise, and the odd series
`P_{2N+1} (cos θ) = ∑_{j ≤ N} 2 a (N + j + 1) a (N - j) cos ((2j + 1) θ)`.

The coefficients of both series satisfy two-term recurrences. Under them the weighted
spherical angular operator `(sin θ S')' + n (n + 1) sin θ S` sends each cosine mode to its two
neighbouring sine frequencies, and the contributions cancel in pairs, so each series solves
the spherical angular equation. A polynomial `P` for which `sin² θ · P' (cos θ)` has
derivative `μ sin θ · P (cos θ)` solves the Legendre equation
`(1 - c²) P'' - 2c P' + μ P = 0` at every real argument.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Polynomial
open scoped BigOperators

/-- The normalized double factorial `(2n - 1)!! / (2n)!! = ∏_{k < n} (1 - 1 / (2 (k + 1)))`,
which equals `(2n choose n) / 4 ^ n`. -/
def halfCentralBinomial (n : ℕ) : ℚ :=
  ∏ k ∈ Finset.range n, (1 - 1 / (2 * ((k : ℚ) + 1)))

/-- Each step multiplies the normalized double factorial by `1 - 1 / (2 (n + 1))`. -/
theorem halfCentralBinomial_succ (n : ℕ) :
    halfCentralBinomial (n + 1) =
      halfCentralBinomial n * (1 - 1 / (2 * ((n : ℚ) + 1))) := by
  simp only [halfCentralBinomial, Finset.prod_range_succ]

/-- The coefficient of `cos (2jθ)` in `P_{2N} (cos θ)`. -/
def evenCosineCoefficient (N j : ℕ) : ℚ :=
  if j ≤ N then
    (if j = 0 then 1 else 2) * halfCentralBinomial (N + j) * halfCentralBinomial (N - j)
  else 0

/-- The coefficient of `cos ((2j + 1) θ)` in `P_{2N+1} (cos θ)`. -/
def oddCosineCoefficient (N j : ℕ) : ℚ :=
  if j ≤ N then 2 * halfCentralBinomial (N + j + 1) * halfCentralBinomial (N - j)
  else 0

/-- The first odd series is `cos θ`. -/
theorem oddCosineCoefficient_zero (j : ℕ) :
    oddCosineCoefficient 0 j = if j = 0 then 1 else 0 := by
  by_cases hj : j = 0
  · subst j
    norm_num [oddCosineCoefficient, halfCentralBinomial]
  · simp only [oddCosineCoefficient, Nat.le_zero, ite_eq_right hj]

/-- The even coefficients satisfy the recurrence of the weighted spherical angular operator,
with the factor two of the constant mode. -/
theorem evenCosineCoefficient_recurrence (N j : ℕ) :
    ((2 * (N : ℚ)) * (2 * (N : ℚ) + 1) - 2 * (j : ℚ) * (2 * (j : ℚ) + 1)) *
        (if j = 0 then 2 else 1) * evenCosineCoefficient N j =
      ((2 * (N : ℚ)) * (2 * (N : ℚ) + 1) - (2 * (j : ℚ) + 2) *
        (2 * (j : ℚ) + 1)) * evenCosineCoefficient N (j + 1) := by
  by_cases hj : j < N
  · have hjle : j ≤ N := Nat.le_of_lt hj
    have hnext : j + 1 ≤ N := hj
    have hsub : N - j = (N - (j + 1)) + 1 := by omega
    simp only [evenCosineCoefficient, ite_eq_left hjle, ite_eq_left hnext,
      Nat.add_one_ne_zero, ite_false]
    rw [hsub, halfCentralBinomial_succ, show N + (j + 1) = (N + j) + 1 by omega,
      halfCentralBinomial_succ]
    have hd₁ : (2 * ((N - (j + 1) : ℕ) : ℚ) + 2) ≠ 0 := by positivity
    have hd₂ : (2 * ((N + j : ℕ) : ℚ) + 2) ≠ 0 := by positivity
    have hcast : ((N - (j + 1) : ℕ) : ℚ) = (N : ℚ) - (j : ℚ) - 1 := by
      rw [Nat.cast_sub hnext, Nat.cast_add, Nat.cast_one]
      ring
    rw [hcast] at hd₁ ⊢
    simp only [Nat.cast_add] at hd₂ ⊢
    have hdiff : (N : ℚ) - (j : ℚ) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (by exact_mod_cast hj))
    by_cases hzero : j = 0
    · subst j
      norm_num at hd₁ hd₂ ⊢
      field_simp
      ring
    · simp only [ite_eq_right hzero]
      field_simp [hdiff]
      ring
  · have hle : N ≤ j := Nat.le_of_not_lt hj
    by_cases heq : j = N
    · subst j
      simp only [evenCosineCoefficient, le_refl, ite_true,
        Nat.not_succ_le_self, ite_false, sub_self, zero_mul, mul_zero]
    · have hlt : N < j := lt_of_le_of_ne hle (Ne.symm heq)
      simp only [evenCosineCoefficient, ite_eq_right (Nat.not_le_of_lt hlt),
        ite_eq_right (by omega : ¬j + 1 ≤ N), mul_zero]

/-- The odd coefficients satisfy the recurrence of the weighted spherical angular operator. -/
theorem oddCosineCoefficient_recurrence (N j : ℕ) :
    ((2 * (N : ℚ) + 1) * (2 * (N : ℚ) + 2) -
      (2 * (j : ℚ) + 1) * (2 * (j : ℚ) + 2)) * oddCosineCoefficient N j =
    ((2 * (N : ℚ) + 1) * (2 * (N : ℚ) + 2) -
      (2 * (j : ℚ) + 3) * (2 * (j : ℚ) + 2)) * oddCosineCoefficient N (j + 1) := by
  by_cases hj : j < N
  · have hjle : j ≤ N := Nat.le_of_lt hj
    have hnext : j + 1 ≤ N := hj
    have hsub : N - j = N - (j + 1) + 1 := by omega
    simp only [oddCosineCoefficient, ite_eq_left hjle, ite_eq_left hnext]
    rw [hsub, halfCentralBinomial_succ (N - (j + 1)),
      show N + (j + 1) + 1 = (N + j + 1) + 1 by omega,
      halfCentralBinomial_succ (N + j + 1)]
    have hd₁ : (2 * ((N - (j + 1) : ℕ) : ℚ) + 2) ≠ 0 := by positivity
    have hd₂ : (2 * ((N + j + 1 : ℕ) : ℚ) + 2) ≠ 0 := by positivity
    have hcast : ((N - (j + 1) : ℕ) : ℚ) = (N : ℚ) - (j : ℚ) - 1 := by
      rw [Nat.cast_sub hnext, Nat.cast_add, Nat.cast_one]
      ring
    rw [hcast] at hd₁ ⊢
    simp only [Nat.cast_add, Nat.cast_one] at hd₂ ⊢
    have hdiff : (N : ℚ) - (j : ℚ) ≠ 0 :=
      ne_of_gt (sub_pos.mpr (by exact_mod_cast hj))
    field_simp [hdiff]
    ring
  · have hle : N ≤ j := Nat.le_of_not_lt hj
    by_cases heq : j = N
    · subst j
      simp only [oddCosineCoefficient, le_refl, ite_true,
        Nat.not_succ_le_self, ite_false, sub_self, zero_mul, mul_zero]
    · have hlt : N < j := lt_of_le_of_ne hle (Ne.symm heq)
      simp only [oddCosineCoefficient, ite_eq_right (Nat.not_le_of_lt hlt),
        ite_eq_right (by omega : ¬j + 1 ≤ N), mul_zero]

/-- The contribution of the cosine mode `a cos (ωθ)` to the weighted spherical angular
operator `(sin θ S')' + μ sin θ S`. -/
def cosineModeResidual (μ a ω θ : ℝ) : ℝ :=
  (μ - ω ^ 2) * a * Real.sin θ * Real.cos (ω * θ) -
    ω * a * Real.cos θ * Real.sin (ω * θ)

/-- The weighted angular operator sends a cosine mode to its two neighbouring sine modes. -/
theorem cosineModeResidual_eq_shift (μ a ω θ : ℝ) :
    cosineModeResidual μ a ω θ =
      a / 2 * ((μ - ω * (ω + 1)) * Real.sin ((ω + 1) * θ) -
        (μ - ω * (ω - 1)) * Real.sin ((ω - 1) * θ)) := by
  rw [show (ω + 1) * θ = ω * θ + θ by ring, show (ω - 1) * θ = ω * θ - θ by ring,
    Real.sin_add, Real.sin_sub]
  unfold cosineModeResidual
  ring

/-- Under the even recurrence the residuals of the frequencies `0, 2, …, 2n` telescope to
the single sine frequency `2n + 1`; the constant mode counts twice because its two
neighbouring sines coincide up to sign. -/
theorem sum_cosineModeResidual_even (μ : ℝ) (a : ℕ → ℝ)
    (hrec : ∀ j : ℕ,
      (μ - 2 * (j : ℝ) * (2 * (j : ℝ) + 1)) * (if j = 0 then 2 else 1) * a j =
        (μ - (2 * (j : ℝ) + 2) * (2 * (j : ℝ) + 1)) * a (j + 1))
    (n : ℕ) (θ : ℝ) :
    (∑ j ∈ Finset.range (n + 1), cosineModeResidual μ (a j) (2 * (j : ℝ)) θ) =
      (if n = 0 then 1 else (1 / 2 : ℝ)) *
        (μ - 2 * (n : ℝ) * (2 * (n : ℝ) + 1)) * a n *
          Real.sin ((2 * (n : ℝ) + 1) * θ) := by
  induction n with
  | zero => simp [cosineModeResidual]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, cosineModeResidual_eq_shift]
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_one_ne_zero, ite_false]
    have hcancel : (if n = 0 then 1 else (1 / 2 : ℝ)) *
        (μ - 2 * (n : ℝ) * (2 * (n : ℝ) + 1)) * a n =
      (μ - (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1)) * a (n + 1) / 2 := by
      have h := hrec n
      by_cases hn : n = 0
      · simp only [ite_eq_left hn] at h ⊢
        linarith only [h]
      · simp only [ite_eq_right hn] at h ⊢
        linarith only [h]
    rw [hcancel, show (2 * ((n : ℝ) + 1) - 1) * θ =
      (2 * (n : ℝ) + 1) * θ by ring]
    ring

/-- Under the odd recurrence the residuals of the frequencies `1, 3, …, 2n + 1` telescope
to the single sine frequency `2n + 2`. -/
theorem sum_cosineModeResidual_odd (μ : ℝ) (a : ℕ → ℝ)
    (hrec : ∀ j : ℕ,
      (μ - (2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2)) * a j =
        (μ - (2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 2)) * a (j + 1))
    (n : ℕ) (θ : ℝ) :
    (∑ j ∈ Finset.range (n + 1), cosineModeResidual μ (a j) (2 * (j : ℝ) + 1) θ) =
      (1 / 2 : ℝ) * (μ - (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2)) * a n *
        Real.sin ((2 * (n : ℝ) + 2) * θ) := by
  have hshift (j : ℕ) (b : ℝ) : cosineModeResidual μ b (2 * (j : ℝ) + 1) θ =
      b / 2 * ((μ - (2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2)) *
          Real.sin ((2 * (j : ℝ) + 2) * θ) -
        (μ - (2 * (j : ℝ) + 1) * (2 * (j : ℝ))) * Real.sin (2 * (j : ℝ) * θ)) := by
    rw [cosineModeResidual_eq_shift, show 2 * (j : ℝ) + 1 + 1 = 2 * (j : ℝ) + 2 by ring,
      show 2 * (j : ℝ) + 1 - 1 = 2 * (j : ℝ) by ring]
  induction n with
  | zero =>
    rw [Finset.sum_range_one, hshift]
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add, Real.sin_zero, sub_zero]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hshift]
    have hcancel := hrec n
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show 2 * ((n : ℝ) + 1) = 2 * (n : ℝ) + 2 by ring,
      show 2 * (n : ℝ) + 2 + 1 = 2 * (n : ℝ) + 3 by ring]
    rw [show (1 / 2 : ℝ) *
        (μ - (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 2)) * a n =
      a (n + 1) / 2 * (μ - (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 2)) by
        linarith only [hcancel]]
    ring

/-- The even series `∑ evenCosineCoefficient N j cos (2jθ)` solves the weighted spherical
angular equation with eigenvalue `2N (2N + 1)`, for every truncation `K ≥ N`. -/
theorem sum_cosineModeResidual_evenCosineCoefficient (N K : ℕ) (hNK : N ≤ K) (θ : ℝ) :
    (∑ j ∈ Finset.range (K + 1), cosineModeResidual ((2 * (N : ℝ)) * (2 * (N : ℝ) + 1))
      (evenCosineCoefficient N j) (2 * (j : ℝ)) θ) = 0 := by
  have hrec (j : ℕ) :
      ((2 * (N : ℝ)) * (2 * (N : ℝ) + 1) - 2 * (j : ℝ) * (2 * (j : ℝ) + 1)) *
          (if j = 0 then 2 else 1) * (evenCosineCoefficient N j : ℝ) =
        ((2 * (N : ℝ)) * (2 * (N : ℝ) + 1) - (2 * (j : ℝ) + 2) *
          (2 * (j : ℝ) + 1)) * (evenCosineCoefficient N (j + 1) : ℝ) := by
    have h := congrArg (fun x : ℚ ↦ (x : ℝ)) (evenCosineCoefficient_recurrence N j)
    push_cast at h
    by_cases hj0 : j = 0 <;> simpa [hj0] using h
  rw [sum_cosineModeResidual_even _ _ hrec]
  by_cases hKN : K = N
  · subst K
    simp only [sub_self, mul_zero, zero_mul]
  · have hlt : N < K := lt_of_le_of_ne hNK (Ne.symm hKN)
    simp only [evenCosineCoefficient, ite_eq_right (Nat.not_le_of_lt hlt),
      Rat.cast_zero, mul_zero, zero_mul]

/-- The odd series `∑ oddCosineCoefficient N j cos ((2j + 1)θ)` solves the weighted
spherical angular equation with eigenvalue `(2N + 1)(2N + 2)`, for every truncation
`K ≥ N`. -/
theorem sum_cosineModeResidual_oddCosineCoefficient (N K : ℕ) (hNK : N ≤ K) (θ : ℝ) :
    (∑ j ∈ Finset.range (K + 1), cosineModeResidual
      ((2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2)) (oddCosineCoefficient N j)
        (2 * (j : ℝ) + 1) θ) = 0 := by
  have hrec (j : ℕ) :
      ((2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2) -
        (2 * (j : ℝ) + 1) * (2 * (j : ℝ) + 2)) * (oddCosineCoefficient N j : ℝ) =
      ((2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 2) -
        (2 * (j : ℝ) + 3) * (2 * (j : ℝ) + 2)) * (oddCosineCoefficient N (j + 1) : ℝ) := by
    have h := congrArg (fun x : ℚ ↦ (x : ℝ)) (oddCosineCoefficient_recurrence N j)
    push_cast at h
    exact h
  rw [sum_cosineModeResidual_odd _ _ hrec]
  by_cases hKN : K = N
  · subst K
    simp only [sub_self, mul_zero, zero_mul]
  · have hlt : N < K := lt_of_le_of_ne hNK (Ne.symm hKN)
    simp only [oddCosineCoefficient, ite_eq_right (Nat.not_le_of_lt hlt),
      Rat.cast_zero, mul_zero, zero_mul]

/-- If `P (cos t) = S t` for every `t` and `S` has derivative `-T θ` at `θ`, then
`P' (cos θ) sin θ = T θ`. -/
theorem derivative_eval_cos_mul_sin {P : ℝ[X]} {S T : ℝ → ℝ}
    (hS : ∀ t : ℝ, P.eval (Real.cos t) = S t) {θ : ℝ} (hd : HasDerivAt S (-T θ) θ) :
    P.derivative.eval (Real.cos θ) * Real.sin θ = T θ := by
  have hP := (P.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)
  simp only [Function.comp_def] at hP
  rw [show (fun t ↦ P.eval (Real.cos t)) = S from funext hS] at hP
  have h := hP.unique hd
  linarith only [h]

/-- If `sin² t · P' (cos t)` has derivative `μ sin θ · P (cos θ)` at every angle, then `P`
solves the Legendre equation at every real argument, including `c = ±1`. -/
theorem legendre_equation_of_hasDerivAt {P : ℝ[X]} {μ : ℝ}
    (hflux : ∀ θ : ℝ, HasDerivAt (fun t ↦ Real.sin t ^ 2 * P.derivative.eval (Real.cos t))
      (μ * Real.sin θ * P.eval (Real.cos θ)) θ) (c : ℝ) :
    (1 - c ^ 2) * P.derivative.derivative.eval c - 2 * c * P.derivative.eval c +
      μ * P.eval c = 0 := by
  have hcos (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
      (1 - Real.cos θ ^ 2) * P.derivative.derivative.eval (Real.cos θ) -
        2 * Real.cos θ * P.derivative.eval (Real.cos θ) + μ * P.eval (Real.cos θ) = 0 := by
    have hp := (P.derivative.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)
    have hd := ((Real.hasDerivAt_sin θ).pow 2).mul hp
    have h := hd.unique (hflux θ)
    norm_num only [Function.comp_def, Pi.pow_apply, Nat.reduceSub, Nat.cast_ofNat,
      pow_one] at h
    have htrig := Real.sin_sq_add_cos_sq θ
    have hproduct : Real.sin θ *
        ((1 - Real.cos θ ^ 2) * P.derivative.derivative.eval (Real.cos θ) -
          2 * Real.cos θ * P.derivative.eval (Real.cos θ) + μ * P.eval (Real.cos θ)) = 0 := by
      rw [show 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 by linarith only [htrig]]
      nlinarith only [h]
    exact (mul_eq_zero.mp hproduct).resolve_left hθ
  let R : ℝ[X] := (1 - X ^ 2) * P.derivative.derivative - (2 * X) * P.derivative + C μ * P
  have hzero : R = 0 := by
    apply eq_zero_of_infinite_isRoot
    apply (Set.Ioo_infinite (by norm_num : (-1 : ℝ) < 1)).mono
    intro x hx
    change R.IsRoot x
    have hs : Real.sin (Real.arccos x) ≠ 0 := by
      rw [Real.sin_arccos]
      apply ne_of_gt
      apply Real.sqrt_pos.mpr
      nlinarith only [hx.1, hx.2]
    have h := hcos (Real.arccos x) hs
    rw [Real.cos_arccos hx.1.le hx.2.le] at h
    simpa only [IsRoot, R, eval_add, eval_sub, eval_mul, eval_one, eval_pow,
      eval_X, eval_ofNat, eval_C] using h
  have h := congrArg (fun Q : ℝ[X] ↦ Q.eval c) hzero
  simpa only [R, eval_add, eval_sub, eval_mul, eval_one, eval_pow, eval_X,
    eval_ofNat, eval_C, eval_zero] using h

end PDE.Analysis
