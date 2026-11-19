/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.PlanarStrainKernelRectangle
public import CAS.Numerics.GaussianPairs

/-!
# Integer evaluation of strain Taylor sums

For a centre `c = C/Z` and scales `hₖ = Hₖ/Z` with integers `C₁ + i C₂ = C`, `H₁`, `H₂` and any
`Z ≠ 0`, the Taylor sum `h₁ h₂ ∑_{m ≤ n} ∑_{s ≤ m} κ_{m,s} T_{s,m-s}` of
`PotentialTheory.Planar.strainTaylorCoeff` with integer moments `T` is the quotient of two
integers:

`h₁ h₂ ∑ κ T = -H₁ H₂ Im (H C̄^{n+2}) / (2 |C|^{2(n+2)})`, `H = ∑_m (m + 1) (-1)^m Dₘ C^{n-m}`,
`Dₘ = ∑_s C(m, s) H₁^s (i H₂)^{m-s} T_{s,m-s}`,

where `H` is evaluated by Horner's rule in Gaussian integers (pairs of integers). The factor `Z`
cancels: the sum is invariant under the common scaling of `c`, `h₁`, `h₂`.

## Main definitions

* `taylorTerm`: `Dₘ` in Gaussian integers.
* `taylorHorner`: Horner's rule `H_k = H_{k-1} C + (k + 1) (-1)^k D_k`, `H_{-1} = 0`.
* `taylorNumerator`, `taylorDenominator`: the integers `-H₁ H₂ Im (H C̄^{n+2})` and
  `2 |C|^{2(n+2)}`.

## Main results

* `taylorNumerator_div_eq`: `h₁ h₂ ∑_{m ≤ n} ∑_{s ≤ m} κ_{m,s} T_{s,m-s}` equals
  `taylorNumerator / taylorDenominator`.
* `gaussianToComplex_taylorHorner`: Horner's rule computes
  `H = ∑_{m ≤ n} (m + 1) (-1)^m Dₘ C^{n-m}`.
* `gaussianToComplex_taylorTerm`: `taylorTerm` computes `Dₘ`.
* `strainTaylorCoeff_div`: `κ(c/Z, h₁/Z, h₂/Z) = Z² κ(c, h₁, h₂)`.
* `binomial_eq`: the factorial quotient `binomial m s` is the binomial coefficient `C(m, s)`.
-/

@[expose] public section

noncomputable section

open Finset Complex CAS.Numerics
open scoped ComplexConjugate

namespace PotentialTheory.Planar

/-- The binomial coefficient as a quotient of factorials, which evaluates in linear time. -/
def binomial (m s : ℕ) : ℤ := (m.descFactorial s / s.factorial : ℕ)

/-- The factorial quotient `binomial m s` is the binomial coefficient `C(m, s)`. -/
theorem binomial_eq (m s : ℕ) : binomial m s = m.choose s := by
  rw [binomial, Nat.choose_eq_descFactorial_div_factorial]

/-- The term `Dₘ = ∑_s C(m, s) H₁^s (i H₂)^{m-s} T_{s,m-s}` in Gaussian integers. -/
def taylorTerm (T : ℕ → ℕ → ℤ) (H₁ H₂ : ℤ) (m : ℕ) : ℤ × ℤ :=
  ∑ s ∈ range (m + 1),
    let a : ℤ := binomial m s * H₁ ^ s * H₂ ^ (m - s) * T s (m - s)
    (a * (gaussianIPow (m - s)).1, a * (gaussianIPow (m - s)).2)

/-- Horner's rule `H_k = H_{k-1} C + (k + 1) (-1)^k D_k`, `H_{-1} = 0`. -/
def taylorHorner (T : ℕ → ℕ → ℤ) (C : ℤ × ℤ) (H₁ H₂ : ℤ) : ℕ → ℤ × ℤ
  | 0 => taylorTerm T H₁ H₂ 0
  | k + 1 =>
    let a : ℤ := (k + 2 : ℤ) * (-1) ^ (k + 1)
    let D := taylorTerm T H₁ H₂ (k + 1)
    gaussianMul (taylorHorner T C H₁ H₂ k) C + (a * D.1, a * D.2)

/-- The integer numerator `-H₁ H₂ Im (H C̄^{n+2})`. -/
def taylorNumerator (T : ℕ → ℕ → ℤ) (C : ℤ × ℤ) (H₁ H₂ : ℤ) (n : ℕ) : ℤ :=
  -(H₁ * H₂ * (gaussianMul (taylorHorner T C H₁ H₂ n) (gaussianPow (C.1, -C.2) (n + 2))).2)

/-- The integer denominator `2 |C|^{2(n+2)}`. -/
def taylorDenominator (C : ℤ × ℤ) (n : ℕ) : ℤ :=
  2 * (C.1 ^ 2 + C.2 ^ 2) ^ (n + 2)

/-- The pair `taylorTerm T H₁ H₂ m` is the complex number
`Dₘ = ∑_s C(m, s) H₁^s (i H₂)^{m-s} T_{s,m-s}`. -/
theorem gaussianToComplex_taylorTerm (T : ℕ → ℕ → ℤ) (H₁ H₂ : ℤ) (m : ℕ) :
    gaussianToComplex (taylorTerm T H₁ H₂ m) = ∑ s ∈ range (m + 1),
      ((m.choose s : ℕ) : ℂ) * (H₁ : ℂ) ^ s * (I * (H₂ : ℂ)) ^ (m - s) * (T s (m - s) : ℂ) := by
  unfold taylorTerm
  induction (range (m + 1)) using Finset.induction_on with
  | empty => simp [gaussianToComplex]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, gaussianToComplex_add, ih]
    congr 1
    dsimp only
    have h := gaussianToComplex_smul (binomial m a * H₁ ^ a * H₂ ^ (m - a) * T a (m - a))
      (gaussianIPow (m - a))
    rw [gaussianToComplex_iPow] at h
    rw [h, mul_pow, binomial_eq]
    push_cast
    ring

/-- Horner's rule computes `H = ∑_{m ≤ n} (m + 1) (-1)^m Dₘ C^{n-m}`: this is the complex number of
`taylorHorner T C H₁ H₂ n`. -/
theorem gaussianToComplex_taylorHorner (T : ℕ → ℕ → ℤ) (C : ℤ × ℤ) (H₁ H₂ : ℤ) (n : ℕ) :
    gaussianToComplex (taylorHorner T C H₁ H₂ n) = ∑ m ∈ range (n + 1),
      ((m + 1 : ℕ) : ℂ) * (-1) ^ m * gaussianToComplex (taylorTerm T H₁ H₂ m) *
        gaussianToComplex C ^ (n - m) := by
  induction n with
  | zero => simp [taylorHorner]
  | succ k ih =>
    rw [taylorHorner, gaussianToComplex_add, gaussianToComplex_mul, ih, gaussianToComplex_smul]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [Finset.sum_mul]
    congr 1
    · apply sum_congr rfl
      intro m hm
      have hmk : m ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hm)
      rw [show k + 1 - m = (k - m) + 1 by omega, pow_succ]
      ring
    · rw [Nat.sub_self, pow_zero]
      push_cast
      ring

/-- The Taylor coefficients scale like `|c|⁻²`: `κ(c/Z, h₁/Z, h₂/Z) = Z² κ(c, h₁, h₂)`. -/
theorem strainTaylorCoeff_div {c : ℂ} (hc : c ≠ 0) (h₁ h₂ : ℝ) {Z : ℝ} (hZ : Z ≠ 0) {m s : ℕ}
    (hsm : s ≤ m) :
    strainTaylorCoeff (c / Z) (h₁ / Z) (h₂ / Z) m s = Z ^ 2 * strainTaylorCoeff c h₁ h₂ m s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hsm
  unfold strainTaylorCoeff
  rw [Nat.add_sub_cancel_left]
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ
  have heq : ((s + t + 1 : ℕ) : ℂ) * (-1) ^ (s + t) * (((s + t).choose s : ℕ) : ℂ) *
      (((h₁ / Z : ℝ)) : ℂ) ^ s * (I * ((h₂ / Z : ℝ) : ℂ)) ^ t * (((c / Z) ^ (s + t + 2))⁻¹) =
      ((Z ^ 2 : ℝ) : ℂ) * (((s + t + 1 : ℕ) : ℂ) * (-1) ^ (s + t) * (((s + t).choose s : ℕ) : ℂ) *
        (h₁ : ℂ) ^ s * (I * (h₂ : ℂ)) ^ t * ((c ^ (s + t + 2))⁻¹)) := by
    push_cast
    rw [mul_div_assoc', div_pow, div_pow, div_pow, inv_div, pow_add, pow_add]
    field_simp
    ring
  rw [heq, Complex.im_ofReal_mul]
  ring

/-- **The integer quotient of a strain Taylor sum**: with `c = C/Z` and `hₖ = Hₖ/Z`,
`h₁ h₂ ∑_{m ≤ n} ∑_{s ≤ m} κ_{m,s} T_{s,m-s} = taylorNumerator / taylorDenominator`. -/
theorem taylorNumerator_div_eq (T : ℕ → ℕ → ℤ) {C : ℤ × ℤ}
    (hC : gaussianToComplex C ≠ 0) (H₁ H₂ : ℤ) {Z : ℝ} (hZ : Z ≠ 0) (n : ℕ) :
    (taylorNumerator T C H₁ H₂ n : ℝ) / (taylorDenominator C n : ℝ) =
      (H₁ / Z) * (H₂ / Z) * ∑ m ∈ range (n + 1), ∑ s ∈ range (m + 1),
        strainTaylorCoeff (gaussianToComplex C / Z) (H₁ / Z) (H₂ / Z) m s * (T s (m - s) : ℝ) := by
  set Cc := gaussianToComplex C with hCc
  -- remove the scale `Z`
  have hscale : (H₁ / Z) * (H₂ / Z) * ∑ m ∈ range (n + 1), ∑ s ∈ range (m + 1),
      strainTaylorCoeff (Cc / Z) (H₁ / Z) (H₂ / Z) m s * (T s (m - s) : ℝ) =
      (H₁ : ℝ) * H₂ * ∑ m ∈ range (n + 1), ∑ s ∈ range (m + 1),
        strainTaylorCoeff Cc H₁ H₂ m s * (T s (m - s) : ℝ) := by
    rw [sum_congr rfl fun m _ ↦ sum_congr rfl fun s hs ↦ by
      rw [strainTaylorCoeff_div hC H₁ H₂ hZ (Nat.lt_succ_iff.mp (mem_range.mp hs)), mul_assoc]]
    simp only [← Finset.mul_sum]
    field_simp
  rw [hscale]
  -- the complex form of each inner sum
  have hinner : ∀ m, ∑ s ∈ range (m + 1), strainTaylorCoeff Cc H₁ H₂ m s * (T s (m - s) : ℝ) =
      -(((m + 1 : ℕ) : ℂ) * (-1) ^ m * gaussianToComplex (taylorTerm T H₁ H₂ m) *
        ((Cc ^ (m + 2))⁻¹)).im / 2 := by
    intro m
    rw [gaussianToComplex_taylorTerm, Finset.mul_sum, Finset.sum_mul, Complex.im_sum,
      neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine sum_congr rfl fun s _ ↦ ?_
    unfold strainTaylorCoeff
    have h : ((m + 1 : ℕ) : ℂ) * (-1) ^ m * (((m.choose s : ℕ) : ℂ) * (H₁ : ℂ) ^ s *
        (I * (H₂ : ℂ)) ^ (m - s) * (T s (m - s) : ℂ)) * ((Cc ^ (m + 2))⁻¹) =
        (((m + 1 : ℕ) : ℂ) * (-1) ^ m * ((m.choose s : ℕ) : ℂ) * ((H₁ : ℝ) : ℂ) ^ s *
          (I * ((H₂ : ℝ) : ℂ)) ^ (m - s) * ((Cc ^ (m + 2))⁻¹)) * ((T s (m - s) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h, Complex.im_mul_ofReal]
    ring
  simp_rw [hinner]
  rw [← Finset.sum_div, Finset.sum_neg_distrib, ← Complex.im_sum]
  -- Horner's rule
  have hhorner : ∑ m ∈ range (n + 1), ((m + 1 : ℕ) : ℂ) * (-1) ^ m *
      gaussianToComplex (taylorTerm T H₁ H₂ m) * ((Cc ^ (m + 2))⁻¹) =
      gaussianToComplex (taylorHorner T C H₁ H₂ n) * ((Cc ^ (n + 2))⁻¹) := by
    rw [gaussianToComplex_taylorHorner, Finset.sum_mul]
    refine sum_congr rfl fun m hm ↦ ?_
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (mem_range.mp hm))
    rw [Nat.add_sub_cancel_left, show m + t + 2 = (m + 2) + t by ring, pow_add, ← hCc]
    field_simp
    ring
  rw [hhorner]
  -- the conjugate form of the inverse power
  have hinv : (Cc ^ (n + 2))⁻¹ = conj Cc ^ (n + 2) * ((normSq Cc ^ (n + 2))⁻¹ : ℝ) := by
    rw [Complex.inv_def, map_pow, map_pow]
  rw [hinv, ← mul_assoc, Complex.im_mul_ofReal]
  unfold taylorNumerator taylorDenominator
  push_cast
  rw [← gaussianToComplex_im, gaussianToComplex_mul, gaussianPow_eq, gaussianToComplex_conj,
    normSq_gaussianToComplex, ← hCc]
  push_cast
  have hN : (C.1 : ℝ) ^ 2 + (C.2 : ℝ) ^ 2 ≠ 0 := by
    have := normSq_gaussianToComplex C
    push_cast [← hCc] at this
    exact this ▸ normSq_eq_zero.not.mpr hC
  field_simp

end PotentialTheory.Planar
