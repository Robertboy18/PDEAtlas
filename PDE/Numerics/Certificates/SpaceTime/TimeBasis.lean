/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import PDE.Analysis.Approximation.HermiteBounds
public import CAS.Polynomial.CoefficientList

/-!
# Polynomial bases in time

A space-time certificate represents a field on a time block as `∑ᵢ bᵢ(τ) cᵢ`, with polynomials
`bᵢ` in the local time `τ` of a reference interval `[lo, hi]` and spatial coefficients `cᵢ`.
`TimeBasis n` stores the monomial coefficients of `b₀, …, b_{n-1}` as lists of rationals, a matrix
`D` with `bᵢ' = ∑ⱼ D i j bⱼ` and upper bounds of `∫_lo^hi |bᵢ|`. With these three pieces of data
the residual `(∂ₜ - 𝓛)` of a block is again a combination of the `bⱼ` with coefficients computed
from the `cᵢ` (`SpaceTime.BlockField`), and its time integral is bounded by the coefficients and
the absolute integrals.

## Main definitions

* `polyDeriv`, `polyIntegral`: the derivatives (`coeffEval_polyDeriv`) and exact integrals
  (`integral_coeffEval`) of polynomials given as coefficient lists (`coeffEval`).
* `TimeBasis.Sound`: the derivative identity and the absolute integral bounds;
  `TimeBasis.derivCheck` decides the derivative identity for a given matrix exactly.
* `taylor`: `taylor n r` is `bᵢ = τⁱ / i!` on `[-r, r]` with `D` the shift and the exact absolute
  integrals `2 r^{i+1} / (i+1)!`. For `n = 4`, `r = 3/2` this is the block of three time steps of
  Chen and Hou, Part II, Section 3.4, with `τ = s / k`; the absolute integrals are the constants
  `C_I = [3, 9/4, 9/8, 27/64]` of Part II (3.31) (`taylor_absIntegral`), and the four-point
  formula of (3.31) interpolates the snapshots at `τ = -3/2, -1/2, 1/2, 3/2`
  (`sum_eval_smul_lagrangeCombination`).
* `hermite`: the cubic Hermite basis on `[0, 1]` of `PDE.Analysis.Approximation.hermiteCubic`
  (values and scaled slopes at the two ends), with exact absolute integrals.
* `chebyshev`: `chebyshev N` is the Chebyshev polynomials `T₀, …, T_N` on `[-1, 1]`
  (`eval_chebyshev`), with `∫ |Tᵢ| ≤ 2` and the derivative matrix `Tᵢ' = 2 i ∑' Tⱼ` (sum over
  `j < i` of the other parity, the term `j = 0` halved), checked by `derivCheck` for each degree.

## Main results

* `integral_coeffEval`: `∫_a^b ∑ⱼ lⱼ τʲ dτ` is the difference of the exact antiderivative.
* `TimeBasis.deriv_eq_of_derivCheck`: a passed `derivCheck` gives `bᵢ' = ∑ⱼ D i j bⱼ` everywhere.
* `taylor_sound`: for `r > 0` the Taylor basis on `[-r, r]` is sound, with the exact absolute
  integrals and the bounds `|bᵢ| ≤ rⁱ / i!`.
* `taylor_absIntegral`: `∫_{-3/2}^{3/2} |τ|ⁱ / i! dτ = C_I(i)` with `C_I = [3, 9/4, 9/8, 27/64]`.
* `sum_eval_smul_lagrangeCombination`: at `τ = -3/2 + p` the cubic through the snapshots `W`
  takes the value `W_p`.
* `hermite_sound`: the cubic Hermite basis is sound, with the bounds `1, 1, 4/27, 4/27` on
  `[0, 1]`.
* `chebyshev_sound`: the Chebyshev basis of degree `N` is sound once its derivative matrix is
  checked.
* `chebyshev_derivCheck_twenty`: the Chebyshev basis `T₀, …, T₂₀` passes `derivCheck`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Section 3.4,
  (3.31).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace CAS.Numerics.SpaceTime

open Finset Set MeasureTheory intervalIntegral CAS.Polynomial

/-! ### Polynomials as coefficient lists -/

/-- The coefficients `k a₀, (k + 1) a₁, (k + 2) a₂, …`. -/
def derivCoeffs (k : ℕ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (k * a) :: derivCoeffs (k + 1) l

/-- The monomial coefficients of the derivative. -/
def polyDeriv : List ℚ → List ℚ
  | [] => []
  | _ :: l => derivCoeffs 1 l

/-- The shifted derivative coefficients evaluate to `k p(τ) + τ p'(τ)`. -/
theorem coeffEval_derivCoeffs (k : ℕ) (l : List ℚ) (τ : ℝ) :
    coeffEval (derivCoeffs k l) τ = k * coeffEval l τ + τ * coeffEval (polyDeriv l) τ := by
  induction l generalizing k with
  | nil => simp [derivCoeffs, polyDeriv]
  | cons a l ih =>
    simp only [derivCoeffs, polyDeriv, coeffEval_cons, ih]
    push_cast
    ring

/-- `polyDeriv` and the recursive `coeffDeriv` give the same polynomial. -/
theorem coeffEval_polyDeriv (l : List ℚ) (τ : ℝ) :
    coeffEval (polyDeriv l) τ = coeffEval (coeffDeriv l) τ := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [polyDeriv, coeffEval_derivCoeffs, coeffDeriv, coeffEval_coeffAdd, coeffEval_cons, ih]
    push_cast
    ring

/-- Any derivative of `coeffEval l` is the value of the derivative coefficients. -/
theorem coeffEval_polyDeriv_eq {l : List ℚ} {τ f' : ℝ} (h : HasDerivAt (coeffEval l) f' τ) :
    coeffEval (polyDeriv l) τ = f' := by
  rw [coeffEval_polyDeriv]
  exact (hasDerivAt_coeffEval l τ).unique h

/-- The coefficients `a₀ / (k + 1), a₁ / (k + 2), …`. -/
def integCoeffs (k : ℕ) : List ℚ → List ℚ
  | [] => []
  | a :: l => (a / (k + 1)) :: integCoeffs (k + 1) l

/-- The monomial coefficients of the antiderivative vanishing at `0`. -/
def polyIntegral (l : List ℚ) : List ℚ :=
  0 :: integCoeffs 0 l

/-- Differentiating the integrated coefficients recovers the coefficients. -/
theorem derivCoeffs_integCoeffs (k : ℕ) (l : List ℚ) :
    derivCoeffs (k + 1) (integCoeffs k l) = l := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    simp only [integCoeffs, derivCoeffs, ih]
    congr 1
    push_cast
    field_simp

/-- **Exact integration.** `∫_a^b ∑ⱼ lⱼ τʲ dτ` is the difference of the antiderivative. -/
theorem integral_coeffEval (l : List ℚ) (a b : ℝ) :
    ∫ τ in a..b, coeffEval l τ =
      coeffEval (polyIntegral l) b - coeffEval (polyIntegral l) a := by
  have h : ∀ x, HasDerivAt (coeffEval (polyIntegral l)) (coeffEval l x) x := fun x ↦ by
    have := hasDerivAt_coeffEval (polyIntegral l) x
    rwa [← coeffEval_polyDeriv, polyIntegral, polyDeriv, derivCoeffs_integCoeffs 0 l] at this
  exact integral_eq_sub_of_hasDerivAt (fun x _ ↦ h x)
    ((continuous_coeffEval l).intervalIntegrable _ _)

/-- The coefficients of `∑_{j ∈ js} c j • ls j`. -/
def combineCoeffs {ι : Type*} (c : ι → ℚ) (ls : ι → List ℚ) : List ι → List ℚ
  | [] => []
  | j :: js => coeffAdd (coeffScale (c j) (ls j)) (combineCoeffs c ls js)

/-- The combined coefficients evaluate to `∑_{j ∈ js} c j * p_j(τ)`. -/
theorem coeffEval_combineCoeffs {ι : Type*} (c : ι → ℚ) (ls : ι → List ℚ) (js : List ι)
    (τ : ℝ) :
    coeffEval (combineCoeffs c ls js) τ =
      (js.map fun j ↦ (c j : ℝ) * coeffEval (ls j) τ).sum := by
  induction js with
  | nil => simp [combineCoeffs]
  | cons j js ih => simp [combineCoeffs, coeffEval_coeffAdd, coeffEval_coeffScale, ih]

/-- Whether every coefficient vanishes. -/
def isZeroCoeffs (l : List ℚ) : Bool :=
  l.all (· == 0)

/-- A coefficient list with only zero entries is the zero polynomial. -/
theorem coeffEval_eq_zero_of_isZeroCoeffs {l : List ℚ} (h : isZeroCoeffs l = true) (τ : ℝ) :
    coeffEval l τ = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [isZeroCoeffs, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, ih h.2]

/-! ### Time bases -/

/-- A basis `b₀, …, b_{n-1}` of polynomials in the local time `τ ∈ [lo, hi]` of a block: the
monomial coefficients of each `bᵢ`, a matrix `D` meant to satisfy `bᵢ' = ∑ⱼ D i j bⱼ`, and upper
bounds of `∫_lo^hi |bᵢ|` and of `|bᵢ|` on `[lo, hi]`. `TimeBasis.Sound` states these
properties. -/
structure TimeBasis (n : ℕ) where
  /-- The left end of the reference interval. -/
  lo : ℚ
  /-- The right end of the reference interval. -/
  hi : ℚ
  /-- The monomial coefficients of `bᵢ`, constant term first. -/
  coeff : Fin n → List ℚ
  /-- The derivative matrix: `bᵢ' = ∑ⱼ D i j bⱼ`. -/
  derivMatrix : Fin n → Fin n → ℚ
  /-- Upper bounds of `∫_lo^hi |bᵢ|`. -/
  absIntegral : Fin n → ℚ
  /-- Upper bounds of `|bᵢ|` on `[lo, hi]`. -/
  supBound : Fin n → ℚ

namespace TimeBasis

variable {n : ℕ} (B : TimeBasis n)

/-- The basis function `bᵢ`. -/
def eval (i : Fin n) (τ : ℝ) : ℝ :=
  coeffEval (B.coeff i) τ

/-- The properties of a time basis: a nonempty reference interval, the derivative identity
`bᵢ' = ∑ⱼ D i j bⱼ`, the absolute integral bounds and the bounds on the reference interval. The
functions need not be linearly independent; the estimates use only these properties. -/
structure Sound : Prop where
  /-- The reference interval is nonempty. -/
  lo_lt_hi : B.lo < B.hi
  /-- The derivative identity. -/
  deriv_eq : ∀ i τ,
    coeffEval (polyDeriv (B.coeff i)) τ = ∑ j, (B.derivMatrix i j : ℝ) * B.eval j τ
  /-- The absolute integral bounds. -/
  integral_abs_le : ∀ i, ∫ τ in (B.lo : ℝ)..B.hi, |B.eval i τ| ≤ B.absIntegral i
  /-- The bounds of the basis functions on the reference interval. -/
  abs_le_supBound : ∀ i, ∀ τ ∈ Icc (B.lo : ℝ) B.hi, |B.eval i τ| ≤ B.supBound i

/-- The basis functions are continuous. -/
theorem continuous_eval (i : Fin n) : Continuous (B.eval i) :=
  continuous_coeffEval _

variable {B}

/-- The derivative of a basis function in the basis. -/
theorem Sound.hasDerivAt (hB : B.Sound) (i : Fin n) (τ : ℝ) :
    HasDerivAt (B.eval i) (∑ j, (B.derivMatrix i j : ℝ) * B.eval j τ) τ := by
  rw [← hB.deriv_eq, coeffEval_polyDeriv]
  exact hasDerivAt_coeffEval _ τ

/-- The absolute integral bounds of a sound basis are nonnegative. -/
theorem Sound.absIntegral_nonneg (hB : B.Sound) (i : Fin n) : 0 ≤ (B.absIntegral i : ℝ) :=
  (intervalIntegral.integral_nonneg (by exact_mod_cast hB.lo_lt_hi.le)
    fun _ _ ↦ abs_nonneg _).trans (hB.integral_abs_le i)

variable (B)

/-- The exact integral `∫_lo^hi bᵢ`. -/
def integral (i : Fin n) : ℚ :=
  coeffEvalRat (polyIntegral (B.coeff i)) B.hi - coeffEvalRat (polyIntegral (B.coeff i)) B.lo

/-- `∫_lo^hi bᵢ` is the exact rational `B.integral i`. -/
theorem integral_eval (i : Fin n) : ∫ τ in (B.lo : ℝ)..B.hi, B.eval i τ = B.integral i := by
  simp only [TimeBasis.eval]
  rw [integral_coeffEval, integral, coeffEval_ratCast, coeffEval_ratCast]
  push_cast
  ring

/-- The value `bᵢ(lo)` at the start of the reference interval. -/
def startValue (i : Fin n) : ℚ :=
  coeffEvalRat (B.coeff i) B.lo

/-- The value `bᵢ(hi)` at the end of the reference interval. -/
def endValue (i : Fin n) : ℚ :=
  coeffEvalRat (B.coeff i) B.hi

/-- `bᵢ(lo)` is the rational `B.startValue i`. -/
theorem eval_lo (i : Fin n) : B.eval i B.lo = B.startValue i :=
  coeffEval_ratCast _ _

/-- `bᵢ(hi)` is the rational `B.endValue i`. -/
theorem eval_hi (i : Fin n) : B.eval i B.hi = B.endValue i :=
  coeffEval_ratCast _ _

/-- The exact check of the derivative identity `bᵢ' = ∑ⱼ D i j bⱼ` on the coefficient lists. -/
def derivCheck : Bool :=
  (List.finRange n).all fun i ↦ isZeroCoeffs (coeffAdd (polyDeriv (B.coeff i))
    (coeffScale (-1) (combineCoeffs (B.derivMatrix i) B.coeff (List.finRange n))))

variable {B}

/-- A passed `derivCheck` gives the derivative identity `bᵢ' = ∑ⱼ D i j bⱼ` everywhere. -/
theorem deriv_eq_of_derivCheck (h : B.derivCheck = true) (i : Fin n) (τ : ℝ) :
    coeffEval (polyDeriv (B.coeff i)) τ = ∑ j, (B.derivMatrix i j : ℝ) * B.eval j τ := by
  have hi := List.all_eq_true.1 h i (List.mem_finRange i)
  have h0 := coeffEval_eq_zero_of_isZeroCoeffs hi τ
  rw [coeffEval_coeffAdd, coeffEval_coeffScale, coeffEval_combineCoeffs] at h0
  rw [Fin.sum_univ_def]
  simp only [eval]
  push_cast at h0
  linarith

end TimeBasis

/-! ### The Taylor basis and the cubic blocks of Part II, Section 3.4 -/

/-- The coefficients of `c τⁱ`. -/
def monomialCoeffs (i : ℕ) (c : ℚ) : List ℚ :=
  List.replicate i 0 ++ [c]

/-- The coefficient list `monomialCoeffs i c` is the monomial `c τⁱ`. -/
theorem coeffEval_monomialCoeffs (i : ℕ) (c : ℚ) (τ : ℝ) :
    coeffEval (monomialCoeffs i c) τ = c * τ ^ i := by
  induction i with
  | zero => simp [monomialCoeffs]
  | succ i ih =>
    simp only [monomialCoeffs, List.replicate_succ, List.cons_append, coeffEval_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

/-- `∫_{-r}^{r} |τⁱ| dτ = 2 r^{i+1} / (i + 1)`. -/
theorem integral_abs_pow {r : ℝ} (hr : 0 ≤ r) (i : ℕ) :
    ∫ τ in -r..r, |τ ^ i| = 2 * r ^ (i + 1) / (i + 1) := by
  have hc : Continuous fun τ : ℝ ↦ |τ ^ i| := (continuous_pow i).abs
  have hpos : ∫ τ in (0 : ℝ)..r, |τ ^ i| = r ^ (i + 1) / (i + 1) := by
    rw [intervalIntegral.integral_congr (g := fun τ : ℝ ↦ τ ^ i), integral_pow]
    · simp
    · intro τ hτ
      rw [Set.uIcc_of_le hr] at hτ
      exact abs_of_nonneg (pow_nonneg hτ.1 i)
  have hneg : ∫ τ in -r..0, |τ ^ i| = r ^ (i + 1) / (i + 1) := by
    rw [← hpos]
    have := intervalIntegral.integral_comp_neg (a := 0) (b := r) (fun τ : ℝ ↦ |τ ^ i|)
    rw [neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr fun τ _ ↦ ?_
    simp only [abs_pow, abs_neg]
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), hneg, hpos]
  ring

/-- `∫_{-r}^{r} |τⁱ / i!| dτ = 2 r^{i+1} / (i + 1)!`. -/
theorem integral_abs_pow_div_factorial {r : ℝ} (hr : 0 ≤ r) (i : ℕ) :
    ∫ τ in -r..r, |τ ^ i / (i.factorial : ℝ)| = 2 * r ^ (i + 1) / ((i + 1).factorial : ℝ) := by
  have hf : (0 : ℝ) < i.factorial := by exact_mod_cast Nat.factorial_pos _
  simp only [abs_div, abs_of_pos hf]
  rw [intervalIntegral.integral_div, integral_abs_pow hr, Nat.factorial_succ]
  push_cast
  field_simp

/-- The Taylor basis `bᵢ(τ) = τⁱ / i!`, `i < n`, on `[-r, r]`, with `bᵢ' = bᵢ₋₁` and the exact
absolute integrals `2 r^{i+1} / (i + 1)!`. -/
def taylor (n : ℕ) (r : ℚ) : TimeBasis n where
  lo := -r
  hi := r
  coeff i := monomialCoeffs i (1 / (i : ℕ).factorial)
  derivMatrix i j := if (j : ℕ) + 1 = i then 1 else 0
  absIntegral i := 2 * r ^ ((i : ℕ) + 1) / ((i : ℕ) + 1).factorial
  supBound i := r ^ (i : ℕ) / (i : ℕ).factorial

/-- The Taylor basis function `bᵢ` is `τⁱ / i!`. -/
theorem eval_taylor (n : ℕ) (r : ℚ) (i : Fin n) (τ : ℝ) :
    (taylor n r).eval i τ = τ ^ (i : ℕ) / (i : ℕ).factorial := by
  simp only [TimeBasis.eval, taylor, coeffEval_monomialCoeffs]
  push_cast
  ring

/-- **The absolute integrals of the Taylor basis.** -/
theorem integral_abs_eval_taylor (n : ℕ) {r : ℚ} (hr : 0 ≤ r) (i : Fin n) :
    ∫ τ in ((taylor n r).lo : ℝ)..(taylor n r).hi, |(taylor n r).eval i τ| =
      (taylor n r).absIntegral i := by
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have hlo : ((taylor n r).lo : ℝ) = -r := by simp [taylor]
  have hhi : ((taylor n r).hi : ℝ) = r := by simp [taylor]
  simp only [eval_taylor, hlo, hhi]
  rw [integral_abs_pow_div_factorial hr']
  simp [taylor]

/-- For `r > 0` the Taylor basis on `[-r, r]` is sound: `bᵢ' = bᵢ₋₁`, with the exact absolute
integrals and the bounds `|bᵢ| ≤ rⁱ / i!`. -/
theorem taylor_sound (n : ℕ) {r : ℚ} (hr : 0 < r) : (taylor n r).Sound where
  lo_lt_hi := by simp only [taylor]; linarith
  deriv_eq i τ := by
    have hd : HasDerivAt ((taylor n r).eval i)
        ((i : ℕ) * τ ^ ((i : ℕ) - 1) / (i : ℕ).factorial) τ := by
      have := (hasDerivAt_pow (i : ℕ) τ).div_const ((i : ℕ).factorial : ℝ)
      simpa [funext (eval_taylor n r i)] using this
    rw [coeffEval_polyDeriv_eq (l := (taylor n r).coeff i) hd]
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · have hz : ∀ j : Fin n, ((taylor n r).derivMatrix i j : ℝ) * (taylor n r).eval j τ = 0 := by
        intro j
        simp [taylor, h0]
      rw [Finset.sum_eq_zero fun j _ ↦ hz j, h0]
      simp
    · have hj : (i : ℕ) - 1 < n := by omega
      rw [Finset.sum_eq_single ⟨(i : ℕ) - 1, hj⟩]
      · have hD : (taylor n r).derivMatrix i ⟨(i : ℕ) - 1, hj⟩ = 1 := by
          change (if (i : ℕ) - 1 + 1 = (i : ℕ) then (1 : ℚ) else 0) = 1
          rw [Nat.sub_add_cancel hpos]
          simp
        rw [hD, eval_taylor, ← Nat.mul_factorial_pred hpos.ne']
        have hi : ((i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
        have : (0 : ℝ) < ((i : ℕ) - 1).factorial := by exact_mod_cast Nat.factorial_pos _
        push_cast
        field_simp
      · intro j _ hji
        have : (j : ℕ) + 1 ≠ i := fun h ↦ hji (Fin.ext (by simp; omega))
        simp [taylor, this]
      · simp
  integral_abs_le i := (integral_abs_eval_taylor n hr.le i).le
  abs_le_supBound i τ hτ := by
    have hlo : ((taylor n r).lo : ℝ) = -r := by simp [taylor]
    have hhi : ((taylor n r).hi : ℝ) = r := by simp [taylor]
    rw [hlo, hhi] at hτ
    have hf : (0 : ℝ) < (i : ℕ).factorial := by exact_mod_cast Nat.factorial_pos _
    rw [eval_taylor, abs_div, abs_of_pos hf, abs_pow]
    simp only [taylor]
    push_cast
    gcongr
    exact abs_le.2 hτ

/-- **Part II (3.31), the constants `C_I`.** For the block of three time steps,
`∫_{-3/2}^{3/2} |τ|ⁱ / i! dτ = C_I(i)` with `C_I = [3, 9/4, 9/8, 27/64]`. -/
theorem taylor_absIntegral : (taylor 4 (3 / 2)).absIntegral = ![3, 9 / 4, 9 / 8, 27 / 64] := by
  funext i
  fin_cases i <;> norm_num [taylor, Nat.factorial]

/-- **Part II (3.31) in the time variable.** For a time step `k > 0`,
`∫_{|s| ≤ 3k/2} |s/k|ⁱ / i! ds = k C_I(i)`. -/
theorem integral_abs_div_pow_div_factorial {k : ℝ} (hk : 0 < k) (i : Fin 4) :
    ∫ s in -(3 * k / 2)..3 * k / 2, |s / k| ^ (i : ℕ) / (i : ℕ).factorial =
      k * ((![3, 9 / 4, 9 / 8, 27 / 64] : Fin 4 → ℚ) i : ℝ) := by
  have hf : (0 : ℝ) < (i : ℕ).factorial := by exact_mod_cast Nat.factorial_pos _
  have hsub := intervalIntegral.integral_comp_div
    (fun τ : ℝ ↦ |τ ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)|) hk.ne' (a := -(3 * k / 2))
    (b := 3 * k / 2)
  have e₁ : -(3 * k / 2) / k = -(3 / 2) := by field_simp
  have e₂ : 3 * k / 2 / k = 3 / 2 := by field_simp
  rw [e₁, e₂, integral_abs_pow_div_factorial (by norm_num)] at hsub
  have hl : ∫ s in -(3 * k / 2)..3 * k / 2, |s / k| ^ (i : ℕ) / (i : ℕ).factorial =
      ∫ s in -(3 * k / 2)..3 * k / 2, |(s / k) ^ (i : ℕ) / ((i : ℕ).factorial : ℝ)| :=
    intervalIntegral.integral_congr fun s _ ↦ by simp [abs_div, abs_pow, abs_of_pos hf]
  rw [hl, hsub, smul_eq_mul]
  congr 1
  fin_cases i <;> norm_num [Nat.factorial]

/-- The coefficient vectors `C₀, …, C₃ ∈ ℚ⁴` of the four-point formula of Part II (3.31): the cubic
through the snapshots `V = (W₀, W₁, W₂, W₃)` at `τ = -3/2, -1/2, 1/2, 3/2` is
`∑ᵢ (Cᵢ · V) τⁱ / i!`. -/
def lagrangeCoeff : Fin 4 → Fin 4 → ℚ :=
  ![![-1 / 16, 9 / 16, 9 / 16, -1 / 16], ![1 / 24, -27 / 24, 27 / 24, -1 / 24],
    ![1 / 2, -1 / 2, -1 / 2, 1 / 2], ![-1, 3, -3, 1]]

/-- The matrix `lagrangeCoeff` inverts the values of the Taylor basis at the snapshots
`τ = -3/2 + p`, checked in exact rational arithmetic. -/
theorem lagrangeCoeff_check : ∀ p l : Fin 4,
    ∑ i, coeffEvalRat ((taylor 4 (3 / 2)).coeff i) (-3 / 2 + (p : ℕ)) * lagrangeCoeff i l =
      if p = l then 1 else 0 := by
  decide +kernel

section Lagrange

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The Taylor coefficients `Cᵢ · V = ∑ₗ Cᵢₗ Wₗ` of the cubic through the snapshots `W`. -/
def lagrangeCombination (W : Fin 4 → E) (i : Fin 4) : E :=
  ∑ l, (lagrangeCoeff i l : ℝ) • W l

/-- **The four-point formula interpolates.** At `τ = -3/2 + p` the cubic block of Part II (3.31)
takes the value `W_p`; consecutive blocks that share the snapshot `W_{3m+3}` therefore agree at
their common end. -/
theorem sum_eval_smul_lagrangeCombination (W : Fin 4 → E) (p : Fin 4) :
    ∑ i, (taylor 4 (3 / 2)).eval i (-3 / 2 + (p : ℕ)) • lagrangeCombination W i = W p := by
  have hq : ∀ i, (taylor 4 (3 / 2)).eval i (-3 / 2 + (p : ℕ)) =
      (coeffEvalRat ((taylor 4 (3 / 2)).coeff i) (-3 / 2 + (p : ℕ)) : ℝ) := fun i ↦ by
    rw [← coeffEval_ratCast]
    push_cast
    rfl
  simp only [lagrangeCombination, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hq]
  have hs : ∀ l, ∑ i, (coeffEvalRat ((taylor 4 (3 / 2)).coeff i) (-3 / 2 + (p : ℕ)) : ℝ) *
      (lagrangeCoeff i l : ℝ) = if p = l then 1 else 0 := fun l ↦ by
    have := congrArg (fun q : ℚ ↦ (q : ℝ)) (lagrangeCoeff_check p l)
    push_cast at this
    rw [this]
    split_ifs <;> simp
  simp only [hs, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end Lagrange

/-! ### The cubic Hermite basis -/

/-- The cubic Hermite basis `(H₀₀, H₀₁, H₁₀, H₁₁)` on `[0, 1]`: the values at `0` and `1` and the
slopes at `0` and `1` in the local time. Its derivative matrix expresses each derivative by its own
end values and slopes, and the absolute integrals are exact (`H₀₀, H₀₁, H₁₀ ≥ 0 ≥ H₁₁` on
`[0, 1]`). The coefficients of the slopes are local: on a block of time scale `k` they are `k`
times the physical slopes, so consecutive blocks are `C¹` in time when `m₁ / kₘ = m₀ / kₘ₊₁`. -/
def hermite : TimeBasis 4 where
  lo := 0
  hi := 1
  coeff := ![[1, 0, -3, 2], [0, 0, 3, -2], [0, 1, -2, 1], [0, 0, -1, 1]]
  derivMatrix := ![![0, 0, -6, 6], ![0, 0, 6, -6], ![1, 0, -4, 2], ![0, 1, -2, 4]]
  absIntegral := ![1 / 2, 1 / 2, 1 / 12, 1 / 12]
  supBound := ![1, 1, 4 / 27, 4 / 27]

/-- The Hermite basis combination is `PDE.Analysis.Approximation.hermiteCubic` (Supp II (8.22)). -/
theorem hermite_eval_combination (l₀ l₁ m₀ m₁ t : ℝ) :
    l₀ * hermite.eval 0 t + l₁ * hermite.eval 1 t + m₀ * hermite.eval 2 t +
        m₁ * hermite.eval 3 t =
      PDE.Analysis.Approximation.hermiteCubic l₀ l₁ m₀ m₁ t := by
  simp [hermite, TimeBasis.eval, PDE.Analysis.Approximation.hermiteCubic]
  ring

/-- The derivative matrix of the cubic Hermite basis passes `derivCheck`. -/
theorem hermite_derivCheck : hermite.derivCheck = true := by
  decide +kernel

/-- The cubic Hermite basis functions in closed form. -/
theorem hermite_eval (i : Fin 4) (τ : ℝ) :
    hermite.eval i τ =
      ![(1 - τ) ^ 2 * (1 + 2 * τ), τ ^ 2 * (3 - 2 * τ), τ * (1 - τ) ^ 2, τ ^ 2 * (τ - 1)] i := by
  fin_cases i <;>
    simp only [hermite, TimeBasis.eval, coeffEval_cons, coeffEval_nil, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one] <;>
    push_cast <;> ring

/-- The cubic Hermite basis has the exact absolute integrals `1/2, 1/2, 1/12, 1/12` on `[0, 1]`. -/
theorem integral_abs_eval_hermite (i : Fin 4) :
    ∫ τ in (hermite.lo : ℝ)..hermite.hi, |hermite.eval i τ| = hermite.absIntegral i := by
  have hsign : ∀ τ ∈ Set.uIcc (0 : ℝ) 1, |hermite.eval i τ| =
      (if i = 3 then -1 else 1) * hermite.eval i τ := by
    intro τ hτ
    rw [Set.uIcc_of_le zero_le_one] at hτ
    obtain ⟨h0, h1⟩ := hτ
    rw [hermite_eval]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (by linarith))]
      simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (by linarith))]
      simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      rw [abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
      simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
      rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith))]
      simp
  have hlo : (hermite.lo : ℝ) = 0 := by simp [hermite]
  have hhi : (hermite.hi : ℝ) = 1 := by simp [hermite]
  rw [hlo, hhi, intervalIntegral.integral_congr hsign, intervalIntegral.integral_const_mul,
    ← hlo, ← hhi, TimeBasis.integral_eval]
  fin_cases i <;> norm_num [hermite, TimeBasis.integral, polyIntegral, integCoeffs, coeffEvalRat]

/-- The cubic Hermite basis is sound, with the bounds `1, 1, 4/27, 4/27` on `[0, 1]`. -/
theorem hermite_sound : hermite.Sound where
  lo_lt_hi := by norm_num [hermite]
  deriv_eq := TimeBasis.deriv_eq_of_derivCheck hermite_derivCheck
  integral_abs_le i := (integral_abs_eval_hermite i).le
  abs_le_supBound i τ hτ := by
    have hlo : (hermite.lo : ℝ) = 0 := by simp [hermite]
    have hhi : (hermite.hi : ℝ) = 1 := by simp [hermite]
    rw [hlo, hhi] at hτ
    obtain ⟨h0, h1⟩ := hτ
    rw [hermite_eval, abs_le]
    fin_cases i <;> simp [hermite] <;> constructor <;>
      nlinarith [mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1), mul_nonneg h0 (sub_nonneg.2 h1),
        mul_nonneg (sq_nonneg (3 * τ - 1)) (sub_nonneg.2 h1),
        mul_nonneg (sq_nonneg (3 * τ - 2)) h0, sq_nonneg (1 - τ), sq_nonneg τ]

/-! ### Chebyshev blocks -/

/-- The coefficient lists of `(T_n, T_{n+1})`, from `T_{n+2} = 2 τ T_{n+1} - T_n`. -/
def chebyshevPair : ℕ → List ℚ × List ℚ
  | 0 => ([1], [0, 1])
  | n + 1 => ((chebyshevPair n).2,
      coeffAdd (0 :: coeffScale 2 (chebyshevPair n).2) (coeffScale (-1) (chebyshevPair n).1))

/-- The monomial coefficients of the Chebyshev polynomial `T_n`. -/
def chebyshevCoeffs (n : ℕ) : List ℚ :=
  (chebyshevPair n).1

/-- The pair `chebyshevPair n` evaluates to the Chebyshev polynomials `(T_n, T_{n+1})`. -/
theorem coeffEval_chebyshevPair (n : ℕ) (τ : ℝ) :
    coeffEval (chebyshevPair n).1 τ = (Polynomial.Chebyshev.T ℝ n).eval τ ∧
      coeffEval (chebyshevPair n).2 τ = (Polynomial.Chebyshev.T ℝ (n + 1)).eval τ := by
  induction n with
  | zero => simp [chebyshevPair]
  | succ n ih =>
    refine ⟨by simpa [chebyshevPair] using ih.2, ?_⟩
    simp only [chebyshevPair, coeffEval_coeffAdd, coeffEval_coeffScale, coeffEval_cons, ih.1,
      ih.2]
    have h := Polynomial.Chebyshev.T_add_two ℝ (n : ℤ)
    have e : ((n + 1 : ℕ) : ℤ) + 1 = (n : ℤ) + 2 := by push_cast; ring
    rw [e, h]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat]
    push_cast
    ring_nf

/-- The coefficient list `chebyshevCoeffs n` evaluates to the Chebyshev polynomial `T_n`. -/
theorem coeffEval_chebyshevCoeffs (n : ℕ) (τ : ℝ) :
    coeffEval (chebyshevCoeffs n) τ = (Polynomial.Chebyshev.T ℝ n).eval τ :=
  (coeffEval_chebyshevPair n τ).1

/-- The derivative matrix of the Chebyshev basis: `Tᵢ' = ∑_{j < i, i - j odd} c_j i Tⱼ` with
`c₀ = 1` and `c_j = 2` otherwise. -/
def chebyshevDeriv (i j : ℕ) : ℚ :=
  if j < i ∧ (i - j) % 2 = 1 then (if j = 0 then i else 2 * i) else 0

/-- The Chebyshev basis `T₀, …, T_N` on `[-1, 1]`, with the absolute integral bound `2`. -/
def chebyshev (N : ℕ) : TimeBasis (N + 1) where
  lo := -1
  hi := 1
  coeff i := chebyshevCoeffs i
  derivMatrix i j := chebyshevDeriv i j
  absIntegral _ := 2
  supBound _ := 1

/-- The Chebyshev basis function `bᵢ` is `Tᵢ`. -/
theorem eval_chebyshev (N : ℕ) (i : Fin (N + 1)) (τ : ℝ) :
    (chebyshev N).eval i τ = (Polynomial.Chebyshev.T ℝ (i : ℕ)).eval τ :=
  coeffEval_chebyshevCoeffs i τ

/-- The Chebyshev basis functions are bounded by `1` on `[-1, 1]`. -/
theorem abs_eval_chebyshev_le (N : ℕ) (i : Fin (N + 1)) {τ : ℝ} (hτ : |τ| ≤ 1) :
    |(chebyshev N).eval i τ| ≤ 1 := by
  rw [eval_chebyshev]
  exact Polynomial.Chebyshev.abs_eval_T_real_le_one _ hτ

/-- The Chebyshev basis of degree `N` is sound once its derivative matrix is checked. -/
theorem chebyshev_sound (N : ℕ) (h : (chebyshev N).derivCheck = true) : (chebyshev N).Sound where
  lo_lt_hi := by norm_num [chebyshev]
  deriv_eq := TimeBasis.deriv_eq_of_derivCheck h
  integral_abs_le i := by
    have hlo : ((chebyshev N).lo : ℝ) = -1 := by simp [chebyshev]
    have hhi : ((chebyshev N).hi : ℝ) = 1 := by simp [chebyshev]
    have hab : ((chebyshev N).absIntegral i : ℝ) = 2 := by simp [chebyshev]
    rw [hlo, hhi, hab]
    calc ∫ τ in (-1 : ℝ)..1, |(chebyshev N).eval i τ| ≤ ∫ _ in (-1 : ℝ)..1, (1 : ℝ) :=
          intervalIntegral.integral_mono_on (by norm_num)
            (((chebyshev N).continuous_eval i).abs.intervalIntegrable _ _)
            intervalIntegrable_const fun τ hτ ↦
              abs_eval_chebyshev_le N i (abs_le.2 ⟨hτ.1, hτ.2⟩)
      _ = 2 := by norm_num
  abs_le_supBound i τ hτ := by
    have hlo : ((chebyshev N).lo : ℝ) = -1 := by simp [chebyshev]
    have hhi : ((chebyshev N).hi : ℝ) = 1 := by simp [chebyshev]
    rw [hlo, hhi] at hτ
    simpa [chebyshev] using abs_eval_chebyshev_le N i (abs_le.2 hτ)

/-- The Chebyshev basis `T₀, …, T₂₀` passes `derivCheck`, checked in the kernel. -/
theorem chebyshev_derivCheck_twenty : (chebyshev 20).derivCheck = true := by
  decide +kernel

end CAS.Numerics.SpaceTime
