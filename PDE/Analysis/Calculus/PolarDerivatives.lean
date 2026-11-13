/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.SpecialFunctions.Trigonometric.TrigSampling
public import PDE.Analysis.Calculus.Deriv.Curried

/-!
# Cartesian derivatives of functions of the polar coordinates

For `g(x, y) = A(r) B(β)` in polar coordinates, Chen and Hou expand
`∂ₓⁱ ∂_yʲ g = ∑_{k + l ≤ i + j} C_{i,j,k,l}(β) r^{k - i - j} A^{(k)}(r) B^{(l)}(β)` ((C.15)), where
the coefficients satisfy `C_{0,0,0,0} = 1` and the recursions
`C_{i+1,j,k,l} = (k - i - j) cos β C - sin β ∂_β C + cos β C_{i,j,k-1,l} - sin β C_{i,j,k,l-1}`
((C.17)) and `C_{i,j+1,k,l} = (k - i - j) sin β C + cos β ∂_β C + sin β C_{i,j,k-1,l} +
cos β C_{i,j,k,l-1}` ((C.18)), with `C = C_{i,j,k,l}` and zero for negative indices.

Here the coefficients are computed exactly as lists of trigonometric terms with rational
coefficients, built by the `y`-recursion and then the `x`-recursion. Every frequency is at most
`i + j` in absolute value (attained by `C_{1,0,1,0} = cos β`), and `C_{i,j,k,l}` vanishes for
`k + l > i + j`. The second `β`-derivative of a coefficient, the function whose supremum the cell
estimates use, is bounded by its samples at `2πj/M` for `M > 2(i + j)`.

The algebra of one differentiation step and the chart structure `IsPolarChart` are here; the
expansion itself is `derivX_iterate_derivY_iterate_eq` in `PolarExpansion`. It holds on any open
set where `r` and `β` have the derivatives of a polar chart, `∂ₓ r = cos β`, `∂_y r = sin β`,
`∂ₓ β = -sin β / r`, `∂_y β = cos β / r`, with `r > 0`; the gradient of `β` alone does not fix
the chart. The radial and angular factors enter through derivative chains `A k`, `B l`.

## Main definitions

* `polarCoeff`: the table `C_{i,j,·,·}` of (C.15), as lists of trigonometric terms.
* `polarExpansion`: the expansion `∑ C_{kl}(β) r^{k - n} A_k(r) B_l(β)` of order `n` with a
  table `C`.
* `IsPolarChart`: `r > 0` and the derivatives of a polar chart `(r, β)` on an open set.

## Main results

* `polarCoeff_succ`: `C_{i+1,j,·,·}` is the `x`-step (C.17) of `C_{i,j,·,·}`.
* `trigTermsEval_polarStepX`: the value of the `x`-step is the right side of (C.17).
* `trigTermsEval_polarStepY`: the value of the `y`-step is the right side of (C.18).
* `polarCoeff_eq_nil`: `C_{i,j,k,l} = 0` for `k + l > i + j`.
* `polarCoeff_freq_le`: every frequency in `C_{i,j,k,l}` is at most `i + j`.
* `polar_step_sum`: the derivative of the expansion of order `n` is the expansion of order
  `n + 1` with the stepped table.
* `abs_polarCoeff_deriv_deriv_le_sqrt_samples`: for `M > 2(i + j)`,
  `|∂_β² C_{i,j,k,l}(β)| ≤ ((2(i + j) / M) ∑_{j' < M} (∂_β² C_{i,j,k,l})(2πj'/M)²)^{1/2}`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, Appendix C.3.1,
  (C.15)-(C.18), and Appendix C.3.2. <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace PDE.Analysis

open Finset Real

/-! ### Coefficient tables -/

/-- A list of terms scaled by a rational. -/
def trigTermsScale (c : ℚ) (l : List TrigTerm) : List TrigTerm :=
  l.map fun t ↦ ⟨c * t.coeff, t.freq, t.isSin⟩

/-- The termwise derivative of a list. -/
def trigTermsDeriv (l : List TrigTerm) : List TrigTerm := l.map TrigTerm.deriv

/-- `cos θ` as a term. -/
def cosTerm : TrigTerm := ⟨1, 1, false⟩

/-- `sin θ` as a term. -/
def sinTerm : TrigTerm := ⟨1, 1, true⟩

/-- Scaling every coefficient of a list by `c` multiplies its value by `c`. -/
theorem trigTermsEval_scale (c : ℚ) (l : List TrigTerm) (θ : ℝ) :
    trigTermsEval (trigTermsScale c l) θ = c * trigTermsEval l θ := by
  induction l with
  | nil => simp [trigTermsScale]
  | cons t l ih =>
    simp only [trigTermsScale, List.map_cons, trigTermsEval_cons] at ih ⊢
    rw [ih]
    simp only [TrigTerm.eval]
    push_cast
    ring

/-- Multiplying a list by `cosTerm` multiplies its value by `cos θ`. -/
theorem trigTermsEval_cosTerm_mul (l : List TrigTerm) (θ : ℝ) :
    trigTermsEval (trigTermsMul [cosTerm] l) θ = Real.cos θ * trigTermsEval l θ := by
  rw [trigTermsEval_trigTermsMul]
  simp [trigTermsEval, cosTerm, TrigTerm.eval]

/-- Multiplying a list by `sinTerm` multiplies its value by `sin θ`. -/
theorem trigTermsEval_sinTerm_mul (l : List TrigTerm) (θ : ℝ) :
    trigTermsEval (trigTermsMul [sinTerm] l) θ = Real.sin θ * trigTermsEval l θ := by
  rw [trigTermsEval_trigTermsMul]
  simp [trigTermsEval, sinTerm, TrigTerm.eval]

/-- The `x`-step (C.17) from order `n`. -/
def polarStepX (n : ℕ) (C : ℕ → ℕ → List TrigTerm) (k l : ℕ) : List TrigTerm :=
  trigTermsMul [cosTerm] (trigTermsScale ((k : ℚ) - n) (C k l)) ++
    trigTermsScale (-1) (trigTermsMul [sinTerm] (trigTermsDeriv (C k l))) ++
    (if k = 0 then [] else trigTermsMul [cosTerm] (C (k - 1) l)) ++
    (if l = 0 then [] else trigTermsScale (-1) (trigTermsMul [sinTerm] (C k (l - 1))))

/-- The `y`-step (C.18) from order `n`. -/
def polarStepY (n : ℕ) (C : ℕ → ℕ → List TrigTerm) (k l : ℕ) : List TrigTerm :=
  trigTermsMul [sinTerm] (trigTermsScale ((k : ℚ) - n) (C k l)) ++
    trigTermsMul [cosTerm] (trigTermsDeriv (C k l)) ++
    (if k = 0 then [] else trigTermsMul [sinTerm] (C (k - 1) l)) ++
    (if l = 0 then [] else trigTermsMul [cosTerm] (C k (l - 1)))

/-- The base table: `C_{0,0,0,0} = 1`. -/
def polarBase (k l : ℕ) : List TrigTerm := if k = 0 ∧ l = 0 then [⟨1, 0, false⟩] else []

/-- The coefficients `C_{0,j,·,·}` by the `y`-recursion. -/
def polarCoeffY : ℕ → ℕ → ℕ → List TrigTerm
  | 0 => polarBase
  | j + 1 => polarStepY j (polarCoeffY j)

/-- The coefficients `C_{i,j,·,·}` of (C.15): the `y`-recursion `j` times, then the `x`-recursion
`i` times. -/
def polarCoeff (i j : ℕ) : ℕ → ℕ → List TrigTerm :=
  Nat.rec (polarCoeffY j) (fun i C ↦ polarStepX (i + j) C) i

/-- The coefficients `C_{0,j,·,·}` are those of the `y`-recursion, `polarCoeffY j`. -/
@[simp] theorem polarCoeff_zero (j : ℕ) : polarCoeff 0 j = polarCoeffY j := rfl

/-- The coefficients `C_{i+1,j,·,·}` are the `x`-step (C.17) of `C_{i,j,·,·}` from order `i + j`. -/
@[simp] theorem polarCoeff_succ (i j : ℕ) :
    polarCoeff (i + 1) j = polarStepX (i + j) (polarCoeff i j) := rfl

/-- The product of a list with the empty list is empty. -/
theorem trigTermsMul_nil (l : List TrigTerm) : trigTermsMul l [] = [] := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [trigTermsMul]

/-- If the table `C` vanishes for `k + l > n`, its `x`-step from order `n` vanishes for
`k + l > n + 1`. -/
theorem polarStepX_eq_nil {n : ℕ} {C : ℕ → ℕ → List TrigTerm}
    (hC : ∀ k l, n < k + l → C k l = []) {k l : ℕ} (hkl : n + 1 < k + l) :
    polarStepX n C k l = [] := by
  have h1 := hC k l (by omega)
  simp only [polarStepX, h1, trigTermsScale, trigTermsDeriv, List.map_nil, trigTermsMul_nil,
    List.nil_append]
  split_ifs with hk hl hl
  · rfl
  · rw [hC k (l - 1) (by omega)]; simp [trigTermsMul_nil]
  · rw [hC (k - 1) l (by omega)]; simp [trigTermsMul_nil]
  · rw [hC (k - 1) l (by omega), hC k (l - 1) (by omega)]
    simp [trigTermsMul_nil]

/-- If the table `C` vanishes for `k + l > n`, its `y`-step from order `n` vanishes for
`k + l > n + 1`. -/
theorem polarStepY_eq_nil {n : ℕ} {C : ℕ → ℕ → List TrigTerm}
    (hC : ∀ k l, n < k + l → C k l = []) {k l : ℕ} (hkl : n + 1 < k + l) :
    polarStepY n C k l = [] := by
  have h1 := hC k l (by omega)
  simp only [polarStepY, h1, trigTermsScale, trigTermsDeriv, List.map_nil, trigTermsMul_nil,
    List.nil_append]
  split_ifs with hk hl hl
  · rfl
  · rw [hC k (l - 1) (by omega)]; simp [trigTermsMul_nil]
  · rw [hC (k - 1) l (by omega)]; simp [trigTermsMul_nil]
  · rw [hC (k - 1) l (by omega), hC k (l - 1) (by omega)]; simp [trigTermsMul_nil]

/-- **Support of the coefficients.** `C_{i,j,k,l} = 0` for `k + l > i + j`. -/
theorem polarCoeff_eq_nil (i j : ℕ) : ∀ k l, i + j < k + l → polarCoeff i j k l = [] := by
  induction i with
  | zero =>
    induction j with
    | zero =>
      intro k l hkl
      simp only [polarCoeff_zero, polarCoeffY, polarBase]
      exact ite_eq_right_iff.mpr fun h ↦ absurd h (by omega)
    | succ j ih =>
      intro k l hkl
      simp only [polarCoeff_zero, polarCoeffY] at ih ⊢
      exact polarStepY_eq_nil (fun k l h ↦ ih k l (by omega)) (by omega)
  | succ i ih =>
    intro k l hkl
    rw [polarCoeff_succ]
    exact polarStepX_eq_nil ih (by omega)

/-! ### Values of the recursions -/

/-- The value of the `x`-step (C.17) is
`(k - n) cos θ C_{k,l} - sin θ ∂_θ C_{k,l} + cos θ C_{k-1,l} - sin θ C_{k,l-1}`, where the last two
terms are absent for `k = 0` and for `l = 0`. -/
theorem trigTermsEval_polarStepX (n : ℕ) (C : ℕ → ℕ → List TrigTerm) (k l : ℕ) (θ : ℝ) :
    trigTermsEval (polarStepX n C k l) θ =
      ((k : ℝ) - n) * Real.cos θ * trigTermsEval (C k l) θ +
        -Real.sin θ * trigTermsEval (trigTermsDeriv (C k l)) θ +
        (if k = 0 then 0 else Real.cos θ * trigTermsEval (C (k - 1) l) θ) +
        (if l = 0 then 0 else -Real.sin θ * trigTermsEval (C k (l - 1)) θ) := by
  unfold polarStepX
  split_ifs <;> simp only [trigTermsEval_append, trigTermsEval_cosTerm_mul, trigTermsEval_scale,
    trigTermsEval_sinTerm_mul, trigTermsEval_nil] <;> push_cast <;> ring

/-- The value of the `y`-step (C.18) is
`(k - n) sin θ C_{k,l} + cos θ ∂_θ C_{k,l} + sin θ C_{k-1,l} + cos θ C_{k,l-1}`, where the last two
terms are absent for `k = 0` and for `l = 0`. -/
theorem trigTermsEval_polarStepY (n : ℕ) (C : ℕ → ℕ → List TrigTerm) (k l : ℕ) (θ : ℝ) :
    trigTermsEval (polarStepY n C k l) θ =
      ((k : ℝ) - n) * Real.sin θ * trigTermsEval (C k l) θ +
        Real.cos θ * trigTermsEval (trigTermsDeriv (C k l)) θ +
        (if k = 0 then 0 else Real.sin θ * trigTermsEval (C (k - 1) l) θ) +
        (if l = 0 then 0 else Real.cos θ * trigTermsEval (C k (l - 1)) θ) := by
  unfold polarStepY
  split_ifs <;> simp only [trigTermsEval_append, trigTermsEval_cosTerm_mul, trigTermsEval_scale,
    trigTermsEval_sinTerm_mul, trigTermsEval_nil] <;> push_cast <;> ring

/-! ### Frequencies -/

/-- Every frequency of a list is at most `m` in absolute value. -/
def FreqLE (m : ℕ) (l : List TrigTerm) : Prop := ∀ t ∈ l, t.freq.natAbs ≤ m

/-- A frequency bound `m` implies every larger bound `m'`. -/
theorem FreqLE.mono {m m' : ℕ} {l : List TrigTerm} (h : FreqLE m l) (hm : m ≤ m') :
    FreqLE m' l := fun t ht ↦ (h t ht).trans hm

/-- Scaling the coefficients of a list keeps its frequency bound. -/
theorem freqLE_scale {m : ℕ} {l : List TrigTerm} (h : FreqLE m l) (c : ℚ) :
    FreqLE m (trigTermsScale c l) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact h s hs

/-- Termwise differentiation of a list keeps its frequency bound. -/
theorem freqLE_deriv {m : ℕ} {l : List TrigTerm} (h : FreqLE m l) :
    FreqLE m (trigTermsDeriv l) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  unfold TrigTerm.deriv
  split_ifs <;> exact h s hs

/-- Two lists with frequency bound `m` have a concatenation with frequency bound `m`. -/
theorem freqLE_append {m : ℕ} {l l' : List TrigTerm} (h : FreqLE m l) (h' : FreqLE m l') :
    FreqLE m (l ++ l') := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact h t ht
  · exact h' t ht

/-- The empty list has every frequency bound. -/
theorem freqLE_nil (m : ℕ) : FreqLE m [] := fun _ ht ↦ absurd ht List.not_mem_nil

/-- Multiplying by a frequency-one term raises the frequencies by at most one. -/
theorem freqLE_mul_single {m : ℕ} {l : List TrigTerm} (h : FreqLE m l) {u : TrigTerm}
    (hu : u.freq = 1) : FreqLE (m + 1) (trigTermsMul [u] l) := by
  intro t ht
  simp only [trigTermsMul, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_flatMap] at ht
  obtain ⟨s, hs, ht⟩ := ht
  have hsm := h s hs
  unfold TrigTerm.mul at ht
  rcases u with ⟨cu, fu, bu⟩
  rcases s with ⟨cs, fs, bs⟩
  simp only at hu hsm
  subst hu
  cases bu <;> cases bs <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ht <;>
    rcases ht with rfl | rfl <;> simp only <;> omega

/-- **Degree of the coefficients.** Every frequency in `C_{i,j,k,l}` is at most `i + j`. -/
theorem polarCoeff_freq_le (i j k l : ℕ) : FreqLE (i + j) (polarCoeff i j k l) := by
  induction i generalizing k l with
  | zero =>
    induction j generalizing k l with
    | zero =>
      simp only [polarCoeff_zero, polarCoeffY, polarBase]
      split_ifs
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        subst ht
        simp
      · exact freqLE_nil _
    | succ j ih =>
      simp only [polarCoeff_zero, polarCoeffY, Nat.zero_add] at ih ⊢
      refine freqLE_append (freqLE_append (freqLE_append ?_ ?_) ?_) ?_
      · exact freqLE_mul_single (freqLE_scale (ih k l) _) rfl
      · exact freqLE_mul_single (freqLE_deriv (ih k l)) rfl
      · split_ifs
        · exact freqLE_nil _
        · exact freqLE_mul_single (ih _ _) rfl
      · split_ifs
        · exact freqLE_nil _
        · exact freqLE_mul_single (ih _ _) rfl
  | succ i ih =>
    rw [polarCoeff_succ, show i + 1 + j = i + j + 1 by ring]
    refine freqLE_append (freqLE_append (freqLE_append ?_ ?_) ?_) ?_
    · exact freqLE_mul_single (freqLE_scale (ih k l) _) rfl
    · exact freqLE_scale (freqLE_mul_single (freqLE_deriv (ih k l)) rfl) _
    · split_ifs
      · exact freqLE_nil _
      · exact freqLE_mul_single (ih _ _) rfl
    · split_ifs
      · exact freqLE_nil _
      · exact freqLE_scale (freqLE_mul_single (ih _ _) rfl) _

/-! ### The expansion and its derivatives -/

/-- The polar expansion of order `n` with the table `C` over the box `k, l < N`:
`∑ C_{kl}(β) r^{k - n} A_k(r) B_l(β)`. -/
noncomputable def polarExpansion (N n : ℕ) (C : ℕ → ℕ → List TrigTerm) (A B : ℕ → ℝ → ℝ)
    (r θ : ℝ) : ℝ :=
  ∑ k ∈ range N, ∑ l ∈ range N, trigTermsEval (C k l) θ * r ^ ((k : ℤ) - n) * A k r * B l θ

/-- The derivatives of a polar chart `(r, β)` on an open set `U`: `r > 0`, `∂ₓ r = cos β`,
`∂_y r = sin β`, `∂ₓ β = -sin β / r`, `∂_y β = cos β / r`. -/
structure IsPolarChart (U : Set (ℝ × ℝ)) (ρ θ : ℝ → ℝ → ℝ) : Prop where
  isOpen : IsOpen U
  pos : ∀ p ∈ U, 0 < ρ p.1 p.2
  hasDerivAt_ρ_x : ∀ p ∈ U, HasDerivAt (fun t ↦ ρ t p.2) (Real.cos (θ p.1 p.2)) p.1
  hasDerivAt_ρ_y : ∀ p ∈ U, HasDerivAt (ρ p.1) (Real.sin (θ p.1 p.2)) p.2
  hasDerivAt_θ_x : ∀ p ∈ U,
    HasDerivAt (fun t ↦ θ t p.2) (-Real.sin (θ p.1 p.2) / ρ p.1 p.2) p.1
  hasDerivAt_θ_y : ∀ p ∈ U, HasDerivAt (θ p.1) (Real.cos (θ p.1 p.2) / ρ p.1 p.2) p.2

/-- Shifting the summation index down by one, with the boundary term removed. -/
theorem sum_range_ite_pred (F : ℕ → ℝ) {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ range N, (if k = 0 then 0 else F (k - 1)) = ∑ k ∈ range N, F k - F (N - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [sum_range_succ', sum_range_succ]
  simp

/-- The algebra of one differentiation step: with `r' = u` and `r β' = v`, the derivative of the
expansion of order `n` is the expansion of order `n + 1` with the table
`(k - n) u C + v C' + u C_{k-1,l} + v C_{k,l-1}`. -/
theorem polar_step_sum (N n : ℕ) (hN : n + 2 ≤ N) (c c' : ℕ → ℕ → ℝ)
    (hc : ∀ k l, n < k + l → c k l = 0) {ρ : ℝ} (hρ : ρ ≠ 0) (u v : ℝ) (a b : ℕ → ℝ) :
    ∑ k ∈ range N, ∑ l ∈ range N,
      (c' k l * (v / ρ) * ρ ^ ((k : ℤ) - n) * a k * b l +
        c k l * (((k : ℤ) - n : ℤ) * ρ ^ ((k : ℤ) - n - 1) * u) * a k * b l +
        c k l * ρ ^ ((k : ℤ) - n) * (a (k + 1) * u) * b l +
        c k l * ρ ^ ((k : ℤ) - n) * a k * (b (l + 1) * (v / ρ))) =
    ∑ k ∈ range N, ∑ l ∈ range N,
      (((k : ℝ) - n) * u * c k l + v * c' k l + (if k = 0 then 0 else u * c (k - 1) l) +
        (if l = 0 then 0 else v * c k (l - 1))) * ρ ^ ((k : ℤ) - (n + 1 : ℕ)) * a k * b l := by
  set P : ℕ → ℝ := fun k ↦ ρ ^ ((k : ℤ) - n)
  have e1 : ∀ k : ℕ, ρ ^ ((k : ℤ) - (n + 1 : ℕ)) = P k * ρ⁻¹ := fun k ↦ by
    rw [show (k : ℤ) - ((n + 1 : ℕ) : ℤ) = ((k : ℤ) - n) - 1 by push_cast; ring,
      zpow_sub_one₀ hρ]
  have e2 : ∀ k : ℕ, ρ ^ ((k : ℤ) - n - 1) = P k * ρ⁻¹ := fun k ↦ zpow_sub_one₀ hρ _
  have e3 : ∀ k : ℕ, P (k + 1) * ρ⁻¹ = P k := fun k ↦ by
    simp only [P]
    rw [← zpow_sub_one₀ hρ]
    congr 1
    push_cast
    ring
  simp only [e1, e2]
  -- split the right side into the main part and the two shifted parts
  have hsplit : ∀ k l : ℕ, (((k : ℝ) - n) * u * c k l + v * c' k l +
      (if k = 0 then 0 else u * c (k - 1) l) + (if l = 0 then 0 else v * c k (l - 1))) *
        (P k * ρ⁻¹) * a k * b l =
      (((k : ℝ) - n) * u * c k l + v * c' k l) * (P k * ρ⁻¹) * a k * b l +
        (if k = 0 then 0 else u * c (k - 1) l * (P k * ρ⁻¹) * a k * b l) +
        (if l = 0 then 0 else v * c k (l - 1) * (P k * ρ⁻¹) * a k * b l) := by
    intro k l
    split_ifs <;> ring
  simp only [hsplit, sum_add_distrib]
  -- the shift in `k`
  have hk : ∑ k ∈ range N, ∑ l ∈ range N,
      (if k = 0 then 0 else u * c (k - 1) l * (P k * ρ⁻¹) * a k * b l) =
      ∑ k ∈ range N, ∑ l ∈ range N, c k l * P k * (a (k + 1) * u) * b l := by
    have hrw : ∀ k ∈ range N, (∑ l ∈ range N,
        (if k = 0 then 0 else u * c (k - 1) l * (P k * ρ⁻¹) * a k * b l)) =
        if k = 0 then 0 else (fun k' ↦ ∑ l ∈ range N, c k' l * P k' * (a (k' + 1) * u) * b l)
          (k - 1) := by
      intro k _
      split_ifs with h0
      · simp
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel, e3]
        refine sum_congr rfl fun l _ ↦ ?_
        ring
    rw [sum_congr rfl hrw, sum_range_ite_pred
      (fun k' ↦ ∑ l ∈ range N, c k' l * P k' * (a (k' + 1) * u) * b l) (by omega : 0 < N)]
    have hzero : ∑ l ∈ range N, c (N - 1) l * P (N - 1) * (a (N - 1 + 1) * u) * b l = 0 :=
      sum_eq_zero fun l _ ↦ by rw [hc (N - 1) l (by omega)]; ring
    rw [hzero, sub_zero]
  -- the shift in `l`
  have hl : ∑ k ∈ range N, ∑ l ∈ range N,
      (if l = 0 then 0 else v * c k (l - 1) * (P k * ρ⁻¹) * a k * b l) =
      ∑ k ∈ range N, ∑ l ∈ range N, c k l * P k * a k * (b (l + 1) * (v / ρ)) := by
    refine sum_congr rfl fun k _ ↦ ?_
    have hrw : ∀ l ∈ range N, (if l = 0 then 0 else v * c k (l - 1) * (P k * ρ⁻¹) * a k * b l) =
        if l = 0 then 0 else (fun l' ↦ c k l' * P k * a k * (b (l' + 1) * (v / ρ))) (l - 1) := by
      intro l _
      split_ifs with h0
      · rfl
      · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        ring
    rw [sum_congr rfl hrw, sum_range_ite_pred
      (fun l' ↦ c k l' * P k * a k * (b (l' + 1) * (v / ρ))) (by omega : 0 < N)]
    simp only [hc k (N - 1) (by omega)]
    ring
  rw [hk, hl]
  have hB1 : ∑ k ∈ range N, ∑ l ∈ range N,
      (((k : ℝ) - n) * u * c k l + v * c' k l) * (P k * ρ⁻¹) * a k * b l =
      ∑ k ∈ range N, ∑ l ∈ range N, c' k l * (v / ρ) * P k * a k * b l +
      ∑ k ∈ range N, ∑ l ∈ range N,
        c k l * ((((k : ℤ) - n : ℤ) : ℝ) * (P k * ρ⁻¹) * u) * a k * b l := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun l _ ↦ ?_
    push_cast
    ring
  linarith [hB1]

/-- **Part II, App C.3.2 for the coefficients.** For `M > 2(i + j)`,
`|∂_β² C_{i,j,k,l}(β)| ≤ ((2(i + j) / M) ∑_{j' < M} (∂_β² C_{i,j,k,l})(2πj'/M)²)^{1/2}`. -/
theorem abs_polarCoeff_deriv_deriv_le_sqrt_samples (i j k l : ℕ) {M : ℕ} (hM : 2 * (i + j) < M)
    (β : ℝ) :
    |trigTermsEval (trigTermsDeriv (trigTermsDeriv (polarCoeff i j k l))) β| ≤
      Real.sqrt (2 * ((i + j : ℕ) : ℝ) / M * ∑ m ∈ range M,
        trigTermsEval (trigTermsDeriv (trigTermsDeriv (polarCoeff i j k l)))
          (2 * π * m / M) ^ 2) :=
  abs_trigTermsEval_deriv_le_sqrt_samples _ (freqLE_deriv (polarCoeff_freq_le i j k l)) hM β

end PDE.Analysis
