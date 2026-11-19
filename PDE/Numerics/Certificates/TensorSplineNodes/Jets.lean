/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Approximation.Splines.TruncatedPowerCell
public import CAS.Analysis.Approximation.Splines.PiecewisePolynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Exact jets of modified B-spline modes on mesh cells

A mode of a tensor B-spline representation is a finite combination of raw B-splines of order
`n + 2` and of their reflections `x ↦ B_r(-x)`, as in Chen and Hou, Part II, (C.4)-(C.12): the
odd tangential modes `B_i(x) - B_i(-x)`, the normal modes with the extrapolated boundary modes
absorbed, the far-field extrapolated modes and the scale factors are all of this form. The raw
spline `r` is the truncated-power formula on the knots `K r, …, K (r + n + 2)` of a rational knot
sequence `K` (ghost knots included).

On a cell `[a, b]` without knots in its interior every raw spline is a polynomial, its cell
piece (`TensorSpline.piece`); on the cell the mode equals its piece, and its derivatives up to
order `n` equal those of the piece, at the two ends as well (`iteratedDeriv_mode_eq`). The
derivatives of the piece are exact rationals in the knots, `jet` (`polynomialJet_piece`):
`∑_t [a < s_t] (n + 2) / d_t (-1)ᵏ (n + 1)ᵏ (s_t - x)^(n + 1 - k)` with the divided-difference
denominators `d_t`, the reflected terms at the reflected cell `[-b, -a]`. `cornerJet` scales the
jet at an end of the cell by `(b - a)ᵏ`, the unit in which the second-order cell recursion does
not depend on the cell size, and `cornerTable` is its floor at scale `2 ^ p`, within `1`
(`abs_cornerTable_sub_lt`). A mode whose terms have all knots on one side of the selecting
point has zero jets (`jet_eq_zero`), which bounds the modes a cell sees.

## Main definitions

* `Term`: one term `c B_r(x)` or `c B_r(-x)` of a modified mode; `mode` is the sum of its terms.
* `piece`: the cell piece of a mode, the polynomial it equals on a cell without interior knots.
* `jet`: the exact rational `k`-th derivative of the cell piece at a point.
* `cornerJet`: the jet at an end of the cell scaled by `(b - a)ᵏ`.
* `cornerTable`: the floor of `2 ^ p` times the scaled corner jet.
* `modeTable`: the integer table entry of a mode, computed from integer knot numerators.

## Main results

* `piece_eval`: on a cell without interior knots a mode equals its cell piece.
* `contDiff_mode`: a mode built from raw B-splines of order `n + 2` is `Cⁿ`.
* `iteratedDeriv_mode_eq`: through order `n` the derivatives of a mode equal those of its cell
  piece on the closed cell, the ends included.
* `polynomialJet_piece`: the derivatives of the cell piece of a mode are the rationals `jet`.
* `jet_eq_zero`: a mode all of whose terms are inactive on a cell has zero jets there.
* `abs_cornerTable_sub_lt`: the integer corner table is within `1` of `2 ^ p` times the scaled
  corner jet.
* `abs_modeTable_sub_le`: the integer table entry of a mode is within `n + 3` units per term of
  `2 ^ p` times its scaled corner jet.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data II: Rigorous Numerics", arXiv:2305.05660v3, (C.4)-(C.12).
  <https://arxiv.org/abs/2305.05660v3>
-/

@[expose] public section

namespace CAS.Numerics.TensorSpline

open _root_.Polynomial CAS.Splines

/-- One term `c B_r(x)`, or `c B_r(-x)` when `reflect` holds, of a modified mode. -/
structure Term where
  /-- The coefficient. -/
  coeff : ℚ
  /-- The index `r` of the raw spline. -/
  index : ℕ
  /-- Whether the raw spline is reflected. -/
  reflect : Bool
  deriving Inhabited

/-- The supporting knots `K r, …, K (r + n + 2)` of the raw spline `r`. -/
noncomputable def knots (n : ℕ) (K : ℕ → ℚ) (r : ℕ) : Fin (n + 3) → ℝ :=
  fun t ↦ (K (r + t) : ℝ)

/-- The raw B-spline of order `n + 2` with index `r`. -/
noncomputable def raw (n : ℕ) (K : ℕ → ℚ) (r : ℕ) : ℝ → ℝ :=
  truncatedPowerBSpline n (knots n K r)

/-- The value of a term. -/
noncomputable def Term.eval (n : ℕ) (K : ℕ → ℚ) (τ : Term) (x : ℝ) : ℝ :=
  (τ.coeff : ℝ) * raw n K τ.index (if τ.reflect then -x else x)

/-- A mode: the sum of its terms. -/
noncomputable def mode (n : ℕ) (K : ℕ → ℚ) (terms : List Term) (x : ℝ) : ℝ :=
  (terms.map fun τ ↦ τ.eval n K x).sum

/-- The cell piece of a term on `[a, b]`: the polynomial branch of the raw spline right of `a`,
or for a reflected term the branch right of `-b` composed with `-X`. -/
noncomputable def Term.piece (n : ℕ) (K : ℕ → ℚ) (τ : Term) (a b : ℝ) : ℝ[X] :=
  C (τ.coeff : ℝ) * if τ.reflect then
    (truncatedPowerCellPolynomial n (knots n K τ.index) (-b)).comp (-X)
  else truncatedPowerCellPolynomial n (knots n K τ.index) a

/-- The cell piece of a mode. -/
noncomputable def piece (n : ℕ) (K : ℕ → ℚ) (terms : List Term) (a b : ℝ) : ℝ[X] :=
  (terms.map fun τ ↦ τ.piece n K a b).sum

/-- No knot of the raw spline `r` lies in the open interval `(a, b)`. -/
def Separated (n : ℕ) (K : ℕ → ℚ) (r : ℕ) (a b : ℝ) : Prop :=
  ∀ t : Fin (n + 3), (K (r + t) : ℝ) ≤ a ∨ b ≤ K (r + t)

/-- No knot of a term lies in the cell `(a, b)`, or in `(-b, -a)` for a reflected term. -/
def Term.Separated (n : ℕ) (K : ℕ → ℚ) (τ : Term) (a b : ℝ) : Prop :=
  if τ.reflect then TensorSpline.Separated n K τ.index (-b) (-a)
  else TensorSpline.Separated n K τ.index a b

/-- On a cell `[a, b]` without knots of the term in its interior, the cell piece of a term evaluates
to the term at every point of `[a, b]`. -/
theorem Term.piece_eval {n : ℕ} {K : ℕ → ℚ} {τ : Term} {a b x : ℝ} (hτ : τ.Separated n K a b)
    (hx : x ∈ Set.Icc a b) : (τ.piece n K a b).eval x = τ.eval n K x := by
  unfold Term.piece Term.eval raw
  unfold Term.Separated at hτ
  cases hr : τ.reflect
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at hτ ⊢
    rw [eval_mul, eval_C, truncatedPowerCellPolynomial_eval n (knots n K τ.index) hτ hx]
  · simp only [hr, ↓reduceIte] at hτ ⊢
    rw [eval_mul, eval_C, eval_comp, eval_neg, eval_X,
      truncatedPowerCellPolynomial_eval n (knots n K τ.index) hτ
        ⟨by linarith [hx.2], by linarith [hx.1]⟩]

/-- On a cell without interior knots a mode equals its cell piece. -/
theorem piece_eval {n : ℕ} {K : ℕ → ℚ} {terms : List Term} {a b x : ℝ}
    (hsep : ∀ τ ∈ terms, τ.Separated n K a b) (hx : x ∈ Set.Icc a b) :
    (piece n K terms a b).eval x = mode n K terms x := by
  unfold piece mode
  induction terms with
  | nil => simp
  | cons τ terms ih =>
    simp only [List.map_cons, List.sum_cons, eval_add]
    rw [Term.piece_eval (hsep τ (by simp)) hx, ih (fun σ hσ ↦ hsep σ (by simp [hσ]))]

/-- A mode built from raw B-splines of order `n + 2` is `Cⁿ`. -/
theorem contDiff_mode (n : ℕ) (K : ℕ → ℚ) (terms : List Term) :
    ContDiff ℝ n (mode n K terms) := by
  unfold mode
  induction terms with
  | nil => simpa using contDiff_const
  | cons τ terms ih =>
    simp only [List.map_cons, List.sum_cons]
    refine ContDiff.add ?_ ih
    unfold Term.eval raw
    refine contDiff_const.mul ?_
    cases τ.reflect
    · exact contDiff_truncatedPowerBSpline n (knots n K τ.index)
    · exact (contDiff_truncatedPowerBSpline n (knots n K τ.index)).comp contDiff_neg

/-- The iterated derivatives of polynomial evaluation are the polynomial jets. -/
theorem iteratedDeriv_eval_eq_polynomialJet (k : ℕ) (p : ℝ[X]) :
    iteratedDeriv k (fun y ↦ p.eval y) = polynomialJet k p := by
  induction k generalizing p with
  | zero => funext y; simp [polynomialJet]
  | succ k ih =>
    rw [iteratedDeriv_succ', show deriv (fun y ↦ p.eval y) = fun y ↦ p.derivative.eval y from
      _root_.funext fun y ↦ Polynomial.deriv (p := p) (x := y), ih]
    funext y
    rw [polynomialJet_succ]

/-- **Derivatives of a mode on a cell.** Through order `n` the derivatives of a mode equal
those of its cell piece on the closed cell, the ends included. -/
theorem iteratedDeriv_mode_eq {n : ℕ} {K : ℕ → ℚ} {terms : List Term} {a b : ℝ} (hab : a < b)
    (hsep : ∀ τ ∈ terms, τ.Separated n K a b) {k : ℕ} (hk : k ≤ n) {x : ℝ}
    (hx : x ∈ Set.Icc a b) :
    iteratedDeriv k (mode n K terms) x = polynomialJet k (piece n K terms a b) x := by
  have h := PDE.Analysis.iteratedDeriv_eqOn_Icc hab
    (PDE.Analysis.contDiff_polynomial_eval (piece n K terms a b) (n := n))
    (contDiff_mode n K terms) (fun y hy ↦ piece_eval hsep hy) hk hx
  rw [← h, iteratedDeriv_eval_eq_polynomialJet]

/-- Increasing knots with `K t₀ ≤ a` and `b ≤ K (t₀ + 1)` leave the open interval `(a, b)`
free of knots, for every raw spline. -/
theorem separated_of_le_of_le {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) {a b : ℝ} {t₀ : ℕ}
    (ha : (K t₀ : ℝ) ≤ a) (hb : b ≤ K (t₀ + 1)) (r : ℕ) : Separated n K r a b := by
  intro t
  rcases Nat.lt_or_ge t₀ (r + t) with h | h
  · right
    exact hb.trans (by exact_mod_cast hK.monotone (by omega : t₀ + 1 ≤ r + t))
  · left
    exact (by exact_mod_cast hK.monotone h : (K (r + t) : ℝ) ≤ K t₀).trans ha

/-- A term is separated from a cell when the cell, or its reflection for a reflected term,
lies between two consecutive knots. -/
theorem Term.separated_of_le_of_le {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) (τ : Term)
    {a b : ℝ} {t₀ t₁ : ℕ} (ha : (K t₀ : ℝ) ≤ a) (hb : b ≤ K (t₀ + 1))
    (hb' : (K t₁ : ℝ) ≤ -b) (ha' : -a ≤ K (t₁ + 1)) : τ.Separated n K a b := by
  unfold Term.Separated
  split_ifs
  · exact TensorSpline.separated_of_le_of_le hK hb' ha' _
  · exact TensorSpline.separated_of_le_of_le hK ha hb _

/-- Increasing knots with `b ≤ K 0` leave `(a, b)` free of knots. -/
theorem separated_of_le_first {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) {a b : ℝ}
    (hb : b ≤ K 0) (r : ℕ) : Separated n K r a b := fun t ↦
  Or.inr (hb.trans (by exact_mod_cast hK.monotone (Nat.zero_le (r + t))))

/-- A term is separated from the cell `[a, b]` when the cell lies between two consecutive knots
and its reflection `[-b, -a]` lies either between two consecutive knots or left of all knots. -/
theorem Term.separated_of_located {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) (τ : Term) {a b : ℝ}
    (hdir : ∃ t₀, (K t₀ : ℝ) ≤ a ∧ b ≤ K (t₀ + 1))
    (hrefl : -a ≤ K 0 ∨ ∃ t₁, (K t₁ : ℝ) ≤ -b ∧ -a ≤ K (t₁ + 1)) : τ.Separated n K a b := by
  unfold Term.Separated
  split_ifs
  · rcases hrefl with h | ⟨t₁, h₁, h₂⟩
    · exact separated_of_le_first hK h _
    · exact TensorSpline.separated_of_le_of_le hK h₁ h₂ _
  · obtain ⟨t₀, h₁, h₂⟩ := hdir
    exact TensorSpline.separated_of_le_of_le hK h₁ h₂ _

/-! ### Exact jets -/

/-- The divided-difference denominator `∏_{u ≠ t} (K (r + t) - K (r + u))`. -/
def denom (n : ℕ) (K : ℕ → ℚ) (r : ℕ) (t : Fin (n + 3)) : ℚ :=
  ∏ u ∈ Finset.univ.erase t, (K (r + t) - K (r + u))

/-- The `k`-th derivative at `x` of the branch of the raw spline `r` right of `a`. -/
def rawJet (n : ℕ) (K : ℕ → ℚ) (r : ℕ) (a : ℚ) (k : ℕ) (x : ℚ) : ℚ :=
  ∑ t : Fin (n + 3), if a < K (r + t) then
    (n + 2 : ℚ) / denom n K r t * ((-1) ^ k * ((n + 1).descFactorial k : ℚ) *
      (K (r + t) - x) ^ (n + 1 - k))
  else 0

/-- The `k`-th derivative at `x` of the cell piece of a term on `[a, b]`. -/
def Term.jet (n : ℕ) (K : ℕ → ℚ) (τ : Term) (a b : ℚ) (k : ℕ) (x : ℚ) : ℚ :=
  τ.coeff * if τ.reflect then (-1) ^ k * rawJet n K τ.index (-b) k (-x)
  else rawJet n K τ.index a k x

/-- The `k`-th derivative at `x` of the cell piece of a mode on `[a, b]`. -/
def jet (n : ℕ) (K : ℕ → ℚ) (terms : List Term) (a b : ℚ) (k : ℕ) (x : ℚ) : ℚ :=
  (terms.map fun τ ↦ τ.jet n K a b k x).sum

/-- The `k`-th derivative of `(s - X)ᵐ` is `(-1)ᵏ m (m - 1) ⋯ (m - k + 1) (s - X)^(m - k)`. -/
theorem iterate_derivative_C_sub_X_pow (m k : ℕ) (s : ℝ) :
    derivative^[k] ((C s - X) ^ m) =
      C ((-1) ^ k * (m.descFactorial k : ℝ)) * (C s - X) ^ (m - k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_pow, derivative_sub,
      derivative_C, derivative_X]
    rcases Nat.lt_or_ge k m with hkm | hkm
    · obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - k - 1, by omega⟩
      rw [Nat.descFactorial_succ, show k + 1 + j - k = j + 1 by omega,
        show k + 1 + j - (k + 1) = j by omega, Nat.add_sub_cancel]
      simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
      push_cast
      ring
    · rw [Nat.sub_eq_zero_of_le hkm,
        (Nat.descFactorial_eq_zero_iff_lt (n := m) (k := k + 1)).mpr (by omega)]
      simp

/-- The `k`-th derivative at a rational `x` of the branch of the raw spline `r` right of `a` is the
rational `rawJet n K r a k x`. -/
theorem polynomialJet_cellPolynomial (n : ℕ) (K : ℕ → ℚ) (r : ℕ) (a : ℚ) (k : ℕ) (x : ℚ) :
    polynomialJet k (truncatedPowerCellPolynomial n (knots n K r) a) x =
      (rawJet n K r a k x : ℝ) := by
  unfold polynomialJet truncatedPowerCellPolynomial rawJet
  rw [iterate_derivative_sum, eval_finsetSum]
  push_cast
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  simp only [knots, Rat.cast_lt]
  split_ifs with h
  · rw [iterate_derivative_C_mul, iterate_derivative_C_sub_X_pow, eval_mul, eval_C, eval_mul,
      eval_C, eval_pow, eval_sub, eval_C, eval_X]
    unfold splineDividedDifferenceDenominator denom
    simp only [knots]
    push_cast
    ring
  · simp

/-- The `k`-th derivative of `p (-X)` is `(-1)ᵏ p⁽ᵏ⁾(-X)`. -/
theorem iterate_derivative_comp_neg_X (p : ℝ[X]) (k : ℕ) :
    derivative^[k] (p.comp (-X)) = C ((-1 : ℝ) ^ k) * (derivative^[k] p).comp (-X) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, derivative_C_mul, derivative_comp, derivative_neg,
      derivative_X, Function.iterate_succ_apply']
    simp only [map_pow, map_neg, map_one]
    ring

/-- The derivatives of the cell piece of a term at a rational point are the rationals `Term.jet`. -/
theorem Term.polynomialJet_piece (n : ℕ) (K : ℕ → ℚ) (τ : Term) (a b : ℚ) (k : ℕ) (x : ℚ) :
    polynomialJet k (τ.piece n K a b) x = (τ.jet n K a b k x : ℝ) := by
  unfold Term.piece Term.jet
  unfold polynomialJet
  rw [iterate_derivative_C_mul, eval_mul, eval_C]
  cases τ.reflect
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have := polynomialJet_cellPolynomial n K τ.index a k x
    unfold polynomialJet at this
    rw [this]
    push_cast
    ring
  · simp only [↓reduceIte]
    rw [iterate_derivative_comp_neg_X, eval_mul, eval_C, eval_comp, eval_neg, eval_X]
    have := polynomialJet_cellPolynomial n K τ.index (-b) k (-x)
    unfold polynomialJet at this
    push_cast at this ⊢
    rw [this]

/-- **Exact jets.** The derivatives of the cell piece of a mode are the rationals `jet`. -/
theorem polynomialJet_piece (n : ℕ) (K : ℕ → ℚ) (terms : List Term) (a b : ℚ) (k : ℕ)
    (x : ℚ) : polynomialJet k (piece n K terms a b) x = (jet n K terms a b k x : ℝ) := by
  unfold piece jet
  induction terms with
  | nil => simp [polynomialJet]
  | cons τ terms ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [polynomialJet_add, Term.polynomialJet_piece, ih]
    push_cast
    rfl

/-- The raw jet vanishes when every knot lies at or left of the selecting point. -/
theorem rawJet_eq_zero_of_le {n : ℕ} {K : ℕ → ℚ} {r : ℕ} {a : ℚ}
    (h : ∀ t : Fin (n + 3), K (r + t) ≤ a) (k : ℕ) (x : ℚ) : rawJet n K r a k x = 0 := by
  unfold rawJet
  exact Finset.sum_eq_zero fun t _ ↦ by
    rw [ite_eq_right_iff.mpr fun h' ↦ absurd h' (not_lt.mpr (h t))]

/-- For a strictly increasing knot sequence the supporting knots of a raw spline are distinct. -/
theorem injective_knots {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) (r : ℕ) :
    Function.Injective (knots n K r) := by
  intro t u htu
  simp only [knots, Rat.cast_inj] at htu
  exact Fin.ext (by have := hK.injective htu; omega)

/-- The raw jet vanishes when every knot lies right of the selecting point: the divided
difference of a polynomial of degree at most `n + 1` is zero. -/
theorem rawJet_eq_zero_of_lt {n : ℕ} {K : ℕ → ℚ} {r : ℕ} {a : ℚ}
    (hK : StrictMono K) (h : ∀ t : Fin (n + 3), a < K (r + t)) (k : ℕ) (x : ℚ) :
    rawJet n K r a k x = 0 := by
  have hzero := sum_splineDividedDifference_pow_eq_zero n (knots n K r) (injective_knots hK r)
    (d := n + 1 - k) (by omega) (x : ℝ)
  have hcast : ((rawJet n K r a k x : ℚ) : ℝ) =
      (n + 2 : ℝ) * ((-1) ^ k * ((n + 1).descFactorial k : ℝ)) *
        ∑ t, (knots n K r t - x) ^ (n + 1 - k) /
          splineDividedDifferenceDenominator (knots n K r) t := by
    unfold rawJet
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [ite_eq_left_iff.mpr fun h' ↦ absurd (by exact_mod_cast h t) h']
    unfold splineDividedDifferenceDenominator denom knots
    push_cast
    ring
  have : ((rawJet n K r a k x : ℚ) : ℝ) = 0 := by rw [hcast, hzero, mul_zero]
  exact_mod_cast this

/-- A term whose raw knots all lie on one side of its selecting point (`a`, or `-b` for a
reflected term) has zero jets. -/
def Term.Inactive (n : ℕ) (K : ℕ → ℚ) (τ : Term) (a b : ℚ) : Prop :=
  let c := if τ.reflect then -b else a
  (∀ t : Fin (n + 3), K (τ.index + t) ≤ c) ∨ ∀ t : Fin (n + 3), c < K (τ.index + t)

/-- For strictly increasing knots an inactive term has zero jets. -/
theorem Term.jet_eq_zero {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) {τ : Term} {a b : ℚ}
    (h : τ.Inactive n K a b) (k : ℕ) (x : ℚ) : τ.jet n K a b k x = 0 := by
  unfold Term.Inactive at h
  unfold Term.jet
  cases hr : τ.reflect
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rcases h with h | h
    · rw [rawJet_eq_zero_of_le h, mul_zero]
    · rw [rawJet_eq_zero_of_lt hK h, mul_zero]
  · simp only [hr, ↓reduceIte] at h ⊢
    rcases h with h | h
    · rw [rawJet_eq_zero_of_le h, mul_zero, mul_zero]
    · rw [rawJet_eq_zero_of_lt hK h, mul_zero, mul_zero]

/-- A mode all of whose terms are inactive on a cell has zero jets there. -/
theorem jet_eq_zero {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) {terms : List Term} {a b : ℚ}
    (h : ∀ τ ∈ terms, τ.Inactive n K a b) (k : ℕ) (x : ℚ) : jet n K terms a b k x = 0 := by
  unfold jet
  induction terms with
  | nil => simp
  | cons τ terms ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Term.jet_eq_zero hK (h τ (by simp)), ih (fun σ hσ ↦ h σ (by simp [hσ])), add_zero]

/-- For strictly increasing knots the branch of the raw spline `r` right of `c` is the zero
polynomial when all its knots lie on one side of `c`. -/
theorem cellPolynomial_eq_zero {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) {r : ℕ} {c : ℚ}
    (h : (∀ t : Fin (n + 3), K (r + t) ≤ c) ∨ ∀ t : Fin (n + 3), c < K (r + t)) :
    truncatedPowerCellPolynomial n (knots n K r) c = 0 := by
  rcases h with h | h
  · exact truncatedPowerCellPolynomial_eq_zero_of_knots_le n _ fun t ↦ by
      simpa [knots] using (Rat.cast_le (K := ℝ)).mpr (h t)
  · exact truncatedPowerCellPolynomial_eq_zero_of_lt_knots n _ (injective_knots hK r) fun t ↦ by
      simpa [knots] using (Rat.cast_lt (K := ℝ)).mpr (h t)

/-- An inactive term has zero cell piece. -/
theorem Term.piece_eq_zero {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) {τ : Term} {a b : ℚ}
    (h : τ.Inactive n K a b) : τ.piece n K a b = 0 := by
  unfold Term.Inactive at h
  unfold Term.piece
  cases hr : τ.reflect
  · simp only [hr, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [cellPolynomial_eq_zero hK h, mul_zero]
  · simp only [hr, ↓reduceIte] at h ⊢
    have h0 := cellPolynomial_eq_zero hK h
    push_cast at h0
    rw [h0, zero_comp, mul_zero]

/-- A mode all of whose terms are inactive on a cell has zero cell piece. -/
theorem piece_eq_zero {n : ℕ} {K : ℕ → ℚ} (hK : StrictMono K) {terms : List Term} {a b : ℚ}
    (h : ∀ τ ∈ terms, τ.Inactive n K a b) : piece n K terms a b = 0 := by
  unfold piece
  induction terms with
  | nil => simp
  | cons τ terms ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Term.piece_eq_zero hK (h τ (by simp)), ih (fun σ hσ ↦ h σ (by simp [hσ])), zero_add]

/-! ### Scaled corner jets and their integer tables -/

/-- The `k`-th derivative of the cell piece at the left (`c = false`) or right (`c = true`)
end of `[a, b]`, multiplied by `(b - a)ᵏ`. -/
def cornerJet (n : ℕ) (K : ℕ → ℚ) (terms : List Term) (a b : ℚ) (k : ℕ) (c : Bool) : ℚ :=
  (b - a) ^ k * jet n K terms a b k (if c then b else a)

/-- The floor of `2 ^ p` times the scaled corner jet. -/
def cornerTable (p n : ℕ) (K : ℕ → ℚ) (terms : List Term) (a b : ℚ) (k : ℕ) (c : Bool) : ℤ :=
  ⌊(2 : ℚ) ^ p * cornerJet n K terms a b k c⌋

/-- The integer corner table is within `1` of `2 ^ p` times the scaled corner jet. -/
theorem abs_cornerTable_sub_lt (p n : ℕ) (K : ℕ → ℚ) (terms : List Term) (a b : ℚ) (k : ℕ)
    (c : Bool) :
    |(cornerTable p n K terms a b k c : ℝ) - 2 ^ p * (cornerJet n K terms a b k c : ℝ)| < 1 := by
  unfold cornerTable
  set v : ℚ := (2 : ℚ) ^ p * cornerJet n K terms a b k c
  have h1 := Int.floor_le v
  have h2 := Int.lt_floor_add_one v
  have hv : (2 : ℝ) ^ p * (cornerJet n K terms a b k c : ℝ) = (v : ℝ) := by
    simp only [v]
    push_cast
    ring
  rw [hv, abs_sub_lt_iff]
  constructor
  · have : ((⌊v⌋ : ℚ) : ℝ) ≤ (v : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  · have : (v : ℝ) < ((⌊v⌋ : ℚ) : ℝ) + 1 := by exact_mod_cast h2
    push_cast at this
    linarith

/-! ### Integer tables from integer knot numerators -/

/-- The knots `N t / D`. -/
def ratKnots (N : ℕ → ℤ) (D : ℕ) : ℕ → ℚ := fun t ↦ (N t : ℚ) / D

/-- The divided-difference denominator of the numerators,
`∏_{u ≠ t} (N (r + t) - N (r + u))`, which is `D ^ (n + 2)` times `denom`. -/
def denomNum (n : ℕ) (N : ℕ → ℤ) (r : ℕ) (t : Fin (n + 3)) : ℤ :=
  ∏ u ∈ Finset.univ.erase t, (N (r + t) - N (r + u))

/-- The floor `⌊a / b⌋` of a quotient of integers, `b ≠ 0`. -/
def floorDiv (a b : ℤ) : ℤ := (a * b.sign) / (b.natAbs : ℤ)

/-- For `b ≠ 0`, `floorDiv a b` is the floor `⌊a / b⌋` of the rational quotient. -/
theorem floorDiv_eq {a b : ℤ} (hb : b ≠ 0) : floorDiv a b = ⌊(a : ℚ) / b⌋ := by
  unfold floorDiv
  rw [← Rat.floor_intCast_div_natCast]
  congr 1
  rcases lt_or_gt_of_ne hb with h | h
  · rw [Int.sign_eq_neg_one_of_neg h, Nat.cast_natAbs, Int.cast_abs,
      abs_of_neg (by exact_mod_cast h)]
    push_cast
    rw [mul_neg_one, neg_div_neg_eq]
  · rw [Int.sign_eq_one_of_pos h, Nat.cast_natAbs, Int.cast_abs,
      abs_of_pos (by exact_mod_cast h)]
    push_cast
    rw [mul_one]

/-- A rational is within `1` of its floor. -/
theorem abs_floor_sub_le_one (v : ℚ) : |((⌊v⌋ : ℤ) : ℚ) - v| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [Int.floor_le v, Int.lt_floor_add_one v]

/-- The integer table entry of one term at scale `2 ^ p` for the cell `[A / D, B / D]`, order
`k` and end `c`: the sum over the knots of the floors of the scaled summands of `Term.jet`, with
the divided-difference denominators `P r t` (`denomNum` when sound). When the first knot lies
right of the selecting point the jet vanishes for increasing knots, and the entry is `0`. -/
def Term.table (p n : ℕ) (N : ℕ → ℤ) (D : ℕ) (P : ℕ → Fin (n + 3) → ℤ) (τ : Term) (A B : ℤ)
    (k : ℕ) (c : Bool) : ℤ :=
  let sel : ℤ := if τ.reflect then -B else A
  let x : ℤ := if τ.reflect then -(if c then B else A) else (if c then B else A)
  let sgn : ℤ := if τ.reflect then (-1) ^ k else 1
  if sel < N τ.index then 0 else
  ∑ t : Fin (n + 3), if sel < N (τ.index + t) then
    floorDiv (2 ^ p * τ.coeff.num * sgn * ((n + 2) * (-1) ^ k * ((n + 1).descFactorial k : ℤ)) *
        (N (τ.index + t) - x) ^ (n + 1 - k) * (B - A) ^ k * D)
      (τ.coeff.den * P τ.index t)
  else 0

/-- The integer table entry of a mode: the sum of the entries of its terms. -/
def modeTable (p n : ℕ) (N : ℕ → ℤ) (D : ℕ) (P : ℕ → Fin (n + 3) → ℤ) (terms : List Term)
    (A B : ℤ) (k : ℕ) (c : Bool) : ℤ :=
  (terms.map fun τ ↦ τ.table p n N D P A B k c).sum

/-- For strictly increasing knot numerators the divided-difference denominator `denomNum` is
nonzero. -/
theorem denomNum_ne_zero {n : ℕ} {N : ℕ → ℤ} (hN : StrictMono N) (r : ℕ) (t : Fin (n + 3)) :
    denomNum n N r t ≠ 0 := by
  unfold denomNum
  rw [Finset.prod_ne_zero_iff]
  intro u hu
  have hut : u ≠ t := Finset.ne_of_mem_erase hu
  have : N (r + t) ≠ N (r + u) := fun h ↦ hut (Fin.ext (by have := hN.injective h; omega))
  exact sub_ne_zero.mpr this

/-- One summand of the scaled term jet as a quotient of integers. -/
theorem summand_eq_div {n p k : ℕ} {N : ℕ → ℤ} {D : ℕ} (hD : 0 < D) (q : ℚ) (sgn : ℤ)
    (r : ℕ) (t : Fin (n + 3)) (A B x : ℤ) (hden : denomNum n N r t ≠ 0) :
    (2 : ℚ) ^ p * ((B : ℚ) / D - (A : ℚ) / D) ^ k * (q * sgn * ((n + 2 : ℚ) /
        denom n (ratKnots N D) r t * ((-1) ^ k * ((n + 1).descFactorial k : ℚ) *
          (ratKnots N D (r + t) - (x : ℚ) / D) ^ (n + 1 - k)))) =
      ((2 ^ p * q.num * sgn * ((n + 2) * (-1) ^ k * ((n + 1).descFactorial k : ℤ)) *
        (N (r + t) - x) ^ (n + 1 - k) * (B - A) ^ k * D : ℤ) : ℚ) /
        ((q.den * denomNum n N r t : ℤ) : ℚ) := by
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hden' : ((denomNum n N r t : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hden
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdenom : denom n (ratKnots N D) r t = (denomNum n N r t : ℚ) / D ^ (n + 2) := by
    unfold denom denomNum ratKnots
    push_cast
    rw [Finset.prod_congr rfl fun u _ ↦ div_sub_div_same _ _ _, Finset.prod_div_distrib,
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, show n + 3 - 1 = n + 2 by omega]
  rw [hdenom]
  conv_lhs => rw [← Rat.num_div_den q]
  unfold ratKnots
  rcases Nat.lt_or_ge (n + 1) k with hk | hk
  · rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hk]
    push_cast
    simp
  · obtain ⟨m, hm⟩ : ∃ m, n + 1 = m + k := ⟨n + 1 - k, by omega⟩
    rw [show n + 1 - k = m by omega]
    push_cast
    rw [show n + 2 = m + k + 1 by omega, div_sub_div_same, div_sub_div_same, div_pow, div_pow]
    field_simp
    ring

/-- **Integer tables.** For knots `N t / D` with `N` strictly increasing and the true
denominators, the integer table entry of a mode is within `(n + 3)` units per term of `2 ^ p`
times its scaled corner jet. -/
theorem abs_modeTable_sub_le {p n : ℕ} {N : ℕ → ℤ} {D : ℕ} (hD : 0 < D) (hN : StrictMono N)
    {P : ℕ → Fin (n + 3) → ℤ} (hP : ∀ r t, P r t = denomNum n N r t) (terms : List Term)
    (A B : ℤ) (k : ℕ) (c : Bool) :
    |(modeTable p n N D P terms A B k c : ℝ) - 2 ^ p *
        (cornerJet n (ratKnots N D) terms ((A : ℚ) / D) ((B : ℚ) / D) k c : ℝ)| ≤
      ((n + 3) * terms.length : ℕ) := by
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  -- the rational statement
  suffices h : |((modeTable p n N D P terms A B k c : ℤ) : ℚ) - 2 ^ p *
      cornerJet n (ratKnots N D) terms ((A : ℚ) / D) ((B : ℚ) / D) k c| ≤
      ((n + 3) * terms.length : ℕ) by
    have := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at this ⊢
    exact this
  have hterm : ∀ τ : Term, |((τ.table p n N D P A B k c : ℤ) : ℚ) -
      2 ^ p * (((B : ℚ) / D - (A : ℚ) / D) ^ k * τ.jet n (ratKnots N D) ((A : ℚ) / D)
        ((B : ℚ) / D) k (if c then (B : ℚ) / D else (A : ℚ) / D))| ≤ (n + 3 : ℕ) := by
    intro τ
    by_cases hg : (if τ.reflect then -B else A) < N τ.index
    · -- every knot lies right of the selecting point: both sides vanish
      have hKm : StrictMono (ratKnots N D) := fun u v huv ↦ by
        unfold ratKnots
        exact div_lt_div_of_pos_right (by exact_mod_cast hN huv) hDq
      have hall : ∀ t : Fin (n + 3), (if τ.reflect then -(B : ℚ) / D else (A : ℚ) / D) <
          ratKnots N D (τ.index + t) := by
        intro t
        have hle : N τ.index ≤ N (τ.index + t) := hN.monotone (by omega)
        unfold ratKnots
        rw [show (if τ.reflect then -(B : ℚ) / D else (A : ℚ) / D) =
          ((if τ.reflect then -B else A : ℤ) : ℚ) / D by split_ifs <;> push_cast <;> ring]
        exact div_lt_div_of_pos_right (by exact_mod_cast hg.trans_le hle) hDq
      have hjet : τ.jet n (ratKnots N D) ((A : ℚ) / D) ((B : ℚ) / D) k
          (if c then (B : ℚ) / D else (A : ℚ) / D) = 0 := by
        unfold Term.jet
        cases hr : τ.reflect
        · simp only [hr, Bool.false_eq_true, ↓reduceIte] at hall ⊢
          rw [rawJet_eq_zero_of_lt hKm hall, mul_zero]
        · simp only [hr, ↓reduceIte] at hall ⊢
          rw [rawJet_eq_zero_of_lt hKm (fun t ↦ by rw [← neg_div]; exact hall t), mul_zero,
            mul_zero]
      unfold Term.table
      simp only
      rw [ite_eq_left hg, hjet]
      simp only [Int.cast_zero, mul_zero, sub_zero, abs_zero]
      positivity
    set x : ℤ := if c then B else A with hx
    have hxq : (if c then (B : ℚ) / D else (A : ℚ) / D) = (x : ℚ) / D := by
      rw [hx]; split_ifs <;> rfl
    rw [hxq]
    have hsum : 2 ^ p * (((B : ℚ) / D - (A : ℚ) / D) ^ k * τ.jet n (ratKnots N D)
        ((A : ℚ) / D) ((B : ℚ) / D) k ((x : ℚ) / D)) =
        ∑ t : Fin (n + 3), if (if τ.reflect then -B else A) < N (τ.index + t) then
          (((2 ^ p * τ.coeff.num * (if τ.reflect then (-1) ^ k else 1) *
            ((n + 2) * (-1) ^ k * ((n + 1).descFactorial k : ℤ)) *
            (N (τ.index + t) - (if τ.reflect then -x else x)) ^ (n + 1 - k) * (B - A) ^ k * D :
              ℤ) : ℚ) / ((τ.coeff.den * denomNum n N τ.index t : ℤ) : ℚ))
        else 0 := by
      unfold Term.jet rawJet
      cases hr : τ.reflect
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        have hsel : ((A : ℚ) / D < ratKnots N D (τ.index + t)) ↔ A < N (τ.index + t) := by
          unfold ratKnots
          rw [div_lt_div_iff_of_pos_right hDq]
          exact_mod_cast Iff.rfl
        by_cases hlt : A < N (τ.index + t)
        · rw [ite_eq_left (hsel.mpr hlt), ite_eq_left hlt,
            ← summand_eq_div hD τ.coeff 1 τ.index t A B x (denomNum_ne_zero hN _ _)]
          push_cast
          ring
        · rw [ite_eq_right (fun h ↦ hlt (hsel.mp h)), ite_eq_right hlt]
          ring
      · simp only [↓reduceIte]
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        have hsel : (-((B : ℚ) / D) < ratKnots N D (τ.index + t)) ↔ -B < N (τ.index + t) := by
          unfold ratKnots
          rw [← neg_div, div_lt_div_iff_of_pos_right hDq]
          exact_mod_cast Iff.rfl
        by_cases hlt : -B < N (τ.index + t)
        · rw [ite_eq_left (hsel.mpr hlt), ite_eq_left hlt,
            ← summand_eq_div hD τ.coeff ((-1) ^ k) τ.index t A B (-x) (denomNum_ne_zero hN _ _)]
          push_cast
          ring
        · rw [ite_eq_right (fun h ↦ hsel.mp h |> hlt), ite_eq_right hlt]
          ring
    rw [hsum]
    unfold Term.table
    simp only
    rw [ite_eq_right hg, Int.cast_sum, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ t : Fin (n + 3), (1 : ℚ) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ ↦ ?_)
          by_cases hsel : (if τ.reflect then -B else A) < N (τ.index + t)
          · rw [ite_eq_left hsel, ite_eq_left hsel, hP, floorDiv_eq (mul_ne_zero
              (by exact_mod_cast τ.coeff.den_ne_zero) (denomNum_ne_zero hN _ _))]
            exact abs_floor_sub_le_one _
          · rw [ite_eq_right hsel, ite_eq_right hsel]
            simp
      _ = (n + 3 : ℕ) := by simp
  have key : ∀ ts : List Term,
      |(((ts.map fun σ ↦ σ.table p n N D P A B k c).sum : ℤ) : ℚ) -
        2 ^ p * (((B : ℚ) / D - (A : ℚ) / D) ^ k * (ts.map fun σ ↦ σ.jet n (ratKnots N D)
          ((A : ℚ) / D) ((B : ℚ) / D) k (if c then (B : ℚ) / D else (A : ℚ) / D)).sum)| ≤
        ((n + 3) * ts.length : ℕ) := by
    intro ts
    induction ts with
    | nil => simp
    | cons τ ts ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have e : ((τ.table p n N D P A B k c + (ts.map fun σ ↦ σ.table p n N D P A B k c).sum :
          ℤ) : ℚ) - 2 ^ p * (((B : ℚ) / D - (A : ℚ) / D) ^ k *
            (τ.jet n (ratKnots N D) ((A : ℚ) / D) ((B : ℚ) / D) k
              (if c then (B : ℚ) / D else (A : ℚ) / D) +
            (ts.map fun σ ↦ σ.jet n (ratKnots N D) ((A : ℚ) / D) ((B : ℚ) / D) k
              (if c then (B : ℚ) / D else (A : ℚ) / D)).sum)) =
          ((((τ.table p n N D P A B k c) : ℤ) : ℚ) - 2 ^ p * (((B : ℚ) / D - (A : ℚ) / D) ^ k *
            τ.jet n (ratKnots N D) ((A : ℚ) / D) ((B : ℚ) / D) k
              (if c then (B : ℚ) / D else (A : ℚ) / D))) +
          ((((ts.map fun σ ↦ σ.table p n N D P A B k c).sum : ℤ) : ℚ) -
            2 ^ p * (((B : ℚ) / D - (A : ℚ) / D) ^ k *
              (ts.map fun σ ↦ σ.jet n (ratKnots N D) ((A : ℚ) / D) ((B : ℚ) / D) k
                (if c then (B : ℚ) / D else (A : ℚ) / D)).sum)) := by
        push_cast
        ring
      rw [e]
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ ((n + 3 : ℕ) : ℚ) + ((n + 3) * ts.length : ℕ) := add_le_add (hterm τ) ih
        _ = ((n + 3) * (ts.length + 1) : ℕ) := by push_cast; ring
  exact key terms

end CAS.Numerics.TensorSpline

