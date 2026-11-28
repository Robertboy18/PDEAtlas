/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.List.GetD
public import Mathlib.LinearAlgebra.Lagrange
public import PDE.Analysis.Complex.NormSq

set_option linter.style.header false

/-!
# Finite sums and products

The lemmas exchange the order of iterated finite sums, split a sum over `Fin n` into its terms, pull
a factor out of a sum and bound a sum term by term. The proofs use `Finset.sum_comm`,
`Finset.sum_congr` and `simp`, with `ring` for the terms.

## Main results

* `PDE.Analysis.mul_norm_sub_sum_mul_sq_eq`: For a real `w`, a complex `f`, a finite set `T` of
  pairs of naturals, `c : ℕ × ℕ → ℂ` and `b : ℕ × ℕ → ℝ`, `w * ‖f - ∑ i ∈ T, c i * (b i : ℂ)‖ ^ 2 =
  w * ‖f‖ ^ 2 - 2 * ∑ i ∈ T, (conj (c i) * ((w : ℂ) * f * (b i : ℂ))).re + ∑ i ∈ T, ∑ i' ∈ T, (c i *
  conj (c i')).re * (w * b i * b i')`.
* `PDE.Analysis.sum_choose_mul_mul_le_eight_mul`: Let `a b : ℕ → ℝ` satisfy `0 ≤ a i ≤ Ma` and
  `0 ≤ b i ≤ Mb` for all `i ≤ 3`. Then for every `j ≤ 3`,
  `∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i) ≤ 8 * (Ma * Mb)`.
* `PDE.Analysis.abs_sum_sum_three_le_nine_mul`: If `f : Fin 3 → Fin 3 → ℝ` satisfies `|f a b| ≤ M`
  for all `a` and `b`, then `|∑ a, ∑ b, f a b| ≤ 9 * M`.
* `PDE.Analysis.add_eq_zero_of_eq_neg_sub`: In an additive commutative group, if `a = -D - P` then
  `a + P + D = 0`.
* `PDE.Analysis.list_sum_map_mul_div_eq_div`: For a list `l`, real-valued functions `w`, `f` and a
  real number `s`, `(l.map (fun p ↦ w p * (f p / s))).sum = (l.map (fun p => w p * f p)).sum / s`.
* `PDE.Analysis.one_div_one_add_sum_inv_le`: Let `f` be a real family with `0 < f j` for every index
  `j`, and let `i` be an element of the finite set `s`. Then `1 / (1 + ∑ j ∈ s, 1 / f j) ≤ f i`.
* `PDE.Analysis.sq_sum_sum_fin_three_mul_le`: Cauchy-Schwarz inequality for
  `f g : Fin 3 → Fin 3 → ℝ`:
  `(∑ l, ∑ j, f l j * g l j) ^ 2 ≤ (∑ l, ∑ j, f l j ^ 2) * ∑ l, ∑ j, g l j ^ 2`.
* `PDE.Analysis.sum_eq_sum_neg_of_neg_mem`: Let `H` be a finite set of integer pairs that is closed
  under negation (`-β ∈ H` for every `β ∈ H`) and let `F : ℤ × ℤ → M` take values in an additive
  commutative monoid `M`. Then `∑ β ∈ H, F β = ∑ β ∈ H, F (-β)`.

There are 101 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Finset Polynomial

namespace PDE.Analysis

/-- Let all indices range over `Fin k`, let `|q i| ≤ cR i`, let
`Bl = B0 + (∑ i, q i * B1 i) + ∑ i, ∑ l ∈ Finset.Ici i, q i * q l * B2 i l` with
`|Pp - Bl| ≤ fD * fA`, and suppose `|oC - ((∑ l, fr l * mC l) - B0)| ≤ cE`,
`|oL i - ((∑ l, fr l * mT i l) - B1 i)| ≤ lE i` for all `i`, and `|oQ i l + B2 i l| ≤ qE i l` for
`i ≤ l`. Then for every `j`,
`|(∑ l, fr l * (mC l + ∑ i, q i * mT i l)) - Pp - sj * q j| ≤ |oC| + cE + (∑ i, (|oL i - (if i = j
then sj else 0)| + lE i) * cR i) + (∑ i, ∑ l ∈ Finset.Ici i, (|oQ i l| + qE i l) * cR i * cR l) +
fD * fA`. The proof splits the left side into its constant, linear and quadratic parts in `q` and
the error `Pp - Bl`, and bounds each part by the triangle inequality. -/
theorem abs_affine_sub_quadratic_le_on_box {k : ℕ} (j : Fin k) (q cR fr mC oL lE B1 : Fin k → ℝ)
    (mT oQ qE B2 : Fin k → Fin k → ℝ) (Pp Bl B0 sj oC cE fD fA : ℝ)
    (hq : ∀ i, |q i| ≤ cR i)
    (hid : Bl = B0 + (∑ i, q i * B1 i) + ∑ i, ∑ l ∈ Finset.Ici i, q i * q l * B2 i l)
    (hE : |Pp - Bl| ≤ fD * fA)
    (hc : |oC - ((∑ l, fr l * mC l) - B0)| ≤ cE)
    (hlin : ∀ i, |oL i - ((∑ l, fr l * mT i l) - B1 i)| ≤ lE i)
    (hquad : ∀ i l, i ≤ l → |oQ i l + B2 i l| ≤ qE i l) :
    |(∑ l, fr l * (mC l + ∑ i, q i * mT i l)) - Pp - sj * q j| ≤
      |oC| + cE + (∑ i, (|oL i - (if i = j then sj else 0)| + lE i) * cR i)
        + (∑ i, ∑ l ∈ Finset.Ici i, (|oQ i l| + qE i l) * cR i * cR l) + fD * fA := by
  have hcR : ∀ i, 0 ≤ cR i := fun i ↦ (abs_nonneg _).trans (hq i)
  have h1 : (∑ l, fr l * (mC l + ∑ i, q i * mT i l)) =
      (∑ l, fr l * mC l) + ∑ i, q i * ∑ l, fr l * mT i l := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  have h2 : (∑ i, q i * (if i = j then sj else 0)) = sj * q j := by
    rw [Finset.sum_eq_single j (fun b _ hb ↦ by rw [ite_eq_right hb, mul_zero])
      (fun h ↦ absurd (Finset.mem_univ j) h), ite_eq_left rfl, mul_comm]
  have h3 : (∑ i, q i * (((∑ l, fr l * mT i l) - B1 i) - (if i = j then sj else 0))) =
      (∑ i, q i * ∑ l, fr l * mT i l) - (∑ i, q i * B1 i) - ∑ i, q i * (if i = j then sj else 0) :=
          by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have b0 : |(∑ l, fr l * mC l) - B0| ≤ |oC| + cE := by
    have h := abs_le.mp hc
    have h' := abs_le.mp (le_refl |oC|)
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [neg_abs_le oC, le_abs_self oC]
  have b1 : |∑ i, q i * (((∑ l, fr l * mT i l) - B1 i) - (if i = j then sj else 0))| ≤
      ∑ i, (|oL i - (if i = j then sj else 0)| + lE i) * cR i := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    have hl := abs_le.mp (hlin i)
    have hd : |((∑ l, fr l * mT i l) - B1 i) - (if i = j then sj else 0)| ≤
        |oL i - (if i = j then sj else 0)| + lE i := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;>
        linarith [neg_abs_le (oL i - (if i = j then sj else 0)),
          le_abs_self (oL i - (if i = j then sj else 0))]
    rw [abs_mul, mul_comm (|oL i - (if i = j then sj else 0)| + lE i)]
    exact mul_le_mul (hq i) hd (abs_nonneg _) (hcR i)
  have b2 : |∑ i, ∑ l ∈ Finset.Ici i, q i * q l * B2 i l| ≤
      ∑ i, ∑ l ∈ Finset.Ici i, (|oQ i l| + qE i l) * cR i * cR l := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l hl ↦ ?_)
    have hil : i ≤ l := Finset.mem_Ici.mp hl
    have hh := abs_le.mp (hquad i l hil)
    have hd : |B2 i l| ≤ |oQ i l| + qE i l := by
      refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [neg_abs_le (oQ i l), le_abs_self (oQ i l)]
    rw [abs_mul, abs_mul]
    calc |q i| * |q l| * |B2 i l| ≤ cR i * cR l * (|oQ i l| + qE i l) :=
          mul_le_mul (mul_le_mul (hq i) (hq l) (abs_nonneg _) (hcR i)) hd (abs_nonneg _)
            (mul_nonneg (hcR i) (hcR l))
      _ = (|oQ i l| + qE i l) * cR i * cR l := by ring
  have key : (∑ l, fr l * (mC l + ∑ i, q i * mT i l)) - Pp - sj * q j =
      ((∑ l, fr l * mC l) - B0)
        + (∑ i, q i * (((∑ l, fr l * mT i l) - B1 i) - (if i = j then sj else 0)))
        - (∑ i, ∑ l ∈ Finset.Ici i, q i * q l * B2 i l) - (Pp - Bl) := by
    rw [h1, h3, h2, hid]
    ring
  rw [key]
  have a0 := abs_le.mp b0
  have a1 := abs_le.mp b1
  have a2 := abs_le.mp b2
  have aE := abs_le.mp hE
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For real families `F M K` on a finite type, if `|(∑ i, F i * M i - P - G) - x| ≤ O`,
`|∑ l, F l * K l + P + G| ≤ B` and `B + O ≤ R`, then `|∑ i, F i * (M i + K i) - x| ≤ R`. The two
quantities inside the absolute values add up to `∑ i, F i * (M i + K i) - x`. -/
theorem abs_sum_mul_add_sub_le {ι : Type*} [Fintype ι] (F M K : ι → ℝ) (x P G O B R : ℝ)
    (hoff : |(∑ i, F i * M i - P - G) - x| ≤ O) (hen : |∑ l, F l * K l + P + G| ≤ B)
    (hinc : B + O ≤ R) : |∑ i, F i * (M i + K i) - x| ≤ R := by
  have h : ∑ i, F i * (M i + K i) - x =
      ((∑ i, F i * M i - P - G) - x) + (∑ l, F l * K l + P + G) := by
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  rw [h]
  exact le_trans (abs_add_le _ _) (by linarith)

/-- Cauchy-Schwarz inequality for real families `f`, `g` indexed by `Fin k`:
`|∑ j, f j * g j| ≤ √(∑ j, f j ^ 2) * √(∑ j, g j ^ 2)`. -/
theorem abs_sum_mul_le_sqrt_mul_sqrt {k : ℕ} (f g : Fin k → ℝ) :
    |∑ j, f j * g j| ≤ Real.sqrt (∑ j, f j ^ 2) * Real.sqrt (∑ j, g j ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ ↦ sq_nonneg (f j))]
  exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

/-- For `w a : Fin 12 → ℝ` with all `a j` nonnegative, `|∑ j, w j * a j| ≤ (∑ j, |w j|) * ∑ j, a j`.
-/
theorem abs_sum_mul_le_sum_abs_mul (w a : Fin 12 → ℝ) (ha : ∀ j, 0 ≤ a j) :
    |∑ j, w j * a j| ≤ (∑ j, |w j|) * ∑ j, a j := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun j _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (ha j)]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ ↦ ha i) (Finset.mem_univ j))
      (abs_nonneg _)

/-- If `f : Fin 3 → Fin 3 → ℝ` satisfies `|f a b| ≤ M` for all `a` and `b`, then
`|∑ a, ∑ b, f a b| ≤ 9 * M`. The proof applies the triangle inequality to both sums and counts the
nine terms. -/
theorem abs_sum_sum_three_le_nine_mul (f : Fin 3 → Fin 3 → ℝ) (M : ℝ) (h : ∀ a b, |f a b| ≤ M) :
    |∑ a : Fin 3, ∑ b : Fin 3, f a b| ≤ 9 * M := by
  calc |∑ a : Fin 3, ∑ b : Fin 3, f a b| ≤ ∑ a : Fin 3, |∑ b : Fin 3, f a b| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, |f a b| :=
        Finset.sum_le_sum (fun a _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, M :=
        Finset.sum_le_sum (fun a _ ↦ Finset.sum_le_sum (fun b _ ↦ h a b))
    _ = 9 * M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- For real numbers with `a = a'`, `b = b'`, `c = c'` and `d = d'`,
`a + b + c + d = c' + d' + a' + b'`. -/
theorem add_add_add_eq_swap_of_eq {a b c d a' b' c' d' : ℝ} (h1 : a = a') (h2 : b = b')
    (h3 : c = c') (h4 : d = d') :
    a + b + c + d = c' + d' + a' + b' := by
  subst h1 h2 h3 h4
  ring

/-- In an additive commutative group, if `a = -D - P` then `a + P + D = 0`. -/
theorem add_eq_zero_of_eq_neg_sub {E : Type*} [AddCommGroup E] {a D P : E} (h : a = -D - P) :
    a + P + D = 0 := by
  rw [h]
  abel

/-- In an additive commutative group, if `D + Fv + A = -G` then
`D + -Fg + c + (Fv + Fg) + A = -(G - c)`. -/
theorem add_neg_add_add_eq_neg_sub {W : Type*} [AddCommGroup W] (D Fv Fg c A G : W)
    (m : D + Fv + A = -G) :
    D + -Fg + c + (Fv + Fg) + A = -(G - c) := by
  rw [show D + -Fg + c + (Fv + Fg) + A = (D + Fv + A) + c by abel, m]
  abel

/-- In an additive commutative group, if `D + Fv = L - G` then
`D + -Fg + c + (Fv + Fg) = L - (G - c)`. -/
theorem add_neg_add_add_eq_sub_sub {W : Type*} [AddCommGroup W] (D Fv Fg c L G : W)
    (m : D + Fv = L - G) :
    D + -Fg + c + (Fv + Fg) = L - (G - c) := by
  rw [show D + -Fg + c + (Fv + Fg) = (D + Fv) + c by abel, m]
  abel

/-- For a real polynomial `p`, substituting `-X` multiplies the coefficient of degree `s` by
`(-1) ^ s`: `(p.comp (-Polynomial.X)).coeff s = (-1) ^ s * p.coeff s`. The proof is by induction on
`p`, reducing to monomials. -/
theorem coeff_comp_neg_X_real (p : Polynomial ℝ) (s : ℕ) :
    (p.comp (-Polynomial.X)).coeff s = (-1) ^ s * p.coeff s := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add,
      mul_add]
  | monomial n a =>
    have hX : (-Polynomial.X : Polynomial ℝ) ^ n = Polynomial.C ((-1) ^ n) * Polynomial.X ^ n := by
      rw [neg_pow, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_1]
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.X_pow_comp, hX,
      ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow]
    split_ifs with h
    · subst h
      ring
    · simp

/-- Let `v : Fin (D + 1) → ℝ` be injective with `tb ≤ v k` and `v k < 1` for all `k`, and let
`g : ℝ → ℝ → ℂ` be such that for every `x` there is a polynomial `r : ℂ[X]` with `r.natDegree ≤ D`
and `g t x = (t - 1) ^ z * r.eval t` for all `t ≥ tb`. Then for all `x` and all `t ≥ tb`,
`g t x = (t - 1) ^ z * ∑ k, (Lagrange.basis Finset.univ (fun k ↦ (v k : ℂ)) k).eval t * (g (v k) x
/ (v k - 1) ^
z)`, with real numbers coerced to `ℂ`. The polynomial `r` equals its Lagrange interpolant at the
`D + 1` nodes, and `r.eval (v k) = g (v k) x / (v k - 1) ^ z` because `v k ≠ 1`. -/
theorem eq_pow_mul_sum_lagrange_basis_eval {g : ℝ → ℝ → ℂ} {tb : ℝ} {z D : ℕ} {v : Fin (D + 1) → ℝ}
    (hinj : Function.Injective v)
    (hv : ∀ k, tb ≤ v k ∧ v k < 1)
    (hg : ∀ x, ∃ r : ℂ[X], r.natDegree ≤ D ∧ ∀ t, tb ≤ t → g t x = ((t : ℂ) - 1) ^ z *
        r.eval (t : ℂ))
    (t x : ℝ) (ht : tb ≤ t) :
    g t x = ((t : ℂ) - 1) ^ z * ∑ k, (Lagrange.basis Finset.univ (fun k ↦ (v k : ℂ)) k).eval
        (t : ℂ) *
      (g (v k) x / (((v k : ℝ) : ℂ) - 1) ^ z) := by
  obtain ⟨r, hr, hre⟩ := hg x
  have hinjC : Set.InjOn (fun k ↦ (v k : ℂ)) (Finset.univ : Finset (Fin (D + 1))) :=
    fun a _ b _ h ↦ hinj (Complex.ofReal_injective h)
  have hdeg : r.degree < (Finset.univ : Finset (Fin (D + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hr)
  have e := congrArg (Polynomial.eval (t : ℂ)) (Lagrange.eq_interpolate hinjC hdeg)
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at e
  rw [hre t ht, e]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk1 : ((v k : ℝ) : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast (hv k).2.ne
  rw [hre (v k) (hv k).1, mul_div_cancel_left₀ _ (pow_ne_zero _ hk1), Polynomial.eval_mul,
      Polynomial.eval_C,
    mul_comm]

/-- Let `J : ℝ → ℝ → ℂ` satisfy `J a b = J a m + J m b` whenever `lo ≤ a ≤ m ≤ b`, and let
`tlo thi : Fin N → ℝ` with `0 < N` and `tlo j < thi j` describe consecutive intervals:
`thi j = tlo j'` when `j' = j + 1`, the first starts at `lo` and the last ends at `hi`. Then
`J lo hi = ∑ j, J (tlo j) (thi j)` and `lo ≤ tlo j` for every `j`. The proof builds the sequence of
break points and argues by induction on the number of intervals. -/
theorem eq_sum_fin_of_additive_of_adjacent (J : ℝ → ℝ → ℂ) {lo hi : ℝ}
    (hadd : ∀ a m b, lo ≤ a → a ≤ m → m ≤ b → J a b = J a m + J m b)
    {N : ℕ} (tlo thi : Fin N → ℝ) (hN : 0 < N) (hlt : ∀ j, tlo j < thi j)
    (hadj : ∀ j j' : Fin N, j.val + 1 = j'.val → thi j = tlo j')
    (hfirst : ∀ j : Fin N, j.val = 0 → tlo j = lo) (hlast : ∀ j : Fin N,
        j.val + 1 = N → thi j = hi) :
    J lo hi = ∑ j, J (tlo j) (thi j) ∧ ∀ j, lo ≤ tlo j := by
  set x : ℕ → ℝ := fun i ↦ if h : i < N then tlo ⟨i, h⟩ else hi with hx
  have hx0 : x 0 = lo := by
    simp only [hx, dite_eq_left hN]
    exact hfirst _ rfl
  have hxt : ∀ i (h : i < N), tlo ⟨i, h⟩ = x i := by
    intro i h
    simp only [hx, dite_eq_left h]
  have hxs : ∀ i (h : i < N), thi ⟨i, h⟩ = x (i + 1) := by
    intro i h
    by_cases h' : i + 1 < N
    · simp only [hx, dite_eq_left h']
      exact hadj _ _ rfl
    · have e : i + 1 = N := by omega
      simp only [hx, dite_eq_right h']
      exact hlast _ e
  have key : ∀ m, m ≤ N → lo ≤ x m ∧ J lo (x m) = ∑ i ∈ Finset.range m, J (x i) (x (i + 1)) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨hx0.ge, ?_⟩
      rw [hx0, Finset.sum_range_zero]
      have h := hadd lo lo lo le_rfl le_rfl le_rfl
      linear_combination -h
    | succ m ih =>
      intro hm
      obtain ⟨h1, h2⟩ := ih (by omega)
      have hlt' : x m < x (m + 1) := by
        rw [← hxt m (by omega), ← hxs m (by omega)]
        exact hlt _
      refine ⟨h1.trans hlt'.le, ?_⟩
      rw [Finset.sum_range_succ, ← h2]
      exact hadd _ _ _ le_rfl h1 hlt'.le
  have hxn : x N = hi := by simp [hx]
  refine ⟨?_, fun j ↦ ?_⟩
  · rw [← hxn, (key N le_rfl).2, ← Fin.sum_univ_eq_sum_range (fun i ↦ J (x i) (x (i + 1)))]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [← hxt j.val j.isLt, ← hxs j.val j.isLt]
  · have h := (key j.val j.isLt.le).1
    rwa [← hxt j.val j.isLt] at h

/-- Lagrange interpolation at `K` distinct real nodes: if `T : Fin K → ℝ` is injective and the real
polynomial `p` has `p.degree < K`, then
`p.eval t = ∑ j, p.eval (T j) * (Lagrange.basis Finset.univ T j).eval t` for every real `t`. -/
theorem eval_eq_sum_eval_mul_lagrange_basis (K : ℕ) (T : Fin K → ℝ) (hT : Function.Injective T)
    (p : Polynomial ℝ)
    (hp : p.degree < K) (t : ℝ) :
    p.eval t = ∑ j, p.eval (T j) * (Lagrange.basis Finset.univ T j).eval t := by
  have h := Lagrange.eq_interpolate (s := Finset.univ) (v := T) (f := p) (hT.injOn) (by
    simpa using hp)
  conv_lhs => rw [h]
  simp [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, mul_comm]

/-- A real polynomial `gp` with `gp.eval 0 = 1` has the form `1 + t * gq`: there is a real
polynomial `gq` with `gp.eval t = 1 + t * gq.eval t` for all real `t`. The proof shows that `X`
divides `gp - 1`, whose constant coefficient vanishes. -/
theorem exists_eval_eq_one_add_mul_eval (gp : Polynomial ℝ) (h : gp.eval 0 = 1) :
    ∃ gq : Polynomial ℝ, ∀ t, gp.eval t = 1 + t * gq.eval t := by
  have hd : Polynomial.X ∣ gp - Polynomial.C 1 := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_C_zero,
        Polynomial.coeff_zero_eq_eval_zero, h,
      sub_self]
  obtain ⟨gq, hgq⟩ := hd
  refine ⟨gq, fun t ↦ ?_⟩
  have := congrArg (Polynomial.eval t) hgq
  simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X] at this
  linarith

/-- If `a : ℕ → ℕ → ℝ` satisfies `a j j ≠ 0` for every `j`, then for each `i ≤ Q` there are
coefficients `d : ℕ → ℝ` such that
`r ^ i = ∑ j ∈ Finset.range (Q + 1), d j * ∑ t ∈ Finset.range (j + 1), a j t * r ^
t` for all real `r`. So every power up to `Q` is a combination of the first `Q +
1` polynomials of a triangular family with nonzero diagonal. The proof is by strong induction on
`i`, solving the `i`-th polynomial for `r ^ i`. -/
theorem exists_pow_eq_sum_triangular (a : ℕ → ℕ → ℝ) (ha : ∀ j, a j j ≠ 0) (Q : ℕ) :
    ∀ i, i ≤ Q → ∃ d : ℕ → ℝ, ∀ r : ℝ,
      r ^ i = ∑ j ∈ Finset.range (Q + 1), d j * ∑ t ∈ Finset.range (j + 1), a j t * r ^ t := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hlt : ∀ t, t < i → ∃ d : ℕ → ℝ, ∀ r : ℝ,
      r ^ t = ∑ j ∈ Finset.range (Q + 1), d j * ∑ s ∈ Finset.range (j + 1), a j s * r ^ s :=
    fun t ht ↦ ih t ht (by omega)
  choose! D hD using hlt
  refine ⟨fun j ↦ ((if j = i then 1 else 0) - ∑ t ∈ Finset.range i, a i t * D t j) / a i i, ?_⟩
  intro r
  set P : ℕ → ℝ := fun j ↦ ∑ t ∈ Finset.range (j + 1), a j t * r ^ t with hP
  have h1 : ∑ j ∈ Finset.range (Q + 1), (if j = i then (1 : ℝ) else 0) * P j = P i := by
    simp [Finset.mem_range, show i < Q + 1 by omega]
  have h2 : ∑ j ∈ Finset.range (Q + 1), (∑ t ∈ Finset.range i, a i t * D t j) * P j =
      ∑ t ∈ Finset.range i, a i t * r ^ t := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [hD t (Finset.mem_range.1 ht) r]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have h3 : P i = ∑ t ∈ Finset.range i, a i t * r ^ t + a i i * r ^ i := by
    simp only [hP]; rw [Finset.sum_range_succ]
  have h4 : ∑ j ∈ Finset.range (Q + 1),
      ((if j = i then (1 : ℝ) else 0) - ∑ t ∈ Finset.range i, a i t * D t j) / a i i * P j =
      (∑ j ∈ Finset.range (Q + 1), (if j = i then (1 : ℝ) else 0) * P j
        - ∑ j ∈ Finset.range (Q + 1), (∑ t ∈ Finset.range i, a i t * D t j) * P j) / a i i := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  change r ^ i = ∑ j ∈ Finset.range (Q + 1),
      ((if j = i then (1 : ℝ) else 0) - ∑ t ∈ Finset.range i, a i t * D t j) / a i i * P j
  rw [h4, h1, h2, h3]
  field_simp [ha i]
  ring

/-- If `C : ℕ → ℕ → ℝ` satisfies `0 < C j j` for every `j`, then for each `j ≤ d` there are
coefficients `a : ℕ → ℝ` such that
`r ^ j = ∑ i ∈ range (d + 1), a i * ∑ t ∈ range (i + 1), C i t * r ^ t` for all real `r`. The proof
shows by strong induction on `j` that `fun r ↦ r ^ j` lies in the span of the first `d + 1`
triangular sums. -/
theorem exists_pow_eq_sum_triangular_of_pos (C : ℕ → ℕ → ℝ) (hC : ∀ j, 0 < C j j) (d : ℕ) :
    ∀ j ≤ d, ∃ a : ℕ → ℝ, ∀ r : ℝ, r ^ j =
      ∑ i ∈ range (d + 1), a i * ∑ t ∈ range (i + 1), C i t * r ^ t := by
  let P : Fin (d + 1) → ℝ → ℝ := fun i r ↦ ∑ t ∈ range ((i : ℕ) + 1), C i t * r ^ t
  have key : ∀ j, j ≤ d → (fun r : ℝ ↦ r ^ j) ∈ Submodule.span ℝ (Set.range P) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hPj : P ⟨j, by omega⟩ ∈ Submodule.span ℝ (Set.range P) := Submodule.subset_span ⟨_, rfl⟩
      have heq : (fun r : ℝ ↦ r ^ j)
          = (C j j)⁻¹ • (P ⟨j, by omega⟩ - ∑ t ∈ range j, C j t • (fun r : ℝ ↦ r ^ t)) := by
        funext r
        have hne := (hC j).ne'
        simp only [P, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul,
            Finset.sum_range_succ]
        field_simp
        ring
      rw [heq]
      refine Submodule.smul_mem _ _ (Submodule.sub_mem _ hPj (Submodule.sum_mem _ fun t ht ↦
        Submodule.smul_mem _ _ (ih t (Finset.mem_range.1 ht) ?_)))
      have := Finset.mem_range.1 ht
      omega
  intro j hj
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (key j hj)
  refine ⟨fun i ↦ if h : i < d + 1 then c ⟨i, h⟩ else 0, fun r ↦ ?_⟩
  have h1 := congrFun hc r
  rw [← h1, Finset.sum_apply, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [P, i.isLt]

/-- For `k : Fin 2`, a natural `o`, a finite set `s` and polynomials `f x : MvPolynomial (Fin 2) ℂ`,
the `o`-fold iterate of `MvPolynomial.pderiv k` applied to `∑ x ∈ s, f x` equals
`∑ x ∈ s, (MvPolynomial.pderiv k)^[o] (f x)`. -/
theorem iterate_pderiv_sum (k : Fin 2) (o : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial (Fin 2) ℂ) :
    (MvPolynomial.pderiv k)^[o] (∑ x ∈ s, f x) = ∑ x ∈ s, (MvPolynomial.pderiv k)^[o] (f x) := by
  induction o with
  | zero => rfl
  | succ o ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    simp only [Function.iterate_succ_apply']

/-- Let `f : ℕ → ℕ → ℝ` be nonnegative. If `i < m` and `j < n`, then
`f i j ≤ ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f i j`. -/
theorem le_sum_range_sum_range_of_nonneg (f : ℕ → ℕ → ℝ) (hf : ∀ i j, 0 ≤ f i j) {m n i j : ℕ}
    (hi : i < m) (hj : j < n) :
    f i j ≤ ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, f i j := by
  calc f i j ≤ ∑ j ∈ Finset.range n, f i j :=
        Finset.single_le_sum (fun k _ ↦ hf i k) (Finset.mem_range.2 hj)
    _ ≤ _ := Finset.single_le_sum (f := fun i ↦ ∑ j ∈ Finset.range n, f i j)
        (fun k _ ↦ Finset.sum_nonneg fun _ _ ↦ hf k _) (Finset.mem_range.2 hi)

/-- Let `l` be a list and `f`, `g`, `h` real-valued functions with `f e = a * g e + b * h e` for
every `e ∈ l`. Then `(l.map f).sum = a * (l.map g).sum + b * (l.map h).sum`. The proof is by
induction on the list. -/
theorem list_sum_map_eq_mul_add_mul {ι : Type} (l : List ι) (f g h : ι → ℝ) (a b : ℝ)
    (hf : ∀ e ∈ l, f e = a * g e + b * h e) :
    (l.map f).sum = a * (l.map g).sum + b * (l.map h).sum := by
  induction l with
  | nil => simp
  | cons e t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hf e (by simp), ih (fun e' he' ↦ hf e' (by simp [he']))]
    ring

/-- For a list `l`, real-valued functions `w`, `f` and a real number `s`,
`(l.map (fun p ↦ w p * (f p / s))).sum = (l.map (fun p ↦ w p * f p)).sum / s`. -/
theorem list_sum_map_mul_div_eq_div {β : Type*} (l : List β) (w f : β → ℝ) (s : ℝ) :
    (l.map (fun p ↦ w p * (f p / s))).sum = (l.map (fun p ↦ w p * f p)).sum / s := by
  induction l with
  | nil => simp
  | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Let `J : (ℝ → ℝ) → ℂ` satisfy `J (fun s ↦ f s + g s) = J f + J g` for continuous `f`, `g` and
`J (fun s ↦ w * f s) = (w : ℂ) * J f` for all real `w` and all `f`. For reals `e i` and continuous
functions `g i : ℝ → ℝ`,
`J (fun s ↦ ∑ i ∈ Finset.range (D + 1), e i * g i s) = ∑ i ∈ Finset.range (D + 1), (e i : ℂ) * J (g
i)`. Proof idea: induction on `D`. -/
theorem map_sum_range_of_additive_on_continuous (J : (ℝ → ℝ) → ℂ)
    (hlin : ∀ f g, Continuous f → Continuous g → J (fun s ↦ f s + g s) = J f + J g)
    (hsmul : ∀ (w : ℝ) f, J (fun s ↦ w * f s) = (w : ℂ) * J f)
    (e : ℕ → ℝ) (g : ℕ → ℝ → ℝ) (hg : ∀ i, Continuous (g i)) (D : ℕ) :
    J (fun s ↦ ∑ i ∈ Finset.range (D + 1), e i * g i s) = ∑ i ∈ Finset.range (D + 1),
        (e i : ℂ) * J (g i) := by
  induction D with
  | zero => simp only [zero_add, Finset.sum_range_one]; exact hsmul _ _
  | succ D ih =>
    have h1 : (fun s ↦ ∑ i ∈ Finset.range (D + 1 + 1), e i * g i s) =
        fun s ↦ (fun s ↦ ∑ i ∈ Finset.range (D + 1), e i * g i s) s +
            (fun s ↦ e (D + 1) * g (D + 1) s) s :=
      funext fun s ↦ Finset.sum_range_succ _ _
    have hc1 : Continuous (fun s ↦ ∑ i ∈ Finset.range (D + 1), e i * g i s) :=
      continuous_finsetSum _ (fun i _ ↦ continuous_const.mul (hg i))
    have hc2 : Continuous (fun s ↦ e (D + 1) * g (D + 1) s) := continuous_const.mul (hg _)
    rw [h1, hlin _ _ hc1 hc2, ih, hsmul]
    exact (Finset.sum_range_succ (fun i ↦ (e i : ℂ) * J (g i)) (D + 1)).symm

/-- For real numbers with `r ≠ 0`, `p * q * s = p * r * (q / r) * s`. -/
theorem mul_mul_eq_mul_mul_div_mul (p q s r : ℝ) (hr : r ≠ 0) : p * q * s = p * r * (q / r) * s :=
    by
  have h : r * (q / r) = q := by field_simp
  rw [mul_assoc p r, h]

/-- If `g : Fin 3 → ℂ` satisfies `‖g i‖ ≤ M` for all `i`, then `‖∑ i, g i‖ ≤ 3 * M`. -/
theorem norm_sum_fin_three_le {g : Fin 3 → ℂ} {M : ℝ} (h : ∀ i, ‖g i‖ ≤ M) : ‖∑ i, g i‖ ≤ 3 * M :=
    by
  refine (norm_sum_le _ _).trans ?_
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

/-- Cauchy-Schwarz inequality for a finite sum with real coefficients: for a finite set `s`,
`κ : n → ℝ` and `d : n → ℂ`,
`‖∑ l ∈ s, (κ l : ℂ) * d l‖ ^ 2 ≤ (∑ l ∈ s, κ l ^ 2) * ∑ l ∈ s, ‖d l‖ ^ 2`. -/
theorem norm_sum_ofReal_mul_sq_le {n : Type*} (s : Finset n) (κ : n → ℝ) (d : n → ℂ) :
    ‖∑ l ∈ s, (κ l : ℂ) * d l‖ ^ 2 ≤ (∑ l ∈ s, κ l ^ 2) * ∑ l ∈ s, ‖d l‖ ^ 2 := by
  have h1 : ‖∑ l ∈ s, (κ l : ℂ) * d l‖ ≤ ∑ l ∈ s, |κ l| * ‖d l‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun l _ ↦ ?_))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun l ↦ |κ l|) (fun l ↦ ‖d l‖)
  have h3 : ∑ l ∈ s, |κ l| ^ 2 = ∑ l ∈ s, κ l ^ 2 := Finset.sum_congr rfl fun l _ ↦ sq_abs _
  rw [h3] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- For a finite set `T`, `μ : ι → ℝ` and `c : ι → ℂ`,
`‖∑ a ∈ T, (μ a : ℂ) * c a‖ ^ 2 ≤ T.card * ∑ a ∈ T, μ a ^ 2 * ‖c a‖ ^ 2`. The proof uses the
triangle inequality and the bound of the square of a sum by the cardinality times the sum of the
squares. -/
theorem norm_sum_ofReal_mul_sq_le_card {ι : Type*} (T : Finset ι) (μ : ι → ℝ) (c : ι → ℂ) :
    ‖∑ a ∈ T, ((μ a : ℝ) : ℂ) * c a‖ ^ 2 ≤ T.card * ∑ a ∈ T, μ a ^ 2 * ‖c a‖ ^ 2 := by
  have h1 : ‖∑ a ∈ T, ((μ a : ℝ) : ℂ) * c a‖ ≤ ∑ a ∈ T, |μ a| * ‖c a‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]))
  have h2 := sq_sum_le_card_mul_sum_sq (s := T) (f := fun a ↦ |μ a| * ‖c a‖)
  have h3 : ‖∑ a ∈ T, ((μ a : ℝ) : ℂ) * c a‖ ^ 2 ≤ (∑ a ∈ T, |μ a| * ‖c a‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h3.trans (h2.trans (le_of_eq ?_))
  congr 1
  exact Finset.sum_congr rfl fun a _ ↦ by rw [mul_pow, sq_abs]

/-- Let `f` be a real family with `0 < f j` for every index `j`, and let `i` be an element of the
finite set `s`. Then `1 / (1 + ∑ j ∈ s, 1 / f j) ≤ f i`. -/
theorem one_div_one_add_sum_inv_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 < f i)
    (i : ι) (hi : i ∈ s) :
    1 / (1 + ∑ j ∈ s, 1 / f j) ≤ f i := by
  have h1 : 1 / f i ≤ ∑ j ∈ s, 1 / f j :=
    Finset.single_le_sum (f := fun j ↦ 1 / f j) (fun j _ ↦ (one_div_pos.mpr (hf j)).le) hi
  have h2 : 0 < 1 / f i := one_div_pos.mpr (hf i)
  calc 1 / (1 + ∑ j ∈ s, 1 / f j) ≤ 1 / (1 / f i) := one_div_le_one_div_of_le h2 (by linarith)
    _ = f i := one_div_one_div _

/-- If `c : ℕ → ℕ → ℝ` satisfies `0 < c j j` for every `j`, then each monomial `fun r : ℝ ↦ r ^ a`
lies in the real span of the functions `fun r ↦ ∑ i ∈ Finset.range (j + 1), c j i * r ^ i` for
`j : ℕ`. The proof is by strong induction on `a`: the `a`-th function is solved for `r ^ a`, and the
lower powers already lie in the span. -/
theorem pow_mem_span_triangular_of_diag_pos (c : ℕ → ℕ → ℝ) (hc : ∀ j, 0 < c j j) (a : ℕ) :
    (fun r : ℝ ↦ r ^ a) ∈ Submodule.span ℝ (Set.range (fun j (r : ℝ) ↦ ∑ i ∈
        Finset.range (j + 1), c j i * r ^ i)) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    have e : (fun r : ℝ ↦ r ^ a) = (c a a)⁻¹ • ((fun r : ℝ ↦ ∑ i ∈ Finset.range (a + 1),
        c a i * r ^ i) -
        ∑ i ∈ Finset.range a, c a i • (fun r : ℝ ↦ r ^ i)) := by
      funext r
      have := (hc a).ne'
      simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, Finset.sum_range_succ]
      field_simp
      ring
    rw [e]
    apply Submodule.smul_mem
    apply Submodule.sub_mem
    · exact Submodule.subset_span ⟨a, rfl⟩
    · exact Submodule.sum_mem _ (fun i hi ↦ Submodule.smul_mem _ _ (ih i (Finset.mem_range.mp hi)))

/-- Let `f : ℤ × ℤ → ℝ` be nonnegative everywhere and let `s` be a finite set of integer pairs with
`∑ α ∈ s, f α ≤ c`. Then `f α ≤ c` for every `α ∈ s`. -/
theorem single_le_of_sum_le {s : Finset (ℤ × ℤ)} {f : ℤ × ℤ → ℝ} {c : ℝ} (hf : ∀ α, 0 ≤ f α)
    (hs : ∑ α ∈ s, f α ≤ c) {α : ℤ × ℤ} (hα : α ∈ s) : f α ≤ c :=
  (Finset.single_le_sum (fun β _ ↦ hf β) hα).trans hs

/-- For `a : Fin 3 → ℝ`, `(∑ j, 9 * a j) ^ 2 ≤ 243 * ∑ j, a j ^ 2`. -/
theorem sq_sum_fin_three_nine_mul_le (a : Fin 3 → ℝ) :
    (∑ j : Fin 3, 9 * a j) ^ 2 ≤ 243 * ∑ j : Fin 3, a j ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 1 - a 2), sq_nonneg (a 0 - a 2)]

/-- Weighted Cauchy-Schwarz inequality on a finite set `s` of integer pairs: if `a : ℤ × ℤ → ℝ` is
nonnegative everywhere, then `(∑ α ∈ s, a α * z α) ^ 2 ≤ (∑ α ∈ s, a α) * ∑ α ∈ s, a α * z α ^ 2`
for every `z : ℤ × ℤ → ℝ`. -/
theorem sq_sum_mul_le_sum_mul_sum {s : Finset (ℤ × ℤ)} {a z : ℤ × ℤ → ℝ} (ha : ∀ α, 0 ≤ a α) :
    (∑ α ∈ s, a α * z α) ^ 2 ≤ (∑ α ∈ s, a α) * ∑ α ∈ s, a α * z α ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun α _ ↦ ha α)
    (fun α _ ↦ mul_nonneg (ha α) (sq_nonneg _)) (fun α _ ↦ le_of_eq (by ring))

/-- Cauchy-Schwarz inequality for `f g : Fin 3 → Fin 3 → ℝ`:
`(∑ l, ∑ j, f l j * g l j) ^ 2 ≤ (∑ l, ∑ j, f l j ^ 2) * ∑ l, ∑ j, g l j ^ 2`. -/
theorem sq_sum_sum_fin_three_mul_le (f g : Fin 3 → Fin 3 → ℝ) :
    (∑ l : Fin 3, ∑ j : Fin 3, f l j * g l j) ^ 2
      ≤ (∑ l : Fin 3, ∑ j : Fin 3, f l j ^ 2) * ∑ l : Fin 3, ∑ j : Fin 3, g l j ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3 × Fin 3))
    (fun p ↦ f p.1 p.2) (fun p ↦ g p.1 p.2)
  simpa only [Fintype.sum_prod_type] using h

/-- For `x w : Fin 3 → Fin 3 → ℂ`:
`(∑ a, ∑ b, ‖x a b‖ * ‖w a b‖) ^ 2 ≤ (∑ a, ∑ b, ‖x a b‖ ^ 2) * (∑ a, ∑ b, ‖w a b‖ ^
2)`. This is `sq_sum_sum_fin_three_mul_le` for the norms of the entries. -/
theorem sq_sum_sum_norm_mul_norm_le (x w : Fin 3 → Fin 3 → ℂ) :
    (∑ a : Fin 3, ∑ b : Fin 3, ‖x a b‖ * ‖w a b‖) ^ 2
      ≤ (∑ a : Fin 3, ∑ b : Fin 3, ‖x a b‖ ^ 2) * (∑ a : Fin 3, ∑ b : Fin 3, ‖w a b‖ ^ 2) :=
          sq_sum_sum_fin_three_mul_le (fun a b ↦ ‖x a b‖) (fun a b ↦ ‖w a b‖)

/-- Cauchy-Schwarz inequality for `x y b c : Fin 3 → ℝ`:
`(∑ l, (x l * b l - y l * c l)) ^ 2 ≤ (∑ l, (x l ^ 2 + y l ^ 2)) * ∑ l, (c l ^ 2 + b l ^ 2)`. -/
theorem sq_sum_three_mul_sub_mul_le (x y b c : Fin 3 → ℝ) :
    (∑ l : Fin 3, (x l * b l - y l * c l)) ^ 2 ≤
      (∑ l : Fin 3, (x l ^ 2 + y l ^ 2)) * ∑ l : Fin 3, (c l ^ 2 + b l ^ 2) := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (x 0 * b 1 - x 1 * b 0), sq_nonneg (x 0 * b 2 - x 2 * b 0),
    sq_nonneg (x 1 * b 2 - x 2 * b 1), sq_nonneg (y 0 * c 1 - y 1 * c 0),
    sq_nonneg (y 0 * c 2 - y 2 * c 0), sq_nonneg (y 1 * c 2 - y 2 * c 1),
    sq_nonneg (x 0 * c 0 + y 0 * b 0), sq_nonneg (x 1 * c 1 + y 1 * b 1),
        sq_nonneg (x 2 * c 2 + y 2 * b 2),
    sq_nonneg (x 0 * c 1 + y 1 * b 0), sq_nonneg (x 1 * c 0 + y 0 * b 1),
    sq_nonneg (x 0 * c 2 + y 2 * b 0), sq_nonneg (x 2 * c 0 + y 0 * b 2),
    sq_nonneg (x 1 * c 2 + y 2 * b 1), sq_nonneg (x 2 * c 1 + y 1 * b 2)]

/-- Minkowski inequality for a weighted `ℓ²` seminorm on `Fin m → ℝ`: if all weights `τ a` are
nonnegative, then `√(∑ a, τ a * (p a + q a) ^ 2) ≤ √(∑ a, τ a * p a ^ 2) + √(∑ a, τ a * q a ^ 2)`.
The proof expands the square and bounds the cross term `∑ a, τ a * (p a * q a)` by the
Cauchy-Schwarz inequality. -/
theorem sqrt_sum_mul_add_sq_le {m : ℕ} (τ p q : Fin m → ℝ) (hτ : ∀ a, 0 ≤ τ a) :
    Real.sqrt (∑ a, τ a * (p a + q a) ^ 2)
      ≤ Real.sqrt (∑ a, τ a * p a ^ 2) + Real.sqrt (∑ a, τ a * q a ^ 2) := by
  set A := ∑ a, τ a * p a ^ 2
  set B := ∑ a, τ a * q a ^ 2
  set C := ∑ a, τ a * (p a * q a)
  have hA : 0 ≤ A := Finset.sum_nonneg fun a _ ↦ mul_nonneg (hτ a) (sq_nonneg _)
  have hB : 0 ≤ B := Finset.sum_nonneg fun a _ ↦ mul_nonneg (hτ a) (sq_nonneg _)
  have hexp : ∑ a, τ a * (p a + q a) ^ 2 = A + 2 * C + B := by
    simp only [A, B, C, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  have hcs : C ^ 2 ≤ A * B := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a ↦ Real.sqrt (τ a) * p a)
      (fun a ↦ Real.sqrt (τ a) * q a)
    have e1 : ∀ a, Real.sqrt (τ a) * p a * (Real.sqrt (τ a) * q a) = τ a * (p a * q a) :=
        fun a ↦ by
      have := Real.mul_self_sqrt (hτ a)
      linear_combination (p a * q a) * this
    have e2 : ∀ (a : Fin m) (x : ℝ), (Real.sqrt (τ a) * x) ^ 2 = τ a * x ^ 2 := fun a x ↦ by
      rw [mul_pow, Real.sq_sqrt (hτ a)]
    simp only [e1, e2] at h
    exact h
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  have hC : C ≤ Real.sqrt A * Real.sqrt B := by
    have h0 : 0 ≤ Real.sqrt A * Real.sqrt B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h2 : C ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := by rw [mul_pow, hsA, hsB]; exact hcs
    nlinarith
  rw [hexp]
  calc Real.sqrt (A + 2 * C + B) ≤ Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = Real.sqrt A + Real.sqrt B := Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))

/-- Triangle inequality for a weighted `ℓ²` seminorm on `Fin m → ℝ`: if all weights `τ a` are
nonnegative, then `√(∑ a, τ a * (x a - y a) ^ 2) ≤ √(∑ a, τ a * x a ^ 2) + √(∑ a, τ a * y a ^ 2)`.
The proof expands the square and bounds the cross term by the Cauchy-Schwarz inequality. -/
theorem sqrt_sum_mul_sub_sq_le {m : ℕ} (τ : Fin m → ℝ) (hτ : ∀ a, 0 ≤ τ a) (x y : Fin m → ℝ) :
    Real.sqrt (∑ a, τ a * (x a - y a) ^ 2) ≤
      Real.sqrt (∑ a, τ a * x a ^ 2) + Real.sqrt (∑ a, τ a * y a ^ 2) := by
  have hX : 0 ≤ ∑ a, τ a * x a ^ 2 := Finset.sum_nonneg fun a _ ↦ mul_nonneg (hτ a) (sq_nonneg _)
  have hY : 0 ≤ ∑ a, τ a * y a ^ 2 := Finset.sum_nonneg fun a _ ↦ mul_nonneg (hτ a) (sq_nonneg _)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a ↦ Real.sqrt (τ a) * x a)
    (fun a ↦ -(Real.sqrt (τ a) * y a))
  have e1 : ∀ a, (Real.sqrt (τ a) * x a) ^ 2 = τ a * x a ^ 2 := fun a ↦ by
    rw [mul_pow, Real.sq_sqrt (hτ a)]
  have e2 : ∀ a, (-(Real.sqrt (τ a) * y a)) ^ 2 = τ a * y a ^ 2 := fun a ↦ by
    rw [neg_sq, mul_pow, Real.sq_sqrt (hτ a)]
  have e3 : ∀ a, Real.sqrt (τ a) * x a * -(Real.sqrt (τ a) * y a) = -(τ a * x a * y a) :=
      fun a ↦ by
    have h := Real.mul_self_sqrt (hτ a)
    linear_combination (-(x a * y a)) * h
  simp only [e1, e2, e3, Finset.sum_neg_distrib] at hcs
  have hexp : ∑ a, τ a * (x a - y a) ^ 2 =
      ∑ a, τ a * x a ^ 2 - 2 * ∑ a, τ a * x a * y a + ∑ a, τ a * y a ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    ring
  rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  refine Real.sqrt_le_sqrt ?_
  rw [hexp, add_sq, Real.sq_sqrt hX, Real.sq_sqrt hY]
  linarith

/-- For real families `f g h` on a finite type, if `|h i| ≤ |f i| + |g i|` for all `i`, then
`√(∑ i, h i ^ 2) ≤ √(∑ i, f i ^ 2) + √(∑ i, g i ^ 2)`. The proof is the triangle inequality of
`EuclideanSpace ℝ ι` applied to the vectors `|f|` and `|g|`. -/
theorem sqrt_sum_sq_le {ι : Type*} [Fintype ι] (f g h : ι → ℝ) (hh : ∀ i, |h i| ≤ |f i| + |g i|) :
    Real.sqrt (∑ i, h i ^ 2) ≤ Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) := by
  have e : ∀ a : ι → ℝ, ‖(WithLp.toLp 2 a : EuclideanSpace ℝ ι)‖ = Real.sqrt (∑ i, a i ^ 2) :=
    fun a ↦ by
      rw [EuclideanSpace.norm_eq]
      simp only [Real.norm_eq_abs, sq_abs]
  have e' : ∀ a : ι → ℝ, Real.sqrt (∑ i, a i ^ 2) = Real.sqrt (∑ i, |a i| ^ 2) :=
    fun a ↦ by simp only [sq_abs]
  have key : Real.sqrt (∑ i, h i ^ 2) ≤ ‖(WithLp.toLp 2
      (fun i ↦ |f i| + |g i|) : EuclideanSpace ℝ ι)‖ := by
    rw [e]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [← sq_abs (h i)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hh i) 2
  have tri := norm_add_le (WithLp.toLp 2 (fun i ↦ |f i|) : EuclideanSpace ℝ ι)
    (WithLp.toLp 2 (fun i ↦ |g i|))
  rw [← WithLp.toLp_add] at tri
  rw [e' f, e' g, ← e (fun i ↦ |f i|), ← e (fun i ↦ |g i|)]
  exact key.trans tri

/-- Let `S` be a finite set of indices in `Fin k` and `q ϱ a : Fin k → ℝ` with `0 < ϱ i` for all
`i ∈ S`. Then `(∑ i ∈ S, |q i| * a i) ^ 2 ≤ (∑ i ∈ S, q i ^ 2 / ϱ i) * ∑ i ∈ S, ϱ i * a i ^ 2`. The
proof writes `|q i| * a i = (|q i| / √(ϱ i)) * (√(ϱ i) * a i)` and applies the Cauchy-Schwarz
inequality for finite sums. -/
theorem sum_abs_mul_sq_le {k : ℕ} (S : Finset (Fin k)) (q ϱ a : Fin k → ℝ) (hϱ : ∀ i ∈ S, 0 < ϱ i) :
    (∑ i ∈ S, |q i| * a i) ^ 2 ≤ (∑ i ∈ S, q i ^ 2 / ϱ i) * ∑ i ∈ S, ϱ i * a i ^ 2 := by
  have e : ∑ i ∈ S, |q i| * a i = ∑ i ∈ S, (|q i| / Real.sqrt (ϱ i)) * (Real.sqrt (ϱ i) * a i) := by
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have h := Real.sqrt_pos.2 (hϱ i hi)
    rw [← mul_assoc, div_mul_cancel₀ _ h.ne']
  rw [e]
  refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans (le_of_eq ?_)
  congr 1
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [div_pow, sq_abs, Real.sq_sqrt (hϱ i hi).le]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [mul_pow, Real.sq_sqrt (hϱ i hi).le]

/-- For real families `a b` and a finite set `s`, if `√(∑ j ∈ s, a j ^ 2) ≤ o`,
`√(∑ j ∈ s, b j ^ 2) ≤ t` and `o + t ≤ r`, then `∑ j ∈ s, (a j + b j) ^ 2 ≤ r ^ 2`. The proof
expands the square and bounds the cross term by the Cauchy-Schwarz inequality. -/
theorem sum_add_sq_le_of_sqrt_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) {o t r : ℝ}
    (ha : Real.sqrt (∑ j ∈ s, a j ^ 2) ≤ o) (hb : Real.sqrt (∑ j ∈ s, b j ^ 2) ≤ t)
    (hr : o + t ≤ r) : ∑ j ∈ s, (a j + b j) ^ 2 ≤ r ^ 2 := by
  have hA : 0 ≤ ∑ j ∈ s, a j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg (a j)
  have hB : 0 ≤ ∑ j ∈ s, b j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg (b j)
  have hAB := Real.sum_mul_le_sqrt_mul_sqrt s a b
  have hexp : ∑ j ∈ s, (a j + b j) ^ 2 =
      ∑ j ∈ s, a j ^ 2 + 2 * ∑ j ∈ s, a j * b j + ∑ j ∈ s, b j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hsa := Real.sq_sqrt hA
  have hsb := Real.sq_sqrt hB
  have h0a := Real.sqrt_nonneg (∑ j ∈ s, a j ^ 2)
  have h0b := Real.sqrt_nonneg (∑ j ∈ s, b j ^ 2)
  have hsum : Real.sqrt (∑ j ∈ s, a j ^ 2) + Real.sqrt (∑ j ∈ s, b j ^ 2) ≤ r := by linarith
  have hsq : (Real.sqrt (∑ j ∈ s, a j ^ 2) + Real.sqrt (∑ j ∈ s, b j ^ 2)) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (add_nonneg h0a h0b) hsum 2
  rw [hexp]
  nlinarith

/-- Minkowski's inequality for finite sums of squares: for real families `a`, `b` and a finite set
`s`, `∑ j ∈ s, (a j + b j) ^ 2 ≤ (√(∑ j ∈ s, a j ^ 2) + √(∑ j ∈ s, b j ^ 2)) ^ 2`. The proof expands
the square and bounds the cross term by the Cauchy-Schwarz inequality. -/
theorem sum_add_sq_le_sq_add_sqrt {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    ∑ j ∈ s, (a j + b j) ^ 2 ≤ (Real.sqrt (∑ j ∈ s, a j ^ 2) + Real.sqrt (∑ j ∈ s, b j ^ 2)) ^ 2 :=
        by
  have hA : 0 ≤ ∑ j ∈ s, a j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have hB : 0 ≤ ∑ j ∈ s, b j ^ 2 := Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have hexp : ∑ j ∈ s, (a j + b j) ^ 2 =
      ∑ j ∈ s, a j ^ 2 + 2 * ∑ j ∈ s, a j * b j + ∑ j ∈ s, b j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hcs : ∑ j ∈ s, a j * b j ≤ Real.sqrt (∑ j ∈ s, a j ^ 2) * Real.sqrt (∑ j ∈ s, b j ^ 2) := by
    rw [← Real.sqrt_mul hA]
    calc ∑ j ∈ s, a j * b j ≤ |∑ j ∈ s, a j * b j| := le_abs_self _
      _ = Real.sqrt ((∑ j ∈ s, a j * b j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∑ j ∈ s, a j ^ 2) * ∑ j ∈ s, b j ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq s a b)
  have h1 := Real.sq_sqrt hA
  have h2 := Real.sq_sqrt hB
  rw [hexp, add_sq, h1, h2]
  linarith

/-- Let `a b : ℕ → ℝ` satisfy `0 ≤ a i ≤ Ma` and `0 ≤ b i ≤ Mb` for all `i ≤ 3`. Then for every
`j ≤ 3`, `∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i) ≤ 8 * (Ma * Mb)`. The proof
checks the four values of `j` one by one. -/
theorem sum_choose_mul_mul_le_eight_mul {a b : ℕ → ℝ} {Ma Mb : ℝ} (ha : ∀ i ≤ 3, 0 ≤ a i ∧ a i ≤ Ma)
    (hb : ∀ i ≤ 3, 0 ≤ b i ∧ b i ≤ Mb) {j : ℕ} (hj : j ≤ 3) :
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i) ≤ 8 * (Ma * Mb) := by
  have p : ∀ i ≤ 3, ∀ k ≤ 3, a i * b k ≤ Ma * Mb := fun i hi k hk ↦
    mul_le_mul (ha i hi).2 (hb k hk).2 (hb k hk).1 ((ha i hi).1.trans (ha i hi).2)
  have n : ∀ i ≤ 3, ∀ k ≤ 3, 0 ≤ a i * b k := fun i hi k hk ↦ mul_nonneg (ha i hi).1 (hb k hk).1
  have hM : 0 ≤ Ma * Mb :=
    (n 0 (by norm_num) 0 (by norm_num)).trans (p 0 (by norm_num) 0 (by norm_num))
  have p00 := p 0 (by norm_num) 0 (by norm_num)
  have p01 := p 0 (by norm_num) 1 (by norm_num)
  have p10 := p 1 (by norm_num) 0 (by norm_num)
  have p02 := p 0 (by norm_num) 2 (by norm_num)
  have p11 := p 1 (by norm_num) 1 (by norm_num)
  have p20 := p 2 (by norm_num) 0 (by norm_num)
  have p03 := p 0 (by norm_num) 3 (by norm_num)
  have p12 := p 1 (by norm_num) 2 (by norm_num)
  have p21 := p 2 (by norm_num) 1 (by norm_num)
  have p30 := p 3 (by norm_num) 0 (by norm_num)
  interval_cases j <;> simp only [Finset.sum_range_succ, Finset.sum_range_zero] <;>
    norm_num [Nat.choose] <;> linarith

/-- Let `a b : ℕ → ℝ` satisfy `0 ≤ a i ≤ M` and `0 ≤ b i ≤ N` for all `i ≤ k`. Then
`∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * a i * b (k - i) ≤ 2 ^ k * (M * N)`. Each product
`a i * b (k - i)` is at most `M * N`, and the binomial coefficients sum to `2 ^ k`. -/
theorem sum_choose_mul_mul_le_two_pow {a b : ℕ → ℝ} {M N : ℝ} {k : ℕ}
    (ha : ∀ i ≤ k, 0 ≤ a i ∧ a i ≤ M)
    (hb : ∀ i ≤ k, 0 ≤ b i ∧ b i ≤ N) :
    ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * a i * b (k - i) ≤ 2 ^ k * (M * N) := by
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * a i * b (k - i)
      ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (M * N) := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h1 := ha i hi'
        have h2 := hb (k - i) (Nat.sub_le k i)
        have hMN : a i * b (k - i) ≤ M * N := mul_le_mul h1.2 h2.2 h2.1 (h1.1.trans h1.2)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hMN (Nat.cast_nonneg _)
    _ = 2 ^ k * (M * N) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose k

/-- Let `L res band` be finite sets of `ℤ × ℤ` with `res` and `band` disjoint, and let `f` take
values in an additive commutative monoid. Then
`∑ ι ∈ L, f ι = ∑ ι ∈ L.filter (· ∈ res), f ι + ∑ ι ∈ L.filter (· ∈ band), f ι + ∑ ι ∈ L.filter (fun
ι => ι ∉ res ∧ ι ∉ band), f ι`. -/
theorem sum_eq_sum_filter_add_of_disjoint {M : Type} [AddCommMonoid M] (L res band : Finset (ℤ × ℤ))
    (hd : Disjoint res band)
    (f : ℤ × ℤ → M) :
    ∑ ι ∈ L, f ι = ∑ ι ∈ L.filter (· ∈ res), f ι + ∑ ι ∈ L.filter (· ∈ band), f ι
      + ∑ ι ∈ L.filter (fun ι ↦ ι ∉ res ∧ ι ∉ band), f ι := by
  rw [← Finset.sum_filter_add_sum_filter_not L (· ∈ res), add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (L.filter (· ∉ res)) (· ∈ band), Finset.filter_filter,
    Finset.filter_filter]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun ι _ ↦ ?_) fun _ _ ↦ rfl
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.disjoint_right.1 hd h, h⟩⟩

/-- For finite sets `S ⊆ T` of `ℤ × ℤ` and `f` with values in an additive commutative monoid,
`∑ ι ∈ S, f ι = ∑ ι ∈ T, if ι ∈ S then f ι else 0`. -/
theorem sum_eq_sum_ite {β : Type*} [AddCommMonoid β] (S T : Finset (ℤ × ℤ)) (h : S ⊆ T)
    (f : ℤ × ℤ → β) :
    ∑ ι ∈ S, f ι = ∑ ι ∈ T, if ι ∈ S then f ι else 0 := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 h]

open Classical in
/-- For a finite set `s` of integer pairs, a function `B : ℤ × ℤ → ℝ` and a predicate `c` on
`ℤ × ℤ`, `∑ α ∈ s, B α = ∑ α ∈ s, (if c α then 0 else B α) + ∑ α ∈ s, (if c α then B α else 0)`. -/
theorem sum_eq_sum_ite_add_sum_ite (s : Finset (ℤ × ℤ)) (B : ℤ × ℤ → ℝ) (c : ℤ × ℤ → Prop) :
    ∑ α ∈ s, B α = ∑ α ∈ s, (if c α then 0 else B α) + ∑ α ∈ s, (if c α then B α else 0) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ ↦ by split_ifs <;> ring

/-- Let `H` be a finite set of integer pairs that is closed under negation (`-β ∈ H` for every
`β ∈ H`) and let `F : ℤ × ℤ → M` take values in an additive commutative monoid `M`. Then
`∑ β ∈ H, F β = ∑ β ∈ H, F (-β)`. -/
theorem sum_eq_sum_neg_of_neg_mem {M : Type} [AddCommMonoid M] (H : Finset (ℤ × ℤ))
    (hH : ∀ β ∈ H, -β ∈ H)
    (F : ℤ × ℤ → M) : ∑ β ∈ H, F β = ∑ β ∈ H, F (-β) :=
  Finset.sum_bij' (fun β _ ↦ -β) (fun β _ ↦ -β) (fun β hβ ↦ hH β hβ) (fun β hβ ↦ hH β hβ)
    (fun β _ ↦ neg_neg β) (fun β _ ↦ neg_neg β) (fun β _ ↦ by simp)

/-- For `g : ℕ × ℕ → ℝ` and a decidable relation `P` on `ℕ`, the double sum over `j l : Fin (Q + 1)`
of `if P j l then g (j, l) else 0` equals the sum of `g` over the pairs in
`Finset.range (Q + 1) ×ˢ Finset.range (Q + 1)` that satisfy `P`. -/
theorem sum_fin_fin_ite_eq_sum_filter (Q : ℕ) (g : ℕ × ℕ → ℝ) (P : ℕ → ℕ → Prop)
    [∀ j l, Decidable (P j l)] :
    (∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), if P j l then g (j, l) else 0)
      = ∑ i ∈ (Finset.range (Q + 1) ×ˢ Finset.range (Q + 1)).filter (fun i ↦ P i.1 i.2), g i := by
  rw [Finset.sum_filter, Finset.sum_product]
  rw [← Fin.sum_univ_eq_sum_range (fun j ↦ ∑ l ∈ Finset.range (Q + 1),
      if P j l then g (j, l) else 0)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l ↦ if P j l then g (j, l) else 0)]

/-- For naturals `N`, `k`, a decidable proposition `P` such that `P` implies `k < N`, and
`F : ℕ → ℂ`, `∑ i : Fin N, (if P ∧ k = (i : ℕ) then F i else 0) = if P then F k else 0`. If `P`
holds, only the index `k` contributes; otherwise every term vanishes. -/
theorem sum_fin_ite_and_eq_val (N k : ℕ) (P : Prop) [Decidable P] (hk : P → k < N) (F : ℕ → ℂ) :
    ∑ i : Fin N, (if P ∧ k = (i : ℕ) then F i else 0) = if P then F k else 0 := by
  by_cases hP : P
  · rw [ite_eq_left hP, Finset.sum_eq_single ⟨k, hk hP⟩]
    · simp [hP]
    · intro i _ hi
      rw [ite_eq_right]
      rintro ⟨_, e⟩
      exact hi (Fin.ext e.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp [hP]

/-- For `F : ℕ → ℕ → ℝ`, the sum of `F jl.1 jl.2` over all pairs `jl : Fin n × Fin n'` equals the
double sum `∑ j ∈ range n, ∑ l ∈ range n', F j l`. -/
theorem sum_fin_prod_fin_eq_sum_range (n n' : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ jl : Fin n × Fin n', F jl.1 jl.2 = ∑ j ∈ range n, ∑ l ∈ range n', F j l := by
  rw [Fintype.sum_prod_type, Finset.sum_range (fun j ↦ ∑ l ∈ range n', F j l)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact (Finset.sum_range (F j)).symm

/-- If every entry of `x : Fin 3 → ℝ` is strictly less than `δ`, then `∑ j : Fin 3, x j < 3 * δ`. -/
theorem sum_fin_three_lt {x : Fin 3 → ℝ} {δ : ℝ} (h : ∀ j, x j < δ) : ∑ j : Fin 3, x j < 3 * δ := by
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

/-- Ring identity for real numbers: the difference of
`c1 * X1 ^ 2 + c2 * X2 ^ 2 + c3 * X3 ^ 2 + c4 * X4 ^ 2 - c5 * X5 ^ 2` and the same expression with
`Y1, …, Y5` in place of `X1, …, X5` equals
`(c1 * X1 ^ 2 - c1 * Y1 ^ 2) + (c2 * X2 ^ 2 - c2 * Y2 ^ 2) + (c3 * X3 ^ 2 - c3 * Y3 ^ 2) + (c4 * X4
^ 2 - c4 * Y4 ^ 2) - (c5 * X5 ^ 2 - c5 * Y5 ^ 2)`. -/
theorem sum_five_mul_sq_sub_eq (c1 c2 c3 c4 c5 X1 X2 X3 X4 X5 Y1 Y2 Y3 Y4 Y5 : ℝ) :
    c1 * X1 ^ 2 + c2 * X2 ^ 2 + c3 * X3 ^ 2 + c4 * X4 ^ 2 - c5 * X5 ^ 2
      - (c1 * Y1 ^ 2 + c2 * Y2 ^ 2 + c3 * Y3 ^ 2 + c4 * Y4 ^ 2 - c5 * Y5 ^ 2)
      = (c1 * X1 ^ 2 - c1 * Y1 ^ 2) + (c2 * X2 ^ 2 - c2 * Y2 ^ 2) + (c3 * X3 ^ 2 - c3 * Y3 ^ 2)
        + (c4 * X4 ^ 2 - c4 * Y4 ^ 2) - (c5 * X5 ^ 2 - c5 * Y5 ^ 2) := by ring

/-- For a finite set `M` of `ℤ × ℤ` and `f` with values in an additive commutative monoid,
`∑ l ∈ M.image Prod.snd, ∑ n₁ ∈ (M.filter (fun ι ↦ ι.2 = l)).image Prod.fst, f (n₁, l) = ∑ ι ∈ M, f
ι`. In words, the sum over `M` can be taken first over the second coordinates that occur in `M` and
then over the first coordinates of the elements with that second coordinate. The proof groups the
sum over `M` by the fibres of `Prod.snd`. -/
theorem sum_image_snd_sum_image_fst {β : Type*} [AddCommMonoid β] (M : Finset (ℤ × ℤ))
    (f : ℤ × ℤ → β) :
    ∑ l ∈ M.image Prod.snd, ∑ n₁ ∈ (M.filter (fun ι ↦ ι.2 = l)).image Prod.fst,
        f (n₁, l) = ∑ ι ∈ M, f ι := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := M) (t := M.image Prod.snd) (g := Prod.snd)
    (fun i hi ↦ Finset.mem_image_of_mem _ hi) f]
  refine Finset.sum_congr rfl (fun l _ ↦ ?_)
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl (fun ι hι ↦ ?_)
    rw [Finset.mem_filter] at hι
    rw [← hι.2]
  · intro a ha b hb hab
    rw [Finset.coe_filter] at ha hb
    exact Prod.ext hab (ha.2.trans hb.2.symm)

/-- For a finite set `S` of `ℤ × ℤ`, a natural number `N`, a real `β` and `g : ℤ × ℤ → ℝ`, the sum
over `ι ∈ S` of `(if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) * g ι` equals `β` times the sum of `g`
over the `ι ∈ S` with `|ι.1| ≤ N`, plus `1 + 1 / β` times the sum of `g` over the other elements of
`S`. -/
theorem sum_ite_abs_fst_le_mul (S : Finset (ℤ × ℤ)) (N : ℕ) (β : ℝ) (g : ℤ × ℤ → ℝ) :
    ∑ ι ∈ S, (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) * g ι
      = β * ∑ ι ∈ S.filter (fun ι ↦ |ι.1| ≤ (N : ℤ)), g ι
        + (1 + 1 / β) * ∑ ι ∈ S.filter (fun ι ↦ ¬ |ι.1| ≤ (N : ℤ)), g ι := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ι ↦ |ι.1| ≤ (N : ℤ)), Finset.mul_sum,
      Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun ι hι ↦ ?_
    rw [ite_eq_left (Finset.mem_filter.1 hι).2]
  · refine Finset.sum_congr rfl fun ι hι ↦ ?_
    rw [ite_eq_right (Finset.mem_filter.1 hι).2]

/-- Let `Rs`, `Bd`, `B` be finite sets of integer pairs, `f : ℤ × ℤ → ℤ × ℤ → ℂ`, and `modes`,
`partners`, `harm : Fin G → Finset (ℤ × ℤ)` with every `harm i ⊆ B` and the sets `harm i` pairwise
disjoint. Suppose that whenever `ι ∈ Rs`, `β ∈ B`, `ι + β ∉ Rs`, `ι + β ∉ Bd` and `f ι β ≠ 0`, some
`i` has `ι ∈ modes i`, `ι + β ∈ partners i` and `β ∈ harm i`. Then the sum over `ι ∈ Rs`, `β ∈ B` of
`f ι β` restricted to `ι + β ∉ Rs ∧ ι + β ∉ Bd` equals the sum over `i`, `ι ∈ Rs` with
`ι ∈ modes i`, and `β ∈ harm i` of `f ι β` restricted to `ι + β ∈ partners i`, `ι + β ∉ Rs`,
`ι + β ∉ Bd`; the proof writes each term as a sum over `i` with at most one nonzero summand and
exchanges the sums. -/
theorem sum_ite_eq_sum_fin_of_cover {G : ℕ} (Rs Bd B : Finset (ℤ × ℤ))
    (modes partners harm : Fin G → Finset (ℤ × ℤ))
    (f : ℤ × ℤ → ℤ × ℤ → ℂ)
    (hcover : ∀ ι ∈ Rs, ∀ β ∈ B, ι + β ∉ Rs → ι + β ∉ Bd → f ι β ≠ 0 →
      ∃ i, ι ∈ modes i ∧ ι + β ∈ partners i ∧ β ∈ harm i)
    (hsub : ∀ i, harm i ⊆ B) (hdisj : ∀ i j β, β ∈ harm i → β ∈ harm j → i = j) :
    (∑ ι ∈ Rs, ∑ β ∈ B, if ι + β ∉ Rs ∧ ι + β ∉ Bd then f ι β else 0)
      = ∑ i, ∑ ι ∈ Rs.filter (fun ι ↦ ι ∈ modes i), ∑ β ∈ harm i,
          if ι + β ∈ (partners i).filter (fun ι' ↦ ι' ∉ Rs ∧ ι' ∉ Bd) then f ι β else 0 := by
  have step1 : ∀ ι ∈ Rs, ∀ β ∈ B, (if ι + β ∉ Rs ∧ ι + β ∉ Bd then f ι β else 0)
      = ∑ i, if ι ∈ modes i ∧ β ∈ harm i ∧ ι + β ∈ (partners i).filter (fun ι' ↦ ι' ∉ Rs ∧ ι' ∉ Bd)
          then f ι β else 0 := by
    intro ι hι β hβ
    by_cases hD : ι + β ∉ Rs ∧ ι + β ∉ Bd
    · by_cases hf : f ι β = 0
      · rw [ite_eq_left hD, hf]
        symm
        exact Finset.sum_eq_zero (fun i _ ↦ ite_self _)
      obtain ⟨i0, h1, h2, h3⟩ := hcover ι hι β hβ hD.1 hD.2 hf
      rw [ite_eq_left hD, Finset.sum_eq_single i0]
      · rw [ite_eq_left ⟨h1, h3, Finset.mem_filter.2 ⟨h2, hD⟩⟩]
      · intro j _ hj
        rw [ite_eq_right]
        rintro ⟨_, hj2, _⟩
        exact hj (hdisj j i0 β hj2 h3)
      · intro h
        exact absurd (Finset.mem_univ i0) h
    · rw [ite_eq_right hD]
      symm
      refine Finset.sum_eq_zero (fun i _ ↦ ite_eq_right ?_)
      rintro ⟨_, _, h⟩
      exact hD (Finset.mem_filter.1 h).2
  rw [Finset.sum_congr rfl (fun ι hι ↦ Finset.sum_congr rfl (fun β hβ ↦ step1 ι hι β hβ))]
  rw [Finset.sum_congr rfl (fun ι _ ↦ Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun ι _ ↦ ?_)
  by_cases hm : ι ∈ modes i
  · rw [ite_eq_left hm]
    symm
    rw [← Finset.sum_subset (hsub i)]
    · refine Finset.sum_congr rfl (fun β hβ ↦ ?_)
      by_cases hq : ι + β ∈ (partners i).filter (fun ι' ↦ ι' ∉ Rs ∧ ι' ∉ Bd)
      · rw [ite_eq_left hq, ite_eq_left ⟨hm, hβ, hq⟩]
      · rw [ite_eq_right hq, ite_eq_right]
        rintro ⟨_, _, h⟩
        exact hq h
    · intro β _ hβ
      rw [ite_eq_right]
      rintro ⟨_, h, _⟩
      exact hβ h
  · rw [ite_eq_right hm]
    refine Finset.sum_eq_zero (fun β _ ↦ ite_eq_right ?_)
    rintro ⟨h, _, _⟩
    exact hm h

open Classical in
/-- Let `s` be a finite set of integer pairs and let `Y B : ℤ × ℤ → ℝ` satisfy `Y α ≤ B α` for every
`α ∈ s`. Then for every predicate `c` on `ℤ × ℤ`,
`∑ α ∈ s, (if c α then Y α else 0) ≤ ∑ α ∈ s, (if c α then B α else 0)`. -/
theorem sum_ite_le_sum_ite_of_le (s : Finset (ℤ × ℤ)) (Y B : ℤ × ℤ → ℝ) (hYB : ∀ α ∈ s, Y α ≤ B α)
    (c : ℤ × ℤ → Prop) :
    ∑ α ∈ s, (if c α then Y α else 0) ≤ ∑ α ∈ s, (if c α then B α else 0) :=
  Finset.sum_le_sum fun α hα ↦ by
    split_ifs
    · exact hYB α hα
    · exact le_rfl

/-- Let `F` be a finite set of pairs of natural numbers and `x j l ≥ 0` for all `j`, `l`. Then
`∑ jl ∈ F, (if D < max jl.1 jl.2 then x jl.1 jl.2 else 0)` is at most the sum over
`j' ∈ F.image Prod.fst` and `l' ∈ F.image Prod.snd` of `if D < j' then x j' l' else 0`, plus the
same double sum of `if D < l' then x j' l' else 0`. The proof uses that `D < max j l` means `D < j`
or `D < l`, and enlarges `F` to the product of its two projections. -/
theorem sum_ite_lt_max_le_add (D : ℕ) (F : Finset (ℕ × ℕ)) (x : ℕ → ℕ → ℝ) (hx : ∀ j l, 0 ≤ x j l) :
    ∑ jl ∈ F, (if D < max jl.1 jl.2 then x jl.1 jl.2 else 0)
      ≤ ∑ j' ∈ F.image Prod.fst, ∑ l' ∈ F.image Prod.snd, (if D < j' then x j' l' else 0)
        + ∑ j' ∈ F.image Prod.fst, ∑ l' ∈ F.image Prod.snd, (if D < l' then x j' l' else 0) := by
  have hsub : F ⊆ (F.image Prod.fst) ×ˢ (F.image Prod.snd) := by
    intro q hq
    exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hq, Finset.mem_image_of_mem _ hq⟩
  simp only [← Finset.sum_add_distrib]
  rw [← Finset.sum_product' (f := fun j' l' ↦
    (if D < j' then x j' l' else 0) + (if D < l' then x j' l' else 0))]
  calc ∑ jl ∈ F, (if D < max jl.1 jl.2 then x jl.1 jl.2 else 0)
      ≤ ∑ jl ∈ F, ((if D < jl.1 then x jl.1 jl.2 else 0) +
          (if D < jl.2 then x jl.1 jl.2 else 0)) := by
        refine Finset.sum_le_sum fun jl _ ↦ ?_
        have h0 := hx jl.1 jl.2
        by_cases h1 : D < jl.1 <;> by_cases h2 : D < jl.2 <;>
          simp only [h1, h2, ite_true, ite_false, lt_max_iff, or_self, true_or, or_true] <;>
              linarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun jl _ _ ↦ by
        have h0 := hx jl.1 jl.2
        split_ifs <;> linarith

/-- Let `S`, `T` be finite sets of integer pairs, `ι : ℤ × ℤ` and `f g : ℤ × ℤ → ℂ` with
`f α = g (ι - α)` for all `α`, and suppose `g ι' = 0` for every `ι' ∈ S` with `ι - ι' ∉ T`. Then
`∑ α ∈ T, (if ι - α ∈ S then f α else 0) = ∑ ι' ∈ S, g ι'`. The proof reindexes by the involution
`α ↦ ι - α`. -/
theorem sum_ite_sub_mem_eq_sum {S T : Finset (ℤ × ℤ)} (ι : ℤ × ℤ) (f g : ℤ × ℤ → ℂ)
    (hfg : ∀ α, f α = g (ι - α)) (hz : ∀ ι' ∈ S, ι - ι' ∉ T → g ι' = 0) :
    ∑ α ∈ T, (if ι - α ∈ S then f α else 0) = ∑ ι' ∈ S, g ι' := by
  classical
  have h2 : ∑ ι' ∈ S, g ι' = ∑ ι' ∈ S with ι - ι' ∈ T, g ι' :=
    (Finset.sum_filter_of_ne (p := fun ι' ↦ ι - ι' ∈ T) (fun ι' h hne ↦ by
      by_contra hn; exact hne (hz ι' h hn))).symm
  rw [← Finset.sum_filter, h2]
  refine Finset.sum_nbij' (fun α ↦ ι - α) (fun ι' ↦ ι - ι') ?_ ?_ ?_ ?_ ?_
  · intro α hα
    rw [Finset.mem_filter] at hα ⊢
    exact ⟨hα.2, by rw [sub_sub_cancel]; exact hα.1⟩
  · intro ι' hι
    rw [Finset.mem_filter] at hι ⊢
    exact ⟨hι.2, by rw [sub_sub_cancel]; exact hι.1⟩
  · intro α _; simp
  · intro ι' _; simp
  · intro α _; exact hfg α

/-- Change of variable `α = ℓ - ι` in a filtered sum over finite sets of `ℤ × ℤ`. If every element
of `U` lies in `H`, then
`∑ ι ∈ T, (if ℓ - ι ∈ U then F (ℓ - ι) else 0) = ∑ α ∈ H, (if α ∈ U ∧ ℓ - α ∈ T then F α else
0)`, for `F` with values in an additive commutative monoid. The proof shows that `ι ↦ ℓ -
ι` maps the indices kept on the left bijectively onto those kept on the right. -/
theorem sum_ite_sub_mem_eq_sum_ite {β : Type*} [AddCommMonoid β] (ℓ : ℤ × ℤ)
    (H T U : Finset (ℤ × ℤ)) (F : ℤ × ℤ → β)
    (hU : ∀ α ∈ U, α ∈ H) :
    ∑ ι ∈ T, (if ℓ - ι ∈ U then F (ℓ - ι) else 0)
      = ∑ α ∈ H, (if α ∈ U ∧ ℓ - α ∈ T then F α else 0) := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have himg : (T.filter (fun ι ↦ ℓ - ι ∈ U)).image (fun ι ↦ ℓ - ι)
      = H.filter (fun α ↦ α ∈ U ∧ ℓ - α ∈ T) := by
    ext α
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨ι, ⟨hιT, hιU⟩, rfl⟩
      exact ⟨hU _ hιU, hιU, by rwa [sub_sub_cancel]⟩
    · rintro ⟨_, hαU, hαT⟩
      exact ⟨ℓ - α, ⟨hαT, by rwa [sub_sub_cancel]⟩, sub_sub_cancel ℓ α⟩
  rw [← himg, Finset.sum_image (fun x _ y _ hxy ↦ sub_right_injective hxy)]

/-- For three nonnegative reals `a i`, `i : Fin 3`, `∑ i, a i ≤ 1 + 3 * ∑ i, a i ^ 2`. -/
theorem sum_le_one_add_mul_sum_sq (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, a i ≤ 1 + 3 * ∑ i, a i ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
  rw [Finset.card_univ, Fintype.card_fin] at h1
  push_cast at h1
  have h0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ ↦ ha i
  nlinarith [sq_nonneg (∑ i, a i - 1)]

/-- For real families `F M K` on a finite type and a real `x`,
`∑ i, F i * (M i + K i) - x = (∑ i, F i * M i - x) + ∑ i, F i * K i`. -/
theorem sum_mul_add_sub_eq {ι : Type*} [Fintype ι] (F M K : ι → ℝ) (x : ℝ) :
    ∑ i, F i * (M i + K i) - x = (∑ i, F i * M i - x) + ∑ i, F i * K i := by
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- For a finite set `S` of integer pairs and `w c : ℤ × ℤ → ℂ`,
`∑ β ∈ S, w β * (if β = 0 then 0 else c β) = ∑ β ∈ S, w β * c β - (if 0 ∈ S then w 0 * c 0 else
0)`. -/
theorem sum_mul_ite_zero_eq_sum_sub (S : Finset (ℤ × ℤ)) (w c : ℤ × ℤ → ℂ) :
    ∑ β ∈ S, w β * (if β = 0 then 0 else c β) = ∑ β ∈ S,
        w β * c β - (if (0 : ℤ × ℤ) ∈ S then w 0 * c 0 else 0) := by
  have e : ∑ β ∈ S, w β * c β
      = ∑ β ∈ S, w β * (if β = 0 then 0 else c β) + ∑ β ∈ S, (if β = 0 then w β * c β else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ ↦ ?_
    split_ifs <;> ring
  rw [e, Finset.sum_ite_eq' S (0 : ℤ × ℤ) (fun β ↦ w β * c β)]
  ring

/-- Scaling one fixed inequality between finite sums by a real `r ≥ 0`. For finite sets `s u w` of
`ℤ × ℤ`, assume `(∑ i ∈ s, ∑ j ∈ s, f1 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, f2 i j + 2 * ∑ i ∈ s, ∑ j ∈ w, f3
i j) - C ≤ (∑ i ∈ s, ∑ j ∈ s, f4 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, f5 i j +
2 * ∑ i ∈ s, ∑ j ∈ w, f6 i j) - ∑ i ∈ s, ∑ j ∈ s, f7 i
j`, where `C` is the sum of twelve single sums: of `c1`, `c2`, `c5`, `c6`, `c9`, `c10` over `s`, of
`c3`, `c7`, `c11` over `u` and of `c4`, `c8`, `c12` over `w`. Then the same inequality holds with
every summand `f1 i j`, ..., `f7 i j`, `c1 i`, ..., `c12 i` multiplied on the left by `r`. -/
theorem sum_mul_left_le_of_sum_le (r : ℝ) (hr : 0 ≤ r) (s u w : Finset (ℤ × ℤ))
    (f1 f2 f3 f4 f5 f6 f7 : ℤ × ℤ → ℤ × ℤ → ℝ)
    (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : ℤ × ℤ → ℝ)
    (h : (∑ i ∈ s, ∑ j ∈ s, f1 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, f2 i j + 2 * ∑ i ∈ s, ∑ j ∈ w, f3 i j)
        - (∑ i ∈ s, c1 i + ∑ i ∈ s, c2 i + ∑ i ∈ u, c3 i + ∑ i ∈ w, c4 i + ∑ i ∈ s, c5 i + ∑ i ∈ s,
            c6 i
          + ∑ i ∈ u, c7 i + ∑ i ∈ w, c8 i + ∑ i ∈ s, c9 i + ∑ i ∈ s, c10 i + ∑ i ∈ u,
              c11 i + ∑ i ∈ w, c12 i)
      ≤ (∑ i ∈ s, ∑ j ∈ s, f4 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, f5 i j + 2 * ∑ i ∈ s, ∑ j ∈ w, f6 i j)
        - ∑ i ∈ s, ∑ j ∈ s, f7 i j) :
    (∑ i ∈ s, ∑ j ∈ s, r * f1 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, r * f2 i j + 2 * ∑ i ∈ s, ∑ j ∈ w,
        r * f3 i j)
        - (∑ i ∈ s, r * c1 i + ∑ i ∈ s, r * c2 i + ∑ i ∈ u, r * c3 i + ∑ i ∈ w, r * c4 i + ∑ i ∈ s,
            r * c5 i
          + ∑ i ∈ s, r * c6 i + ∑ i ∈ u, r * c7 i + ∑ i ∈ w, r * c8 i + ∑ i ∈ s,
              r * c9 i + ∑ i ∈ s, r * c10 i
          + ∑ i ∈ u, r * c11 i + ∑ i ∈ w, r * c12 i)
      ≤ (∑ i ∈ s, ∑ j ∈ s, r * f4 i j + 2 * ∑ i ∈ s, ∑ j ∈ u, r * f5 i j + 2 * ∑ i ∈ s, ∑ j ∈ w,
          r * f6 i j)
        - ∑ i ∈ s, ∑ j ∈ s, r * f7 i j := by
  have h2 := mul_le_mul_of_nonneg_left h hr
  have hm : ∀ y : ℝ, r * (2 * y) = 2 * (r * y) := fun y ↦ by ring
  simp only [mul_sub, mul_add, hm, Finset.mul_sum] at h2 ⊢
  exact h2

/-- For real-valued `f` and weights `μ`,
`∑ a ∈ T, μ a * ∑ n ∈ s, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, (if cnd n j l then f a n j l
else 0)` equals `∑ n ∈ s, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, (if cnd n j l then ∑ a ∈ T, μ
a * f a n j l else 0)`. The proof distributes `μ
a` over the inner sums and commutes the sum over `a` with each of the three inner sums. -/
theorem sum_mul_sum_sum_sum_ite_comm {ι : Type*} (T : Finset ι) (s : Finset ℤ) (m : ℕ) (μ : ι → ℝ)
    (cnd : ℤ → ℕ → ℕ → Prop)
    [∀ n j l, Decidable (cnd n j l)] (f : ι → ℤ → ℕ → ℕ → ℝ) :
    (∑ a ∈ T, μ a * ∑ n ∈ s, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
        if cnd n j l then f a n j l else 0)
      = ∑ n ∈ s, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m,
          if cnd n j l then ∑ a ∈ T, μ a * f a n j l else 0 := by
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  split_ifs <;> simp

/-- Let `s` be a finite set of integer pairs that is closed under negation (`-α ∈ s` for every `α ∈
s`). Then `∑ α ∈ s, F (-α) = ∑ α ∈ s, F α` for every `F : ℤ × ℤ → ℝ`. A case of
`PDE.Analysis.sum_eq_sum_neg_of_neg_mem`. -/
theorem sum_neg_eq_sum_of_neg_mem (s : Finset (ℤ × ℤ)) (hneg : ∀ α ∈ s, -α ∈ s) (F : ℤ × ℤ → ℝ) :
    ∑ α ∈ s, F (-α) = ∑ α ∈ s, F α :=
  Eq.symm (sum_eq_sum_neg_of_neg_mem s hneg F)

/-- For a finite subset `s` of `ℤ × ℤ` closed under negation and `f : ℤ × ℤ → ℂ`,
`∑ κ ∈ s, f (-κ) = ∑ κ ∈ s, f κ`. -/
theorem sum_neg_index (s : Finset (ℤ × ℤ)) (hs : ∀ κ ∈ s, -κ ∈ s) (f : ℤ × ℤ → ℂ) :
    ∑ κ ∈ s, f (-κ) = ∑ κ ∈ s, f κ :=
  Finset.sum_nbij' (fun κ ↦ -κ) (fun κ ↦ -κ) (fun κ hk ↦ hs κ hk) (fun κ hk ↦ hs κ hk)
    (fun κ _ ↦ neg_neg κ) (fun κ _ ↦ neg_neg κ) fun _ _ ↦ rfl

/-- If a finite set `S` of `ℤ × ℤ` is closed under negation, then `∑ β ∈ S, f (-β) = ∑ β ∈ S, f β`
for every `f` with values in an additive commutative monoid. -/
theorem sum_neg_of_symmetric {M : Type*} [AddCommMonoid M] {S : Finset (ℤ × ℤ)}
    (hS : ∀ β ∈ S, -β ∈ S)
    (f : ℤ × ℤ → M) : ∑ β ∈ S, f (-β) = ∑ β ∈ S, f β := by
  refine Finset.sum_nbij' (fun β ↦ -β) (fun β ↦ -β) (fun β hβ ↦ hS β hβ) (fun β hβ ↦ hS β hβ)
    (fun β _ ↦ neg_neg β) (fun β _ ↦ neg_neg β) (fun β _ ↦ rfl)

/-- A sum over `Fin 3 × Fin 3 × Fin 3` is an iterated sum:
`∑ x, f x.1 x.2.1 x.2.2 = ∑ a, ∑ b, ∑ c, f a b c`, for `f` with values in an additive commutative
monoid. -/
theorem sum_prod_prod_fin_three {M : Type*} [AddCommMonoid M] (f : Fin 3 → Fin 3 → Fin 3 → M) :
    ∑ x : Fin 3 × Fin 3 × Fin 3, f x.1 x.2.1 x.2.2 =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, f a b c := by
  simp only [Fintype.sum_prod_type]

/-- Let `a`, `b : ℕ → ℝ` satisfy `0 ≤ a i ≤ M` and `0 ≤ b i ≤ M` for all `i ≤ 2`. Then for every
natural `j ≤ 2`, `∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i) ≤ 4 * (M * M)`. The
proof checks `j = 0`, `1`, `2` one by one; the binomial coefficients in each case add up to at most
`4`. -/
theorem sum_range_choose_mul_mul_le {a b : ℕ → ℝ} {M : ℝ} (ha : ∀ i ≤ 2, 0 ≤ a i ∧ a i ≤ M)
    (hb : ∀ i ≤ 2, 0 ≤ b i ∧ b i ≤ M) {j : ℕ} (hj : j ≤ 2) :
    ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a i * b (j - i) ≤ 4 * (M * M) := by
  have p : ∀ i ≤ 2, ∀ k ≤ 2, a i * b k ≤ M * M := fun i hi k hk ↦
    mul_le_mul (ha i hi).2 (hb k hk).2 (hb k hk).1 ((ha i hi).1.trans (ha i hi).2)
  have n : ∀ i ≤ 2, ∀ k ≤ 2, 0 ≤ a i * b k := fun i hi k hk ↦ mul_nonneg (ha i hi).1 (hb k hk).1
  have hM : 0 ≤ M * M := (n 0 (by
    norm_num) 0 (by norm_num)).trans (p 0 (by norm_num) 0 (by norm_num))
  interval_cases j
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    linarith [p 0 (by norm_num) 0 (by norm_num)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    linarith [p 0 (by norm_num) 1 (by norm_num), p 1 (by norm_num) 0 (by norm_num)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    linarith [p 0 (by norm_num) 2 (by norm_num), p 1 (by norm_num) 1 (by norm_num),
      p 2 (by norm_num) 0 (by norm_num)]

/-- Let `m` be a strictly increasing list of reals (`m.Pairwise (· < ·)`), `t` a real and
`u : ℕ → ℝ`. Then
`∑ i ∈ Finset.range m.length, (if m.getD i 0 ≤ t then u i else 0) = ∑ i ∈ Finset.range (m.filter
(fun b ↦ decide (b ≤ t))).length, u
i`, because the entries that are at most `t` form an initial segment of `m`. The proof is by
induction on the list. -/
theorem sum_range_ite_eq_sum_range_filter (t : ℝ) : ∀ (m : List ℝ), m.Pairwise (· < ·) → ∀
    (u : ℕ → ℝ),
    ∑ i ∈ Finset.range m.length, (if m.getD i 0 ≤ t then u i else 0) =
      ∑ i ∈ Finset.range (m.filter (fun b ↦ decide (b ≤ t))).length, u i := by
  intro m
  induction m with
  | nil => intro _ u; simp
  | cons b m ih =>
    intro hm u
    rw [List.pairwise_cons] at hm
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    by_cases hb : b ≤ t
    · rw [List.filter_cons_of_pos (by simpa using hb), List.length_cons, Finset.sum_range_succ',
        ih hm.2 (fun i ↦ u (i + 1)), ite_eq_left hb]
    · have hnil : m.filter (fun x ↦ decide (x ≤ t)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        have := hm.1 x hx
        simp only [decide_eq_true_eq, not_le]
        linarith [not_le.mp hb]
      rw [List.filter_cons_of_neg (by simpa using hb), hnil, ite_eq_right hb, List.length_nil,
        Finset.sum_range_zero, add_zero]
      apply Finset.sum_eq_zero
      intro i hi
      have hi' : i < m.length := Finset.mem_range.mp hi
      have hlt := hm.1 (m.getD i 0) (by
        rw [List.getD_eq_getElem _ _ hi']; exact List.getElem_mem hi')
      rw [ite_eq_right (fun hle ↦ hb (le_trans (le_of_lt hlt) hle))]

/-- For natural numbers `M ≤ N` and `X : ℕ → ℝ`,
`∑ j ∈ range N, (if M ≤ j then 1 else 0) * X j = ∑ j ∈ range N, X j - ∑ j ∈ range M, X
j`. The proof is by induction on `N`. -/
theorem sum_range_ite_le_mul_eq_sub (M N : ℕ) (h : M ≤ N) (X : ℕ → ℝ) :
    ∑ j ∈ range N, (if M ≤ j then (1 : ℝ) else 0) * X j = ∑ j ∈ range N, X j - ∑ j ∈ range M,
        X j := by
  induction N with
  | zero =>
    have : M = 0 := by omega
    subst this
    simp
  | succ N ih =>
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'
      rw [sub_self]
      exact Finset.sum_eq_zero fun j hj ↦ by
        rw [ite_eq_right (by have := Finset.mem_range.1 hj; omega), zero_mul]
    · rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (by omega), ite_eq_left (by omega)]
      ring

/-- The sum of the first `n + 1` odd numbers is a square:
`∑ k ∈ range (n + 1), (k + 1 + k) = (n + 1) ^ 2` in the real numbers. The proof is by induction on
`n`. -/
theorem sum_range_odd_eq_add_one_sq (n : ℕ) :
    ∑ k ∈ range (n + 1), ((k : ℝ) + 1 + k) = ((n : ℝ) + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- For every natural number `q`, `∑ m ∈ range (q + 1), 4 * m ^ 2 * (2 * m + 1) ≤ 2 * (q + 1) ^ 4`
in the real numbers. The proof is by induction on `q`. -/
theorem sum_range_sq_mul_le_pow_four (q : ℕ) :
    ∑ m ∈ range (q + 1), 4 * (m : ℝ) ^ 2 * (2 * m + 1) ≤ 2 * ((q : ℝ) + 1) ^ 4 := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    push_cast
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [ih, sq_nonneg (n : ℝ), mul_nonneg hn (sq_nonneg (n : ℝ))]

/-- For `j ≤ Q` and a function `f` from `ℕ` to an additive commutative monoid,
`∑ i ∈ Finset.range (j + 1), f i = ∑ i : Fin (Q + 1), if (i : ℕ) ≤ j then f i else 0`. -/
theorem sum_range_succ_eq_sum_fin_ite {M : Type*} [AddCommMonoid M] (f : ℕ → M) {j Q : ℕ}
    (hj : j ≤ Q) :
    ∑ i ∈ Finset.range (j + 1), f i = ∑ i : Fin (Q + 1), if (i : ℕ) ≤ j then f i else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i ≤ j then f i else 0) (Q + 1), Finset.sum_ite,
    Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  ext i
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

/-- Let `S` be a finite set of integer pairs closed under negation, `K` a finite set,
`ν : α → ℤ × ℤ` with `ν a ∈ S` for all `a ∈ K`, and `w : α → ℂ`. Then
`∑ ξ ∈ S, (∑ a ∈ K, ((if ξ = ν a then w a / 2 else 0) + (if ξ = -ν a then conj (w a) / 2 else
0))).re = ∑ a ∈ K, (w a).re`. -/
theorem sum_re_sum_ite_add_ite_conj {α : Type*} (S : Finset (ℤ × ℤ)) (hSy : ∀ β ∈ S, -β ∈ S)
    (K : Finset α)
    (ν : α → ℤ × ℤ) (hK : ∀ a ∈ K, ν a ∈ S) (w : α → ℂ) :
    ∑ ξ ∈ S, (∑ a ∈ K, ((if ξ = ν a then w a / 2 else 0) +
      (if ξ = -ν a then starRingEnd ℂ (w a) / 2 else 0))).re = ∑ a ∈ K, (w a).re := by
  rw [← Complex.re_sum, Finset.sum_comm, Complex.re_sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' S (ν a), Finset.sum_ite_eq' S (-ν a),
    ite_eq_left (hK a ha), ite_eq_left (hSy _ (hK a ha))]
  simp

/-- For a finite type `α`, `c : ℂ` and `u w F : α → ℂ`,
`∑ a, (c • (u - w)) a * F a = c * (∑ a, u a * F a - ∑ a, w a * F a)`. -/
theorem sum_smul_sub_apply_mul {α : Type} [Fintype α] (c : ℂ) (u w : α → ℂ) (F : α → ℂ) :
    ∑ a, (c • (u - w)) a * F a = c * (∑ a, u a * F a - ∑ a, w a * F a) := by
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ ↦ by ring

/-- For a finite type `α`, `c b : ℂ` and `r u w F : α → ℂ`,
`∑ a, (c • (r - b • (u - w))) a * F a = c * (∑ a, r a * F a - b * (∑ a, u a * F a - ∑ a, w a * F
a))`. -/
theorem sum_smul_sub_smul_sub_apply_mul {α : Type} [Fintype α] (c b : ℂ) (r u w : α → ℂ)
    (F : α → ℂ) :
    ∑ a, (c • (r - b • (u - w))) a * F a
      = c * (∑ a, r a * F a - b * (∑ a, u a * F a - ∑ a, w a * F a)) := by
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ ↦ by ring

/-- For a finite type `α`, `s : ℂ`, coefficients `c : Fin n → ℕ → ℂ`, functions
`f : Fin n → ℕ → α → ℂ`, a natural `N` and `F : α → ℂ`,
`∑ a, (s • ∑ j, ∑ i ∈ Finset.range N, c j i • f j i) a * F a =
s * ∑ j, ∑ i ∈ Finset.range N, c j i * ∑ a, f j i a * F a`. -/
theorem sum_smul_sum_sum_smul_apply_mul {α : Type} [Fintype α] {n : ℕ} (s : ℂ) (c : Fin n → ℕ → ℂ)
    (f : Fin n → ℕ → α → ℂ) (N : ℕ) (F : α → ℂ) :
    ∑ a, (s • ∑ j, ∑ i ∈ Finset.range N, c j i • f j i) a * F a
      = s * ∑ j, ∑ i ∈ Finset.range N, c j i * ∑ a, f j i a * F a := by
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun a _ ↦ by ring))

/-- For a finite set `S` in a finite type `J` and a real `x` with `0 ≤ x`,
`∑ j, (if j ∈ S then √x else 0) ^ 2 = S.card * x`, the sum being over all `j : J`. -/
theorem sum_sq_ite_mem {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) {x : ℝ} (hx : 0 ≤ x) :
    ∑ j, (if j ∈ S then Real.sqrt x else 0) ^ 2 = (S.card : ℝ) * x := by
  have : ∀ j, (if j ∈ S then Real.sqrt x else 0) ^ 2 = if j ∈ S then x else 0 := by
    intro j
    split_ifs
    · exact Real.sq_sqrt hx
    · ring
  simp only [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- For a real family `κ` indexed by `Fin k`, the sum of squares `∑ i, κ i ^ 2` is nonnegative. -/
theorem sum_sq_nonneg {k : ℕ} (κ : Fin k → ℝ) : 0 ≤ ∑ i, κ i ^ 2 :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- For a finite type `n`, a finite set `Js`, `y : n → ℂ`, `wv : ℂ`, `fp : J → ℂ` and
`φp : n → J → ℂ`,
`∑ i, star (y i) * (wv * ∑ j ∈ Js, fp j * conj (φp i j)) = wv * ∑ j ∈ Js, fp j * conj (∑ i, y i * φp
i j)`. -/
theorem sum_star_mul_sum_mul_conj_eq {n : Type*} {J : Type*} [Fintype n] (Js : Finset J) (y : n → ℂ)
    (wv : ℂ) (fp : J → ℂ) (φp : n → J → ℂ) :
    ∑ i, star (y i) * (wv * ∑ j ∈ Js, fp j * (starRingEnd ℂ) (φp i j))
      = wv * ∑ j ∈ Js, fp j * (starRingEnd ℂ) (∑ i, y i * φp i j) := by
  simp_rw [map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Complex.star_def]
  ring

/-- A sum over the elements of a one-element finite set of integers has one term. If `s = {n}`, `f`
is defined on the elements of `s` with values in an additive commutative monoid, and `f x = y`
whenever `(x : ℤ) = n`, then `∑ x, f x = y`. -/
theorem sum_subtype_eq_of_eq_singleton {s : Finset ℤ} {n : ℤ} (hs : s = {n}) {β : Type*}
    [AddCommMonoid β] (f : ↥s → β) (y : β)
    (hf : ∀ x : ↥s, (x : ℤ) = n → f x = y) : ∑ x, f x = y := by
  subst hs
  have e : ∀ x : ↥({n} : Finset ℤ), f x = y := fun x ↦ hf x (Finset.mem_singleton.1 x.2)
  rw [Finset.sum_congr rfl fun x _ ↦ e x, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    Finset.card_singleton, one_smul]

/-- In a fourfold finite sum with values in an additive commutative monoid, the outer pair of sums
can be exchanged with the inner pair:
`∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, f a b c
d`. The proof applies `Finset.sum_comm` four times. -/
theorem sum_sum_comm_sum_sum {A C E F M : Type*} [AddCommMonoid M] (s : Finset A) (t : Finset C)
    (u : Finset E)
    (v : Finset F) (f : A → C → E → F → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t,
        f a b c d := by
  calc _ = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, f a b c d :=
        Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
  _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ v, f a b c d := Finset.sum_comm
  _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, f a b c d :=
        Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun a _ ↦ Finset.sum_comm
  _ = _ := Finset.sum_congr rfl fun c _ ↦ Finset.sum_comm

/-- For a real-valued `F`, `∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, ∑ c' ∈ sc, F a b c c' = ∑ c ∈ sc, ∑ c' ∈
sc, ∑ a ∈ sa, ∑ b ∈ sb, F a b c c'`. So in a fourfold finite sum whose two inner sums run over the
same finite set, the outer pair of sums can be exchanged with the inner pair. The proof applies
`Finset.sum_comm` four times. A case of `PDE.Analysis.sum_sum_comm_sum_sum`. -/
theorem sum_sum_comm_sum_sum_real {A B C : Type*} (sa : Finset A) (sb : Finset B) (sc : Finset C)
    (F : A → B → C → C → ℝ) :
    ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, ∑ c' ∈ sc, F a b c c' = ∑ c ∈ sc, ∑ c' ∈ sc, ∑ a ∈ sa, ∑ b ∈ sb,
        F a b c c' :=
  sum_sum_comm_sum_sum sa sb sc sc F

/-- For finite sets `Pg g` of `ℤ × ℤ` indexed by `g : Fin N`, all contained in a finite set `L`, and
real numbers `a g ι`, `∑ g, ∑ ι' ∈ Pg g, a g ι' = ∑ ι ∈ L, ∑ g, (if ι ∈ Pg g then a g ι else 0)`. -/
theorem sum_sum_eq_sum_sum_ite_mem {N : ℕ} (Pg : Fin N → Finset (ℤ × ℤ)) (L : Finset (ℤ × ℤ))
    (hsub : ∀ g, Pg g ⊆ L)
    (a : Fin N → ℤ × ℤ → ℝ) :
    ∑ g, ∑ ι' ∈ Pg g, a g ι' = ∑ ι ∈ L, ∑ g, (if ι ∈ Pg g then a g ι else 0) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun g _ ↦ ?_)
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (hsub g)]

/-- For `f : ℕ → ℕ → ℂ`,
`∑ j : Fin N, ∑ l : Fin N, f j l = ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, f j l`. -/
theorem sum_sum_fin_eq_sum_sum_range {N : ℕ} (f : ℕ → ℕ → ℂ) :
    ∑ j : Fin N, ∑ l : Fin N, f j l = ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N, f j l := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ ∑ l : Fin N, f j l)]
  exact Finset.sum_congr rfl (fun j _ ↦ Fin.sum_univ_eq_sum_range (f j) N)

/-- Let `P'` be a finite set of `ℤ × ℤ`, `L` a finite set of integers, `s` an integer and
`g : ℤ × ℤ → ℝ` nonnegative on `P'`. Then
`∑ l ∈ L, ∑ n₂ ∈ (P'.filter (fun ι ↦ ι.2 = l + s)).image Prod.fst, g (n₂, l + s) ≤ ∑ ι ∈ P', g
ι`. Each `ι ∈ P'` is counted at most once on the left, namely for `l = ι.2 -
s` when this lies in `L`. -/
theorem sum_sum_image_fst_le_sum (P' : Finset (ℤ × ℤ)) (L : Finset ℤ) (s : ℤ) (g : ℤ × ℤ → ℝ)
    (hg : ∀ ι ∈ P', 0 ≤ g ι) :
    ∑ l ∈ L, ∑ n₂ ∈ (P'.filter (fun ι ↦ ι.2 = l + s)).image Prod.fst, g (n₂, l + s) ≤ ∑ ι ∈ P',
        g ι := by
  have e : ∀ l, ∑ n₂ ∈ (P'.filter (fun ι ↦ ι.2 = l + s)).image Prod.fst, g (n₂, l + s)
      = ∑ ι ∈ P', if ι.2 - s = l then g ι else 0 := by
    intro l
    rw [Finset.sum_image, ← Finset.sum_filter]
    · refine Finset.sum_congr (Finset.filter_congr (fun ι _ ↦ by omega)) (fun ι hι ↦ ?_)
      rw [Finset.mem_filter] at hι
      have : ι.2 = l + s := by omega
      rw [← this]
    · intro a ha b hb hab
      rw [Finset.coe_filter] at ha hb
      exact Prod.ext hab (ha.2.trans hb.2.symm)
  simp only [e]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun ι hι ↦ ?_)
  rw [Finset.sum_ite_eq]
  split_ifs
  · exact le_rfl
  · exact hg ι hι

/-- For `f : Fin 3 → Fin 3 → ℂ` and `a b : Fin 3`, the double sum over `a'` and `b'` in `Fin 3` of
`(if a' = a ∧ b' = b then 1 else 0) * f a' b'` equals `f a b`. -/
theorem sum_sum_ite_and_eq_mul (f : Fin 3 → Fin 3 → ℂ) (a b : Fin 3) :
    ∑ a' : Fin 3, ∑ b' : Fin 3, (if a' = a ∧ b' = b then (1 : ℂ) else 0) * f a' b' = f a b := by
  simp [ite_and]

/-- For a finite type `n`, a map `L : n → κ` with all values in the finite set `T`, and
`F : κ → n → ℂ`, `∑ ℓ ∈ T, ∑ i, (if L i = ℓ then F ℓ i else 0) = ∑ i, F (L i) i`. -/
theorem sum_sum_ite_eq_sum_of_mem {n κ : Type*} [Fintype n] [DecidableEq κ] (L : n → κ)
    (T : Finset κ) (hL : ∀ i, L i ∈ T)
    (F : κ → n → ℂ) : ∑ ℓ ∈ T, ∑ i, (if L i = ℓ then F ℓ i else 0) = ∑ i, F (L i) i := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [Finset.sum_ite_eq T (L i) (fun ℓ ↦ F ℓ i), ite_eq_left (hL i)]

/-- For finite sets `s`, `t` of integers, a finite set `u` of natural numbers and real-valued `f`,
`g`, the sum `∑ j ∈ u, ∑ l ∈ u, (if d < max j l then ∑ n ∈ s, f n j l + ∑ n ∈ t, g n j l else 0)`
equals `(∑ n ∈ s, ∑ j ∈ u, ∑ l ∈ u, if d < max j l then f n j l else 0) + ∑ n ∈ t, ∑ j ∈ u, ∑ l ∈ u,
if d < max j l then g n j l else
0`. The proof commutes the sums and moves the condition outside the sums over `n`. -/
theorem sum_sum_ite_sum_add_sum_eq (d : ℕ) (s t : Finset ℤ) (u : Finset ℕ) (f g : ℤ → ℕ → ℕ → ℝ) :
    ∑ j ∈ u, ∑ l ∈ u, (if d < max j l then ∑ n ∈ s, f n j l + ∑ n ∈ t, g n j l else 0) =
      (∑ n ∈ s, ∑ j ∈ u, ∑ l ∈ u, if d < max j l then f n j l else 0)
        + ∑ n ∈ t, ∑ j ∈ u, ∑ l ∈ u, if d < max j l then g n j l else 0 := by
  have h1 : ∀ (h : ℤ → ℕ → ℕ → ℝ) (w : Finset ℤ), ∑ n ∈ w, ∑ j ∈ u, ∑ l ∈ u,
      (if d < max j l then h n j l else 0)
      = ∑ j ∈ u, ∑ l ∈ u, if d < max j l then ∑ n ∈ w, h n j l else 0 := by
    intro h w
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ ↦ ?_)
    split_ifs <;> simp
  rw [h1, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ ↦ ?_)
  split_ifs <;> simp

/-- For `q : Fin k → ℝ` and `f : Fin k → Fin k → E` with values in a real vector space `E`:
`∑ i, ∑ m, (q i * q m) • f i m = ∑ i, ∑ m ∈ Finset.Ici i, (q i * q m) • (if i = m then f i i else f
i m + f m i)`, a sum over the pairs `i ≤ m`. The proof splits each inner sum into the parts `i ≤
m` and `m < i` and swaps the order of summation in the second part. -/
theorem sum_sum_smul_eq_sum_sum_Ici {k : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (q : Fin k → ℝ) (f : Fin k → Fin k → E) :
    ∑ i, ∑ m, (q i * q m) • f i m =
      ∑ i, ∑ m ∈ Finset.Ici i, (q i * q m) • (if i = m then f i i else f i m + f m i) := by
  have hsplit : ∀ i : Fin k, ∑ m, (q i * q m) • f i m =
      ∑ m ∈ Finset.Ici i, (q i * q m) • f i m + ∑ m ∈ Finset.Iio i, (q i * q m) • f i m := by
    intro i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun m ↦ i ≤ m)]
    congr 1
    · apply Finset.sum_congr _ (fun _ _ ↦ rfl)
      ext m; simp
    · apply Finset.sum_congr _ (fun _ _ ↦ rfl)
      ext m; simp
  have hswap : ∑ i : Fin k, ∑ m ∈ Finset.Iio i, (q i * q m) • f i m =
      ∑ i : Fin k, ∑ m ∈ Finset.Ioi i, (q m * q i) • f m i := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun m ↦ Finset.Ioi m)]
    intro x y
    simp
  have hdiag : ∀ i : Fin k, ∑ m ∈ Finset.Ici i, (q i * q m) •
      (if i = m then f i i else f i m + f m i) =
      (q i * q i) • f i i + ∑ m ∈ Finset.Ioi i, (q i * q m) • (f i m + f m i) := by
    intro i
    rw [← Finset.insert_Ioi, Finset.sum_insert (by simp), ite_eq_left rfl]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    rw [ite_eq_right (ne_of_lt (Finset.mem_Ioi.mp hm))]
  have hdiag' : ∀ i : Fin k, ∑ m ∈ Finset.Ici i, (q i * q m) • f i m =
      (q i * q i) • f i i + ∑ m ∈ Finset.Ioi i, (q i * q m) • f i m := by
    intro i
    rw [← Finset.insert_Ioi, Finset.sum_insert (by simp)]
  simp only [hsplit, Finset.sum_add_distrib, hswap, hdiag, hdiag', smul_add, mul_comm (q _) (q _)]
  abel

/-- For finite sets of integers `t ⊆ s` and a real-valued `F`,
`∑ n ∈ s, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, (if n ∈ t then F n j l else 0) = ∑ n ∈ t, ∑ j
∈ Finset.range m, ∑ l ∈ Finset.range m, F n j l`. -/
theorem sum_sum_sum_ite_mem_of_subset (s t : Finset ℤ) (hts : t ⊆ s) (F : ℤ → ℕ → ℕ → ℝ) (m : ℕ) :
    (∑ n ∈ s, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, if n ∈ t then F n j l else 0)
      = ∑ n ∈ t, ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, F n j l := by
  have e : ∀ n, (∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, if n ∈ t then F n j l else 0)
      = if n ∈ t then ∑ j ∈ Finset.range m, ∑ l ∈ Finset.range m, F n j l else 0 := by
    intro n; split_ifs <;> simp
  simp only [e]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hts]

/-- For a finite type `ι`, `g : ι → Fin 3 → Fin 3 → ℂ` and `u : ι → ℂ`,
`∑ e, (∑ i, ∑ q, g e i q) * u e = ∑ i, ∑ q, ∑ e, g e i q * u e`. The factor `u e` is distributed
over the inner sums and the sum over `e` is moved inside. -/
theorem sum_sum_sum_mul_comm {ι : Type} [Fintype ι] (g : ι → Fin 3 → Fin 3 → ℂ) (u : ι → ℂ) :
    ∑ e, (∑ i : Fin 3, ∑ q : Fin 3, g e i q) * u e =
      ∑ i : Fin 3, ∑ q : Fin 3, ∑ e, g e i q * u e := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_comm]

/-- For disjoint finite sets `Bd` and `Dd` of integer pairs, `g : ℤ × ℤ → (Fin 12 → ℂ) → ℝ` and
`B Dv : ℤ × ℤ → Fin 12 → ℂ`,
`∑ ι ∈ Bd ∪ Dd, g ι (if ι ∈ Bd then B ι else Dv ι) = ∑ ι ∈ Bd, g ι (B ι) + ∑ ι ∈ Dd, g ι (Dv ι)`. -/
theorem sum_union_ite_mem_of_disjoint {Bd Dd : Finset (ℤ × ℤ)} (h : Disjoint Bd Dd)
    (g : ℤ × ℤ → (Fin 12 → ℂ) → ℝ)
    (B Dv : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ Bd ∪ Dd, g ι (if ι ∈ Bd then B ι else Dv ι) = ∑ ι ∈ Bd, g ι (B ι) + ∑ ι ∈ Dd,
        g ι (Dv ι) := by
  classical
  rw [Finset.sum_union h]
  congr 1
  · exact Finset.sum_congr rfl fun ι hι ↦ by rw [ite_eq_left hι]
  · exact Finset.sum_congr rfl fun ι hι ↦ by
      rw [ite_eq_right (fun hB ↦ Finset.disjoint_left.1 h hB hι)]

/-- For pairwise disjoint finite sets `Rs`, `Bd`, `Dd` of integer pairs,
`g : ℤ × ℤ → (Fin 12 → ℂ) → ℝ` and `O B Dv : ℤ × ℤ → Fin 12 → ℂ`, the sum over `ι ∈ Rs ∪ Bd ∪ Dd` of
`g ι (if ι ∈ Rs then O ι else if ι ∈ Bd then B ι else Dv ι)` equals
`∑ ι ∈ Rs, g ι (O ι) + ∑ ι ∈ Bd, g ι (B ι) + ∑ ι ∈ Dd, g ι (Dv ι)`. The proof splits the sum over
the disjoint union and evaluates the conditional on each part. -/
theorem sum_union_union_ite_mem_of_disjoint {Rs Bd Dd : Finset (ℤ × ℤ)} (h1 : Disjoint Rs Bd)
    (h2 : Disjoint Rs Dd) (h3 : Disjoint Bd Dd)
    (g : ℤ × ℤ → (Fin 12 → ℂ) → ℝ) (O B Dv : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ Rs ∪ Bd ∪ Dd, g ι (if ι ∈ Rs then O ι else if ι ∈ Bd then B ι else Dv ι)
      = ∑ ι ∈ Rs, g ι (O ι) + ∑ ι ∈ Bd, g ι (B ι) + ∑ ι ∈ Dd, g ι (Dv ι) := by
  classical
  rw [Finset.sum_union (Finset.disjoint_union_left.2 ⟨h2, h3⟩), Finset.sum_union h1]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun ι hι ↦ by rw [ite_eq_left hι]
    · exact Finset.sum_congr rfl fun ι hι ↦ by
        rw [ite_eq_right (fun hR ↦ Finset.disjoint_left.1 h1 hR hι), ite_eq_left hι]
  · exact Finset.sum_congr rfl fun ι hι ↦ by
      rw [ite_eq_right (fun hR ↦ Finset.disjoint_left.1 h2 hR hι),
          ite_eq_right (fun hB ↦ Finset.disjoint_left.1 h3 hB hι)]

/-- If `c : ℕ → ℕ → ℝ` satisfies `0 < c j j` for every `j`, then for each natural number `a` there
are a finite set `s` of natural numbers and coefficients `d : ℕ → ℝ` such that
`r ^ a = ∑ j ∈ s, d j * ∑ i ∈ Finset.range (j + 1), c j i * r ^ i` for all real `r`. -/
theorem exists_finset_pow_eq_sum_triangular (c : ℕ → ℕ → ℝ) (hc : ∀ j, 0 < c j j) (a : ℕ) :
    ∃ s : Finset ℕ, ∃ d : ℕ → ℝ, ∀ r : ℝ, r ^ a =
      ∑ j ∈ s, d j * ∑ i ∈ Finset.range (j + 1), c j i * r ^ i := by
  obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp
      (pow_mem_span_triangular_of_diag_pos c hc a)
  refine ⟨d.support, d, fun r ↦ ?_⟩
  have := congrFun hd r
  rw [← this, Finsupp.sum, Finset.sum_apply]
  rfl

/-- Expansion of an interval-additive functional `J : ℝ → ℝ → (ℝ → ℝ) → ℂ` over a subdivision.
Suppose `J a b f = J a m f + J m b f` for `lo ≤ a ≤ m ≤ b` and continuous `f`, `J a b` is additive
on continuous functions for `lo ≤ a` and satisfies `J a b (fun s ↦ w * f s) = w * J a b f` for real
`w`, and the intervals from `tlo j` to `thi j`, `j : Fin N` with `0 < N`, satisfy `tlo j < thi j`,
start at `lo`, end at `hi`, and each ends where the next begins. If `T` is continuous and
`T s = ∑ i ∈ Finset.range (tdeg + 1), coef j i * g j i s` for all `j` and `s`, with every `g j i`
continuous, then `J lo hi T = ∑ j, ∑ i ∈ Finset.range (tdeg + 1), coef j i * J (tlo j) (thi j) (g j
i)`. -/
theorem interval_functional_eq_sum_sum_mul (J : ℝ → ℝ → (ℝ → ℝ) → ℂ) {lo hi : ℝ}
    (hadd : ∀ a m b, lo ≤ a → a ≤ m → m ≤ b → ∀ f, Continuous f → J a b f = J a m f + J m b f)
    (hlin : ∀ a b, lo ≤ a → ∀ f g, Continuous f → Continuous g → J a b (fun s ↦ f s + g s) =
        J a b f + J a b g)
    (hsmul : ∀ a b (w : ℝ) f, J a b (fun s ↦ w * f s) = (w : ℂ) * J a b f)
    {N : ℕ} (tlo thi : Fin N → ℝ) (hN : 0 < N) (hlt : ∀ j, tlo j < thi j)
    (hadj : ∀ j j' : Fin N, j.val + 1 = j'.val → thi j = tlo j')
    (hfirst : ∀ j : Fin N, j.val = 0 → tlo j = lo) (hlast : ∀ j : Fin N, j.val + 1 = N → thi j = hi)
    (T : ℝ → ℝ) (hT : Continuous T) (tdeg : ℕ) (coef : Fin N → ℕ → ℝ) (g : Fin N → ℕ → ℝ → ℝ)
    (hg : ∀ j i, Continuous (g j i)) (hid : ∀ j s, T s = ∑ i ∈ Finset.range (tdeg + 1),
        coef j i * g j i s) :
    J lo hi T = ∑ j, ∑ i ∈ Finset.range (tdeg + 1), (coef j i : ℂ) * J (tlo j) (thi j) (g j i) := by
  obtain ⟨hs, hle⟩ := eq_sum_fin_of_additive_of_adjacent (fun a b ↦ J a b T)
      (fun a m b ha h1 h2 ↦ hadd a m b ha h1 h2 T hT)
    tlo thi hN hlt hadj hfirst hlast
  have hs' : J lo hi T = ∑ j, J (tlo j) (thi j) T := hs
  rw [hs']
  refine Finset.sum_congr rfl (fun j _ ↦ ?_)
  have hT' : T = fun s ↦ ∑ i ∈ Finset.range (tdeg + 1), coef j i * g j i s := funext (hid j)
  rw [hT']
  exact map_sum_range_of_additive_on_continuous (J (tlo j) (thi j)) (hlin _ _ (hle j)) (hsmul _ _)
      (coef j) (g j) (hg j) tdeg

/-- Cauchy-Schwarz inequality for `x y b c : Fin 3 → ℝ`:
`(∑ l, (x l * b l + y l * c l)) ^ 2 ≤ (∑ l, (x l ^ 2 + y l ^ 2)) * ∑ l, (b l ^ 2 + c l ^ 2)`. -/
theorem sq_sum_three_mul_add_mul_le (x y b c : Fin 3 → ℝ) :
    (∑ l : Fin 3, (x l * b l + y l * c l)) ^ 2 ≤
      (∑ l : Fin 3, (x l ^ 2 + y l ^ 2)) * ∑ l : Fin 3, (b l ^ 2 + c l ^ 2) := by
  have h := sq_sum_three_mul_sub_mul_le x y b (fun l ↦ -c l)
  simp only [mul_neg, sub_neg_eq_add, neg_sq] at h
  rw [Finset.sum_congr rfl (fun l _ ↦ add_comm (c l ^ 2) (b l ^ 2))] at h
  exact h

/-- Regroups a filtered sum over `H : Finset (ℤ × ℤ)` into `N` groups given by finite sets `U j` and
`T j`: `∑ α ∈ H, (if keep (ℓ - α) then F α else 0) = ∑ j, ∑ ι ∈ T j, (if ℓ - ι ∈ U j then F (ℓ - ι)
else 0)`, for `F` with values in an additive commutative monoid. It is assumed that each `U j` is
contained in `H`, that no element lies in two different `U j`, that `keep` holds on every `T j`, and
that every `α ∈ H` with `keep (ℓ - α)` and `F α ≠ 0` has an index `j` with `ℓ - α ∈ T j` and
`α ∈ U j`. The proof changes variables `α = ℓ - ι` in each inner sum, exchanges the two sums, and
checks that for each `α` at most one `j` contributes. -/
theorem sum_ite_eq_sum_sum_of_disjoint {β : Type*} [AddCommMonoid β] (ℓ : ℤ × ℤ)
    (H : Finset (ℤ × ℤ))
    (keep : ℤ × ℤ → Prop) [DecidablePred keep] {N : ℕ} (U T : Fin N → Finset (ℤ × ℤ))
        (F : ℤ × ℤ → β)
    (hcover : ∀ α ∈ H, keep (ℓ - α) → F α ≠ 0 → ∃ j, ℓ - α ∈ T j ∧ α ∈ U j)
    (hdisj : ∀ j j' α, α ∈ U j → α ∈ U j' → j = j')
    (hkeep : ∀ j ι, ι ∈ T j → keep ι)
    (hsub : ∀ j α, α ∈ U j → α ∈ H) :
    ∑ α ∈ H, (if keep (ℓ - α) then F α else 0)
      = ∑ j, ∑ ι ∈ T j, (if ℓ - ι ∈ U j then F (ℓ - ι) else 0) := by
  classical
  simp only [fun j ↦ sum_ite_sub_mem_eq_sum_ite ℓ H (T j) (U j) F (hsub j)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun α hα ↦ ?_)
  by_cases hk : keep (ℓ - α)
  · rw [ite_eq_left hk]
    by_cases hf : F α = 0
    · rw [hf]
      exact (Finset.sum_eq_zero (fun j _ ↦ ite_self _)).symm
    obtain ⟨j0, hT0, hU0⟩ := hcover α hα hk hf
    rw [Finset.sum_eq_single j0 (fun j _ hj ↦ ite_eq_right (fun h ↦ hj (hdisj j j0 α h.1 hU0)))
      (fun h ↦ absurd (Finset.mem_univ j0) h), ite_eq_left ⟨hU0, hT0⟩]
  · rw [ite_eq_right hk]
    exact (Finset.sum_eq_zero (fun j _ ↦ ite_eq_right (fun h ↦ hk (hkeep j _ h.2)))).symm

/-- For a finite type `n`, `κ : n → ℝ`, `a b : n → Fin 3 → ℂ` and `0 ≤ w`,
`w * ∑ c, ‖∑ l, (κ l : ℂ) * (a l c - b l c)‖ ^ 2 ≤ (∑ l, κ l ^ 2) * (w * ∑ l, ∑ c, ‖a l c - b l c‖ ^
2)`. The proof applies the Cauchy-Schwarz inequality for each `c` and sums over `c`. -/
theorem sum_norm_sum_mul_sub_sq_le {n : Type*} [Fintype n] (κ : n → ℝ) (a b : n → Fin 3 → ℂ) {w : ℝ}
    (hw : 0 ≤ w) :
    w * ∑ c, ‖∑ l, (κ l : ℂ) * (a l c - b l c)‖ ^ 2
      ≤ (∑ l, κ l ^ 2) * (w * ∑ l, ∑ c, ‖a l c - b l c‖ ^ 2) := by
  have h : ∀ c, ‖∑ l, (κ l : ℂ) * (a l c - b l c)‖ ^ 2 ≤ (∑ l, κ l ^ 2) * ∑ l,
      ‖a l c - b l c‖ ^ 2 :=
    fun c ↦ norm_sum_ofReal_mul_sq_le Finset.univ κ (fun l ↦ a l c - b l c)
  have h2 := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) ↦ h c)
  rw [← Finset.mul_sum, Finset.sum_comm] at h2
  calc w * ∑ c, ‖∑ l, (κ l : ℂ) * (a l c - b l c)‖ ^ 2
      ≤ w * ((∑ l, κ l ^ 2) * ∑ l, ∑ c, ‖a l c - b l c‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hw
    _ = (∑ l, κ l ^ 2) * (w * ∑ l, ∑ c, ‖a l c - b l c‖ ^ 2) := by ring

/-- For natural numbers `M ≤ N` and `Y : ℕ → ℝ`,
`∑ j ∈ range N, (if j < M then 1 else 0) * Y j = ∑ j ∈ range M, Y j`. The proof writes the indicator
of `j < M` as one minus the indicator of `M ≤ j`. -/
theorem sum_range_ite_lt_mul_eq_sum (M N : ℕ) (h : M ≤ N) (Y : ℕ → ℝ) :
    ∑ j ∈ range N, (if j < M then (1 : ℝ) else 0) * Y j = ∑ j ∈ range M, Y j := by
  have e : ∀ j, (if j < M then (1 : ℝ) else 0) * Y j = Y j - (if M ≤ j then (1 : ℝ) else 0) *
      Y j := by
    intro j
    by_cases h1 : j < M
    · rw [ite_eq_left h1, ite_eq_right (by omega)]; ring
    · rw [ite_eq_right h1, ite_eq_left (by omega)]; ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, sum_range_ite_le_mul_eq_sub M N h]
  ring

/-- Let `Q ≥ 2` and `f g : ℕ → ℕ → ℝ`. The sum of `f j l` over the pairs `(j, l)` of
`Fin (Q + 1) × Fin (Q + 1)` with `Q - 1 ≤ j`, plus the sum of `g j l` over the pairs with
`j ≤ Q - 1` and `Q - 1 ≤ l` (both written with factors `if ... then 1 else 0`), equals
`(∑ j ∈ range (Q + 1), ∑ l ∈ range (Q + 1), f j l - ∑ j ∈ range (Q - 2 + 1), ∑ l ∈ range (Q + 1), f
j l) + (∑ j ∈ range (Q - 1 + 1), ∑ l ∈ range (Q + 1), g j l - ∑ j ∈ range (Q - 1 + 1), ∑ l ∈ range
(Q - 2 + 1), g j
l)`. The proof turns the sums over pairs into double sums over ranges and writes each indicator sum
as a difference of range sums. -/
theorem sum_fin_prod_ite_eq_range_sub (Q : ℕ) (hQ : 2 ≤ Q) (f g : ℕ → ℕ → ℝ) :
    (∑ jl : Fin (Q + 1) × Fin (Q + 1), (if Q - 1 ≤ (jl.1 : ℕ) then (1 : ℝ) else 0) * f jl.1 jl.2)
      + (∑ jl : Fin (Q + 1) × Fin (Q + 1),
          (if (jl.1 : ℕ) ≤ Q - 1 ∧ Q - 1 ≤ (jl.2 : ℕ) then (1 : ℝ) else 0) * g jl.1 jl.2)
    = (∑ j ∈ range (Q + 1), ∑ l ∈ range (Q + 1), f j l - ∑ j ∈ range (Q - 2 + 1),
        ∑ l ∈ range (Q + 1), f j l)
      + (∑ j ∈ range (Q - 1 + 1), ∑ l ∈ range (Q + 1), g j l
          - ∑ j ∈ range (Q - 1 + 1), ∑ l ∈ range (Q - 2 + 1), g j l) := by
  have e1 : Q - 2 + 1 = Q - 1 := by omega
  have e2 : Q - 1 + 1 = Q := by omega
  rw [e1, e2, sum_fin_prod_fin_eq_sum_range (Q + 1) (Q + 1)
      (fun j l ↦ (if Q - 1 ≤ j then (1 : ℝ) else 0) * f j l),
    sum_fin_prod_fin_eq_sum_range (Q + 1) (Q + 1) (fun j l ↦
        (if j ≤ Q - 1 ∧ Q - 1 ≤ l then (1 : ℝ) else 0) * g j l)]
  have e3 : ∀ j l, (if j ≤ Q - 1 ∧ Q - 1 ≤ l then (1 : ℝ) else 0) * g j l
      = (if j < Q then (1 : ℝ) else 0) * ((if Q - 1 ≤ l then (1 : ℝ) else 0) * g j l) := by
    intro j l
    by_cases h1 : j < Q <;> by_cases h2 : Q - 1 ≤ l
    · rw [ite_eq_left ⟨by omega, h2⟩, ite_eq_left h1, ite_eq_left h2]; ring
    · rw [ite_eq_right (fun h ↦ h2 h.2), ite_eq_left h1, ite_eq_right h2]; ring
    · rw [ite_eq_right (fun h ↦ h1 (by omega)), ite_eq_right h1]; ring
    · rw [ite_eq_right (fun h ↦ h1 (by omega)), ite_eq_right h1]; ring
  simp_rw [e3]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_range_ite_le_mul_eq_sub (Q - 1) (Q + 1) (by omega)]
  rw [sum_range_ite_lt_mul_eq_sum Q (Q + 1) (by omega), Finset.sum_sub_distrib]

/-- Let `J : (ℝ → ℝ) → ℂ` satisfy `J (fun s ↦ f s + g s) = J f + J g` for continuous `f`, `g` and
`J (fun s ↦ w * f s) = (w : ℂ) * J f` for all real `w` and all `f`. If `G p` is continuous for
every entry `p` of a list `l`, then
`J (fun s ↦ (l.map (fun p ↦ G p s)).sum) = (l.map (fun p ↦ J (G p))).sum`. Proof idea: induction
on the list; the empty case uses that `J` vanishes on the zero function, by homogeneity with
`w = 0`. -/
theorem map_list_sum_of_additive_on_continuous {β : Type*} (J : (ℝ → ℝ) → ℂ)
    (hlin : ∀ f g, Continuous f → Continuous g → J (fun s ↦ f s + g s) = J f + J g)
    (hsmul : ∀ (w : ℝ) f, J (fun s ↦ w * f s) = (w : ℂ) * J f)
    (l : List β) (G : β → ℝ → ℝ) (hG : ∀ p ∈ l, Continuous (G p)) :
    J (fun s ↦ (l.map (fun p ↦ G p s)).sum) = (l.map (fun p ↦ J (G p))).sum := by
  induction l with
  | nil =>
    have := hsmul 0 (fun _ ↦ 0)
    simp only [zero_mul, Complex.ofReal_zero] at this
    simpa using this
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hlin _ _ (hG p List.mem_cons_self) (continuous_list_sum ps
        (fun q hq ↦ hG q (List.mem_cons_of_mem _ hq))),
      ih (fun q hq ↦ hG q (List.mem_cons_of_mem _ hq))]

/-- For a real `w`, a complex `f`, a finite set `T` of pairs of naturals, `c : ℕ × ℕ → ℂ` and
`b : ℕ × ℕ → ℝ`, `w * ‖f - ∑ i ∈ T, c i * (b i : ℂ)‖ ^ 2 = w * ‖f‖ ^ 2 - 2 * ∑ i ∈ T, (conj (c i) *
((w : ℂ) * f * (b i : ℂ))).re + ∑ i ∈ T, ∑ i' ∈ T, (c i * conj (c i')).re * (w * b i * b
i')`. The proof expands `(f - P) * conj (f - P)` for the combination `P = ∑ i ∈ T, c i * (b i :
ℂ)` and takes real parts term by term. -/
theorem mul_norm_sub_sum_mul_sq_eq (w : ℝ) (f : ℂ) (T : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ)
    (b : ℕ × ℕ → ℝ) :
    w * ‖f - ∑ i ∈ T, c i * (b i : ℂ)‖ ^ 2 =
      w * ‖f‖ ^ 2 - 2 * ∑ i ∈ T, ((starRingEnd ℂ) (c i) * ((w : ℂ) * f * (b i : ℂ))).re
        + ∑ i ∈ T, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re * (w * b i * b i') := by
  set P := ∑ i ∈ T, c i * (b i : ℂ) with hPdef
  have e1 : (f - P) * (starRingEnd ℂ) (f - P) = f * (starRingEnd ℂ) f
      - (f * (starRingEnd ℂ) P + (starRingEnd ℂ) (f * (starRingEnd ℂ) P)) + P *
          (starRingEnd ℂ) P := by
    simp only [map_sub, map_mul, Complex.conj_conj]; ring
  have e2 : (f * (starRingEnd ℂ) P).re = ∑ i ∈ T, b i * ((starRingEnd ℂ) (c i) * f).re := by
    rw [hPdef, map_sum, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, Complex.conj_ofReal, show f * ((starRingEnd ℂ) (c i) * (b i : ℂ))
      = (b i : ℂ) * ((starRingEnd ℂ) (c i) * f) by ring, Complex.re_ofReal_mul]
  have e3 : (P * (starRingEnd ℂ) P).re
      = ∑ i ∈ T, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re * (b i * b i') := by
    rw [hPdef, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i' _ ↦ ?_
    rw [map_mul, Complex.conj_ofReal, show c i * (b i : ℂ) * ((starRingEnd ℂ) (c i') * (b i' : ℂ))
      = ((b i * b i' : ℝ) : ℂ) * (c i * (starRingEnd ℂ) (c i')) by
        push_cast; ring, Complex.re_ofReal_mul]
    ring
  have e4 : ∀ i, ((starRingEnd ℂ) (c i) * ((w : ℂ) * f * (b i : ℂ))).re
      = w * (b i * ((starRingEnd ℂ) (c i) * f).re) := by
    intro i
    rw [show (starRingEnd ℂ) (c i) * ((w : ℂ) * f * (b i : ℂ))
      = ((w * b i : ℝ) : ℂ) * ((starRingEnd ℂ) (c i) * f) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  have e5 : ∑ i ∈ T, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re * (w * b i * b i')
      = w * ∑ i ∈ T, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re * (b i * b i') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ ↦ by ring
  rw [sq_norm_eq_re_mul_conj (f - P), sq_norm_eq_re_mul_conj f, e1, Complex.add_re, Complex.sub_re,
      Complex.add_re, Complex.conj_re, e3,
      e2, e5]
  simp only [e4, ← Finset.mul_sum]
  ring

/-- For a finite type `n`, `a b : n → Fin 3 → ℂ` and `0 ≤ w`,
`w * ∑ l, ∑ c, ‖a l c - b l c‖ ^ 2 ≤ ∑ l, ∑ c, (2 * (w * ‖a l c‖ ^ 2) + 2 * (w * ‖b l c‖ ^ 2))`. -/
theorem mul_sum_sum_norm_sub_sq_le {n : Type*} [Fintype n] (a b : n → Fin 3 → ℂ) {w : ℝ}
    (hw : 0 ≤ w) :
    w * ∑ l, ∑ c, ‖a l c - b l c‖ ^ 2
      ≤ ∑ l, ∑ c, (2 * (w * ‖a l c‖ ^ 2) + 2 * (w * ‖b l c‖ ^ 2)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ ↦ ?_
  have := mul_le_mul_of_nonneg_left (norm_sub_sq_le_two_mul (a l c) (b l c)) hw
  linarith

/-- Let `N > 0`, and let `∑ k ∈ range N, st k = N * T` for complex `st k`, and
`∑ k ∈ range N, cu k = N * X`, `∑ k ∈ range N, cy k = N * Y` for real `cu k`, `cy k`. If
`2 * ‖st k‖ ≤ β * cu k + β⁻¹ * cy k` for every `k`, then `2 * ‖T‖ ≤ β * X + β⁻¹ * Y`. By the
triangle inequality for the sum, then division by `N`. -/
theorem two_mul_norm_le_of_sum_eq (N : ℕ) (hN : 0 < N) (T : ℂ) (st : ℕ → ℂ) (cu cy : ℕ → ℝ)
    (β X Y : ℝ)
    (hexp : ∑ k ∈ Finset.range N, st k = N * T) (hpt : ∀ k, 2 * ‖st k‖ ≤ β * cu k + β⁻¹ * cy k)
    (hU : ∑ k ∈ Finset.range N, cu k = N * X) (hY : ∑ k ∈ Finset.range N, cy k = N * Y) :
    2 * ‖T‖ ≤ β * X + β⁻¹ * Y := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) * (2 * ‖T‖) = 2 * ‖∑ k ∈ Finset.range N, st k‖ := by
    rw [hexp, norm_mul, Complex.norm_natCast]
    ring
  have h2 : 2 * ‖∑ k ∈ Finset.range N, st k‖ ≤ ∑ k ∈ Finset.range N, 2 * ‖st k‖ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
  have h3 : ∑ k ∈ Finset.range N, 2 * ‖st k‖ ≤ ∑ k ∈ Finset.range N, (β * cu k + β⁻¹ * cy k) :=
    Finset.sum_le_sum fun k _ ↦ hpt k
  have h4 : ∑ k ∈ Finset.range N, (β * cu k + β⁻¹ * cy k) = N * (β * X + β⁻¹ * Y) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hU, hY]
    ring
  exact le_of_mul_le_mul_left (by linarith) hNpos

/-- For a complex function `f` of four indices in `Fin 3`, the fourfold sum of `f a b a' b'` taken
in the order `a`, `b`, `a'`, `b'` equals the sum taken in the order `a'`, `b'`, `a`, `b`. A case of
`sum_sum_comm_sum_sum`. -/
theorem sum_sum_comm_sum_sum_fin_three (f : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    ∑ a, ∑ b, ∑ a', ∑ b', f a b a' b' = ∑ a', ∑ b', ∑ a, ∑ b, f a b a' b' :=
  sum_sum_comm_sum_sum _ _ _ _ f

/-- For `f`, `g`, `T : ι → ℂ` on a finite type,
`∑ d, (f - g) d * T d = ∑ d, f d * T d - ∑ d, g d * T d`. -/
theorem sum_pi_sub_mul {ι : Type*} [Fintype ι] (f g T : ι → ℂ) :
    ∑ d, (f - g) d * T d = ∑ d, f d * T d - ∑ d, g d * T d := by
  simp [sub_mul, Finset.sum_sub_distrib]

/-- For a finite set `s`, functions `f j : ι → ℂ` and `T : ι → ℂ` on a finite type,
`∑ d, (∑ j ∈ s, f j) d * T d = ∑ j ∈ s, ∑ d, f j d * T d`. -/
theorem sum_pi_finsetSum_mul {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → ℂ) (T : ι → ℂ) :
    ∑ d, (∑ j ∈ s, f j) d * T d = ∑ j ∈ s, ∑ d, f j d * T d := by
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- For a complex `c` and `f`, `T : ι → ℂ` on a finite type,
`∑ d, (c • f) d * T d = c * ∑ d, f d * T d`. -/
theorem sum_pi_smul_mul {ι : Type*} [Fintype ι] (c : ℂ) (f T : ι → ℂ) :
    ∑ d, (c • f) d * T d = c * ∑ d, f d * T d := by
  simp [Finset.mul_sum, mul_assoc]

/-- If `f : Fin 3 → ℝ` satisfies `|f i| ≤ b` for every `i`, then `|∑ i, f i| ≤ 3 * b`. By the
triangle inequality. -/
theorem abs_sum_fin_three_le (f : Fin 3 → ℝ) (b : ℝ) (h : ∀ i, |f i| ≤ b) : |∑ i, f i| ≤ 3 * b := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ ↦ h i).trans ?_)
  simp

end PDE.Analysis
