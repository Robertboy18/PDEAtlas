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

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import PDE.Analysis.Complex.NormSq
public import PDE.Analysis.Scalar.Inequalities
public import PDE.Analysis.Scalar.Inequalities.Basic
public import PDE.Analysis.Scalar.Powers.Basic

set_option linter.style.header false

/-!
# Inequalities between real numbers: bounds of composite expressions

The lemmas bound squares, products, absolute values and fractions of real numbers: Young-type bounds
of a product by squares, bounds of a sum by the sum of the bounds, comparisons of two expressions
under sign conditions. The proofs are long calculations closed by `nlinarith`, `linarith`,
`positivity` or `field_simp`, after case splits.

## Main results

* `PDE.Analysis.abs_sum_five_mul_sq_le`: Let `|cD| ≤ Bd`, `|cZ| ≤ Bz`, `0 ≤ hD`, `hD ≤ K1`,
  `0 ≤ hZ`, `(1 + r) ^ 2 * hZ ≤ Bz`, `0 < 1 + r`, `0 < c`, `0 ≤ wv` and `wv ≤ Bw` be real numbers.
  Then `|(cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2 +
  (cZ - hD - c * wv) * x1 ^ 2 - hZ * x0 ^ 2| ≤ (Bd + c + (1 + Bd) + (1 / 4 + Bz) +
  (Bz + K1 + c * Bw) + Bz) * (x2 ^ 2 + xc ^ 2 + x1 ^ 2 + xo ^ 2 + (x0 / (1 + r)) ^ 2)` for all real
  `x2`, `xc`, `xo`, `x1`, `x0`.
* `PDE.Analysis.le_sqrt_mul_sqrt_of_forall_le`: Let `0 ≤ a` and `0 ≤ b`. If
  `X ≤ u * a / 2 + b / (2 * u)` for every `u > 0`, then `X ≤ √a * √b`.
* `PDE.Analysis.neg_add_sub_le_of_abs_le`: Let `r ≥ 1` and let `A`, `U₀`, `X`, `s`, `S`, `c`, `ρ`,
  `σ` be nonnegative real numbers with `ρ ≤ 1 / r`, `σ ≤ 1 / r` and `s ≤ S * (√X + c * A / r)`. If
  `|L| ≤ c1 * A ^ 2 / r`, `|Tu| ≤ c2 * U₀ * A ^ 2 / r`,
  `|Tw| ≤ c3 * s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r`, `|St| ≤ 2 * U₁ * E`,
  `|SS| ≤ c4 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ)`,
  `|M1 + M2| ≤ c5 * U₀ * A ^ 2 / r` and `T = Tu + Tw`, then `-X + L + T - St - (SS + M1 + M2) ≤ 2 *
  U₁ * E + (|c1| + |c2| + |c5| + |c4| + c ^ 2 / 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 + |c4| ^
  2 * S ^ 2 + |c4| * S * c) * (1 + U₀) * (A ^ 2 + A ^ 6) / r`.
* `PDE.Analysis.neg_add_sub_sub_le_of_bounds`: Let `1 ≤ r`, let `A`, `U₀`, `D`, `s`, `S`, `ρ`, `σ`
  be nonnegative with `ρ ≤ 1 / r`, `σ ≤ 1 / r` and `s ≤ S * (A + √D)`, and let `T = Tu + Tw`. If
  `(3 / 4) * D - C0 * A ^ 2 / r ^ 2 ≤ I`, `|Tu| ≤ c2 * U₀ * A ^ 2 / r`,
  `|Tw| ≤ c3 * s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r`, `|St| ≤ 2 * U₁ * E`,
  `|SS| ≤ c4 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ)` and
  `|M1 + M2| ≤ c5 * U₀ * A ^ 2 / r`, then `-I + T - St - (SS + M1 + M2) ≤ 2 * U₁ * E + (|C0| +
  |c2| + |c5| + |c4| + 4 * (|c3| + |c4|) * √S ^ 3 + 8 ^ 3 * (4 * (|c3| + |c4|) * √S ^ 3) ^ 4 +
  |c4| * S + 2 * |c4| ^ 2 * S ^ 2) * (1 + U₀) * (A ^ 2 + A ^ 6) / r`. The terms containing `s` are
  absorbed into `(3 / 4) * D` by two Young-type bounds that cost `D / 8` each, and `A ^ 3`, `A ^ 4`
  are bounded by `A ^ 2 + A ^ 6`.
* `PDE.Analysis.neg_mul_triple_product_le`: Let `K ≥ 0` be a real number with
  `K ^ 2 = c0 ^ 2 + c1 ^ 2 + c2 ^ 2`. Then `-e * (c0 * (p1 * q2 - p2 * q1) + c1 * (p2 * q0 - p0 *
  q2) + c2 * (p0 * q1 - p1 * q0)) ≤ |e| * ((1 / 2) * K) * ((p0 ^ 2 + q0 ^ 2) + (p1 ^ 2 + q1 ^ 2) +
  (p2 ^ 2 + q2 ^ 2))` for all real `e`, `p0`, `p1`, `p2`, `q0`, `q1`, `q2`; the bracket on the left
  is the triple product of the vectors `c`, `p`, `q` written in coordinates.
* `PDE.Analysis.rpow_mul_rpow_le_div_eight_add`: Let `D`, `A`, `s`, `S`, `C` be nonnegative reals,
  `1 ≤ r` and `s ≤ S * (A + √D)`. Then `C * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) ≤ D / 8 +
  (4 * C * √S ^ 3 * A ^ 3 + 8 ^ 3 * (4 * C * √S ^ 3) ^ 4 * A ^ 6) / r`.

There is one further lemma of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

/-- Let `|cD| ≤ Bd`, `|cZ| ≤ Bz`, `0 ≤ hD`, `hD ≤ K1`, `0 ≤ hZ`, `(1 + r) ^ 2 * hZ ≤ Bz`,
`0 < 1 + r`, `0 < c`, `0 ≤ wv` and `wv ≤ Bw` be real numbers. Then
`|(cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2 + (cZ - hD - c * wv) * x1 ^ 2 - hZ *
x0 ^ 2| ≤ (Bd + c + (1 + Bd) + (1 / 4 + Bz) + (Bz + K1 + c * Bw) + Bz) * (x2 ^ 2 + xc ^ 2 + x1 ^ 2 +
xo ^ 2 + (x0 / (1 + r)) ^
2)` for all real `x2`, `xc`, `xo`, `x1`, `x0`. The proof uses the triangle inequality, bounds each
coefficient by its absolute bound, and rewrites `hZ * x0 ^ 2` as
`((1 + r) ^ 2 * hZ) * (x0 / (1 + r)) ^ 2`. -/
theorem abs_sum_five_mul_sq_le {cD c cZ hD hZ wv x2 xc xo x1 x0 r Bd Bz K1 Bw : ℝ} (hcD : |cD| ≤ Bd)
    (hcZ : |cZ| ≤ Bz) (hD0 : 0 ≤ hD) (hD1 : hD ≤ K1) (hZ0 : 0 ≤ hZ) (hZr : (1 + r) ^ 2 * hZ ≤ Bz)
    (hr : 0 < 1 + r) (hc : 0 < c) (hw0 : 0 ≤ wv) (hwB : wv ≤ Bw) :
    |(cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2 + (cZ - hD - c * wv) * x1 ^ 2 -
        hZ * x0 ^ 2|
      ≤ (Bd + c + (1 + Bd) + (1 / 4 + Bz) + (Bz + K1 + c * Bw) + Bz)
        * (x2 ^ 2 + xc ^ 2 + x1 ^ 2 + xo ^ 2 + (x0 / (1 + r)) ^ 2) := by
  have a1 := abs_le.1 hcD
  have a2 := abs_le.1 hcZ
  have hBd : 0 ≤ Bd := (abs_nonneg _).trans hcD
  have hBz : 0 ≤ Bz := (abs_nonneg _).trans hcZ
  have hK1 : 0 ≤ K1 := hD0.trans hD1
  have hcw : c * wv ≤ c * Bw := mul_le_mul_of_nonneg_left hwB hc.le
  have hcw0 : 0 ≤ c * wv := mul_nonneg hc.le hw0
  have t1 : |(cD - c) * x2 ^ 2| ≤ (Bd + c) * x2 ^ 2 := abs_mul_sq_le_of_abs_le
      (abs_le.2 ⟨by linarith, by
    linarith⟩)
  have t2 : |(1 - cD) * xc ^ 2| ≤ (1 + Bd) * xc ^ 2 := abs_mul_sq_le_of_abs_le
      (abs_le.2 ⟨by linarith, by
    linarith⟩)
  have t3 : |(1 / 4 - cZ) * xo ^ 2| ≤ (1 / 4 + Bz) * xo ^ 2 :=
      abs_mul_sq_le_of_abs_le (abs_le.2 ⟨by linarith, by linarith⟩)
  have t4 : |(cZ - hD - c * wv) * x1 ^ 2| ≤ (Bz + K1 + c * Bw) * x1 ^ 2 :=
    abs_mul_sq_le_of_abs_le (abs_le.2 ⟨by linarith, by linarith⟩)
  have e5 : hZ * x0 ^ 2 = ((1 + r) ^ 2 * hZ) * (x0 / (1 + r)) ^ 2 := by
    field_simp
  have t5 : |hZ * x0 ^ 2| ≤ Bz * (x0 / (1 + r)) ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg hZ0 (sq_nonneg x0)), e5]
    exact mul_le_mul_of_nonneg_right hZr (sq_nonneg _)
  have tri : |(cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2 + (cZ - hD - c * wv) *
      x1 ^ 2
      - hZ * x0 ^ 2| ≤ |(cD - c) * x2 ^ 2| + |(1 - cD) * xc ^ 2| + |(1 / 4 - cZ) * xo ^ 2|
        + |(cZ - hD - c * wv) * x1 ^ 2| + |hZ * x0 ^ 2| := by
    have h1 := abs_sub ((cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2
      + (cZ - hD - c * wv) * x1 ^ 2) (hZ * x0 ^ 2)
    have h2 := abs_add_le ((cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2 + (1 / 4 - cZ) * xo ^ 2)
      ((cZ - hD - c * wv) * x1 ^ 2)
    have h3 := abs_add_le ((cD - c) * x2 ^ 2 + (1 - cD) * xc ^ 2) ((1 / 4 - cZ) * xo ^ 2)
    have h4 := abs_add_le ((cD - c) * x2 ^ 2) ((1 - cD) * xc ^ 2)
    linarith
  set K := Bd + c + (1 + Bd) + (1 / 4 + Bz) + (Bz + K1 + c * Bw) + Bz with hK
  have s2 := sq_nonneg x2
  have sc := sq_nonneg xc
  have s1 := sq_nonneg x1
  have so := sq_nonneg xo
  have s0 := sq_nonneg (x0 / (1 + r))
  have hcB : 0 ≤ c * Bw := hcw0.trans hcw
  have k2 : (Bd + c) * x2 ^ 2 ≤ K * x2 ^ 2 := mul_le_mul_of_nonneg_right (by linarith) s2
  have kc : (1 + Bd) * xc ^ 2 ≤ K * xc ^ 2 := mul_le_mul_of_nonneg_right (by linarith) sc
  have ko : (1 / 4 + Bz) * xo ^ 2 ≤ K * xo ^ 2 := mul_le_mul_of_nonneg_right (by linarith) so
  have k1 : (Bz + K1 + c * Bw) * x1 ^ 2 ≤ K * x1 ^ 2 := mul_le_mul_of_nonneg_right (by linarith) s1
  have k0 : Bz * (x0 / (1 + r)) ^ 2 ≤ K * (x0 / (1 + r)) ^ 2 := mul_le_mul_of_nonneg_right (by
    linarith) s0
  have ex : K * (x2 ^ 2 + xc ^ 2 + x1 ^ 2 + xo ^ 2 + (x0 / (1 + r)) ^ 2)
      = K * x2 ^ 2 + K * xc ^ 2 + K * x1 ^ 2 + K * xo ^ 2 + K * (x0 / (1 + r)) ^ 2 := by ring
  rw [ex]
  linarith

/-- Let `0 ≤ a` and `0 ≤ b`. If `X ≤ u * a / 2 + b / (2 * u)` for every `u > 0`, then `X ≤ √a * √b`.
This is `sq_sqrt_bound` with the hypothesis written `u * a / 2 + b / (2 * u)`. -/
theorem le_sqrt_mul_sqrt_of_forall_le {X a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ u : ℝ, 0 < u → X ≤ u * a / 2 + b / (2 * u)) : X ≤ Real.sqrt a * Real.sqrt b :=
  sq_sqrt_bound ha hb fun t ht ↦ (h t ht).trans_eq (by field_simp)

/-- Let `K ≥ 0` be a real number with `K ^ 2 = c0 ^ 2 + c1 ^ 2 + c2 ^ 2`. Then
`-e * (c0 * (p1 * q2 - p2 * q1) + c1 * (p2 * q0 - p0 * q2) + c2 * (p0 * q1 - p1 * q0)) ≤ |e| * ((1 /
2) * K) * ((p0 ^ 2 + q0 ^ 2) + (p1 ^ 2 + q1 ^ 2) + (p2 ^ 2 + q2 ^
2))` for all real `e`, `p0`, `p1`, `p2`, `q0`, `q1`, `q2`; the bracket on the left is the triple
product of the vectors `c`, `p`, `q` written in coordinates. The proof compares squares: the squared
length of the cross product of `p` and `q` is at most the product of their squared lengths, the
Cauchy-Schwarz inequality brings in the factor `K ^ 2`, and a product of two nonnegative numbers is
at most the square of half their sum. -/
theorem neg_mul_triple_product_le (e c0 c1 c2 p0 p1 p2 q0 q1 q2 K : ℝ)
    (hK : K ^ 2 = c0 ^ 2 + c1 ^ 2 + c2 ^ 2)
    (hK0 : 0 ≤ K) :
    -e * (c0 * (p1 * q2 - p2 * q1) + c1 * (p2 * q0 - p0 * q2) + c2 * (p0 * q1 - p1 * q0))
      ≤ |e| * ((1 / 2) * K) * ((p0 ^ 2 + q0 ^ 2) + (p1 ^ 2 + q1 ^ 2) + (p2 ^ 2 + q2 ^ 2)) := by
  have hu : (p1 * q2 - p2 * q1) ^ 2 + (p2 * q0 - p0 * q2) ^ 2 + (p0 * q1 - p1 * q0) ^ 2
      ≤ (p0 ^ 2 + p1 ^ 2 + p2 ^ 2) * (q0 ^ 2 + q1 ^ 2 + q2 ^ 2) := by
    nlinarith [sq_nonneg (p0 * q0 + p1 * q1 + p2 * q2)]
  have hs : (c0 * (p1 * q2 - p2 * q1) + c1 * (p2 * q0 - p0 * q2) + c2 * (p0 * q1 - p1 * q0)) ^ 2
      ≤ K ^ 2 * ((p1 * q2 - p2 * q1) ^ 2 + (p2 * q0 - p0 * q2) ^ 2 + (p0 * q1 - p1 * q0) ^ 2) := by
    rw [hK]
    nlinarith [sq_nonneg (c0 * (p2 * q0 - p0 * q2) - c1 * (p1 * q2 - p2 * q1)),
      sq_nonneg (c0 * (p0 * q1 - p1 * q0) - c2 * (p1 * q2 - p2 * q1)),
      sq_nonneg (c1 * (p0 * q1 - p1 * q0) - c2 * (p2 * q0 - p0 * q2))]
  have hPQ : (p0 ^ 2 + p1 ^ 2 + p2 ^ 2) * (q0 ^ 2 + q1 ^ 2 + q2 ^ 2)
      ≤ (((p0 ^ 2 + q0 ^ 2) + (p1 ^ 2 + q1 ^ 2) + (p2 ^ 2 + q2 ^ 2)) / 2) ^ 2 := by
    nlinarith [sq_nonneg ((p0 ^ 2 + p1 ^ 2 + p2 ^ 2) - (q0 ^ 2 + q1 ^ 2 + q2 ^ 2))]
  generalize (c0 * (p1 * q2 - p2 * q1) + c1 * (p2 * q0 - p0 * q2) + c2 * (p0 * q1 - p1 * q0)) =
      s at hs ⊢
  generalize (p1 * q2 - p2 * q1) ^ 2 + (p2 * q0 - p0 * q2) ^ 2 + (p0 * q1 - p1 * q0) ^ 2 =
      U at hu hs
  generalize (p0 ^ 2 + p1 ^ 2 + p2 ^ 2) * (q0 ^ 2 + q1 ^ 2 + q2 ^ 2) = PQ at hu hPQ
  have hN : 0 ≤ (p0 ^ 2 + q0 ^ 2) + (p1 ^ 2 + q1 ^ 2) + (p2 ^ 2 + q2 ^ 2) := by positivity
  generalize (p0 ^ 2 + q0 ^ 2) + (p1 ^ 2 + q1 ^ 2) + (p2 ^ 2 + q2 ^ 2) = N at hPQ hN ⊢
  have hsq : (-e * s) ^ 2 ≤ (|e| * ((1 / 2) * K) * N) ^ 2 := by
    have h1 : (-e * s) ^ 2 = e ^ 2 * s ^ 2 := by ring
    have h2 : (|e| * ((1 / 2) * K) * N) ^ 2 = e ^ 2 * (K ^ 2 * (N / 2) ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, sq_abs]
      ring
    rw [h1, h2]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg e)
    calc s ^ 2 ≤ K ^ 2 * U := hs
      _ ≤ K ^ 2 * PQ := mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ ≤ K ^ 2 * (N / 2) ^ 2 := mul_le_mul_of_nonneg_left hPQ (sq_nonneg _)
  exact le_of_sq_le_sq hsq (by positivity)

/-- Let `D`, `A`, `s`, `S`, `C` be nonnegative reals, `1 ≤ r` and `s ≤ S * (A + √D)`. Then
`C * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) ≤ D / 8 + (4 * C * √S ^ 3 * A ^ 3 + 8 ^ 3 * (4 * C * √S
^ 3) ^ 4 * A ^ 6) / r`. The proof bounds `√s ≤ √S * (√A +
√(√D))`, cubes this, and absorbs the term with `√(√D) ^ 3` into `D /
8` by a Young-type inequality, using `√(√D) ^ 4 = D`. -/
theorem rpow_mul_rpow_le_div_eight_add {D A r s S C : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hs : 0 ≤ s) (hS : 0 ≤ S) (hC : 0 ≤ C) (hso : s ≤ S * (A + √D)) :
    C * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) ≤
      D / 8 + (4 * C * √S ^ 3 * A ^ 3 + 8 ^ 3 * (4 * C * √S ^ 3) ^ 4 * A ^ 6) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  rw [rpow_three_halves_eq_sqrt_pow_of_nonneg hs, rpow_three_halves_eq_sqrt_pow_of_nonneg hA]
  have hσ0 := Real.sqrt_nonneg s
  have ha0 := Real.sqrt_nonneg A
  have hτ0 := Real.sqrt_nonneg (√D)
  have hL0 := Real.sqrt_nonneg S
  have hσ2 : √s ^ 2 = s := Real.sq_sqrt hs
  have ha2 : √A ^ 2 = A := Real.sq_sqrt hA
  have ht2 : √(√D) ^ 2 = √D := Real.sq_sqrt (Real.sqrt_nonneg D)
  have hD2 : √D ^ 2 = D := Real.sq_sqrt hD
  have hL2 : √S ^ 2 = S := Real.sq_sqrt hS
  set σ := √s
  set a := √A
  set τ := √(√D)
  set L := √S
  have hτ4 : τ ^ 4 = D := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ht2, hD2]
  have ha6 : a ^ 6 = A ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, ha2]
  have ha12 : a ^ 12 = A ^ 6 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, ha2]
  have hB0 : 0 ≤ L * (a + τ) := mul_nonneg hL0 (add_nonneg ha0 hτ0)
  have hsq : σ ^ 2 ≤ (L * (a + τ)) ^ 2 := by
    have e : (L * (a + τ)) ^ 2 = L ^ 2 * (a ^ 2 + τ ^ 2) + 2 * L ^ 2 * (a * τ) := by ring
    rw [e, hσ2, hL2, ha2, ht2]
    have : 0 ≤ 2 * S * (a * τ) := by positivity
    linarith
  have hσ : σ ≤ L * (a + τ) := by
    by_contra h
    rw [not_le] at h
    nlinarith [mul_lt_mul'' h h hB0 hB0]
  have hσ3 : σ ^ 3 ≤ (L * (a + τ)) ^ 3 := pow_le_pow_left₀ hσ0 hσ 3
  have hcube : (a + τ) ^ 3 ≤ 4 * (a ^ 3 + τ ^ 3) := by
    nlinarith [mul_nonneg (add_nonneg ha0 hτ0) (sq_nonneg (a - τ))]
  have hL3 : 0 ≤ L ^ 3 := pow_nonneg hL0 3
  have ha3 : 0 ≤ a ^ 3 := pow_nonneg ha0 3
  have hprod : σ ^ 3 * a ^ 3 ≤ 4 * L ^ 3 * a ^ 6 + 4 * L ^ 3 * τ ^ 3 * a ^ 3 := by
    have h1 : σ ^ 3 * a ^ 3 ≤ (L * (a + τ)) ^ 3 * a ^ 3 := mul_le_mul_of_nonneg_right hσ3 ha3
    have h2 : (L * (a + τ)) ^ 3 * a ^ 3 ≤ L ^ 3 * (4 * (a ^ 3 + τ ^ 3)) * a ^ 3 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube hL3) ha3
    have e : L ^ 3 * (4 * (a ^ 3 + τ ^ 3)) * a ^ 3 = 4 * L ^ 3 * a ^ 6 + 4 * L ^ 3 * τ ^ 3 *
        a ^ 3 := by
      ring
    linarith
  set M := 4 * C * L ^ 3 with hMdef
  have hM : 0 ≤ M := by positivity
  have hZ : 0 ≤ a ^ 3 / r := div_nonneg ha3 hr0.le
  have hy := mul_cube_mul_le_pow_four_add (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hM) hτ0 hZ
  have hZ4 : (a ^ 3 / r) ^ 4 = A ^ 6 / r ^ 4 := by
    rw [div_pow, ← pow_mul, show 3 * 4 = 12 from rfl, ha12]
  have hr4 : r ≤ r ^ 4 := by
    have h1 : 1 ≤ r ^ 3 := one_le_pow₀ hr
    nlinarith
  have hA6 : A ^ 6 / r ^ 4 ≤ A ^ 6 / r :=
    div_le_div_of_nonneg_left (by positivity) hr0 hr4
  have hProductBound : M * τ ^ 3 * (a ^ 3 / r) ≤ D / 8 + 8 ^ 3 * M ^ 4 * (A ^ 6 / r) := by
    have e : (8 * M) ^ 4 = 8 * (8 ^ 3 * M ^ 4) := by ring
    rw [e, hZ4, hτ4] at hy
    have hM4 : 0 ≤ 8 ^ 3 * M ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left hA6 hM4
    nlinarith
  have hCr : C * (σ ^ 3 * a ^ 3 / r) ≤ C * ((4 * L ^ 3 * a ^ 6 + 4 * L ^ 3 * τ ^ 3 * a ^ 3) / r) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hprod hr0.le) hC
  have e2 : C * ((4 * L ^ 3 * a ^ 6 + 4 * L ^ 3 * τ ^ 3 * a ^ 3) / r) =
      M * A ^ 3 / r + M * τ ^ 3 * (a ^ 3 / r) := by
    rw [hMdef, ha6.symm]; ring
  have e3 : (M * A ^ 3 + 8 ^ 3 * M ^ 4 * A ^ 6) / r = M * A ^ 3 / r + 8 ^ 3 * M ^ 4 *
      (A ^ 6 / r) := by
    ring
  rw [e3]
  linarith

/-- Let `X`, `A`, `s`, `S`, `c`, `C` be nonnegative real numbers and `r ≥ 1`, with
`s ≤ S * (√X + c * A / r)`. Then
`C * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) ≤ X / 2 + (c ^ 2 / 2 * A ^ 2 + C ^ 4 * (4 * S ^ 2 + 1)
^ 3 * A ^ 6) / r`. The proof bounds `s ^ (3 / 2 :
ℝ)` with the hypothesis on `s` and then applies a Young-type bound of the form `u * x ^ 3 * z ≤ x ^
4 + u ^ 4 * z ^ 4`. -/
theorem rpow_three_halves_mul_le_half_add {X A r s S c C : ℝ} (hX : 0 ≤ X) (hA : 0 ≤ A) (hr : 1 ≤ r)
    (hs : 0 ≤ s) (hS : 0 ≤ S) (hc : 0 ≤ c) (hC : 0 ≤ C) (hHs : s ≤ S * (√X + c * A / r)) :
    C * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) ≤
      X / 2 + (c ^ 2 / 2 * A ^ 2 + C ^ 4 * (4 * S ^ 2 + 1) ^ 3 * A ^ 6) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hq0 : 0 ≤ c * A / r := div_nonneg (mul_nonneg hc hA) hr0.le
  have hq : c * A / r ≤ c * A := div_le_self (mul_nonneg hc hA) hr
  have ha := Real.sqrt_nonneg X
  have hsX : √X ^ 2 = X := Real.sq_sqrt hX
  have hB : 0 ≤ S * (√X + c * A / r) := mul_nonneg hS (add_nonneg ha hq0)
  have hsB : s ^ (3 / 2 : ℝ) ≤ (S * (√X + c * A / r)) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hs hHs (by norm_num)
  rw [rpow_three_halves_eq_sqrt_pow_of_nonneg hB] at hsB
  rw [rpow_three_halves_eq_sqrt_pow_of_nonneg hA]
  have hx0 := Real.sqrt_nonneg (S * (√X + c * A / r))
  have hz0 : 0 ≤ √A ^ 3 := pow_nonneg (Real.sqrt_nonneg A) 3
  have hx4 : √(S * (√X + c * A / r)) ^ 4 = (S * (√X + c * A / r)) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hB]
  have hz4 : (√A ^ 3) ^ 4 = A ^ 6 := by
    rw [← pow_mul, show 3 * 4 = 2 * 6 from rfl, pow_mul, Real.sq_sqrt hA]
  have hk : 0 < 4 * S ^ 2 + 1 := by positivity
  have hy := mul_cube_mul_le_pow_four_add (mul_nonneg hC hk.le) hx0 hz0
  have hsq : (√X + c * A / r) ^ 2 ≤ 2 * (X + c ^ 2 * A ^ 2) := by
    nlinarith [sq_nonneg (√X - c * A / r), mul_le_mul hq hq hq0 (mul_nonneg hc hA)]
  have hB2 : (S * (√X + c * A / r)) ^ 2 ≤ 2 * S ^ 2 * (X + c ^ 2 * A ^ 2) := by
    calc (S * (√X + c * A / r)) ^ 2 = S ^ 2 * (√X + c * A / r) ^ 2 := by ring
      _ ≤ S ^ 2 * (2 * (X + c ^ 2 * A ^ 2)) := mul_le_mul_of_nonneg_left hsq (sq_nonneg S)
      _ = 2 * S ^ 2 * (X + c ^ 2 * A ^ 2) := by ring
  have hXA : 0 ≤ X + c ^ 2 * A ^ 2 := by positivity
  have hk2 := mul_le_mul_of_nonneg_right
    (show 2 * S ^ 2 ≤ (4 * S ^ 2 + 1) / 2 by linarith) hXA
  set x := √(S * (√X + c * A / r))
  set z := √A ^ 3
  set k := 4 * S ^ 2 + 1
  have hmain : C * (x ^ 3 * z) ≤ (X + c ^ 2 * A ^ 2) / 2 + C ^ 4 * k ^ 3 * A ^ 6 := by
    have h' : k * (C * (x ^ 3 * z)) ≤ k * ((X + c ^ 2 * A ^ 2) / 2 + C ^ 4 * k ^ 3 * A ^ 6) := by
      calc k * (C * (x ^ 3 * z)) = C * k * x ^ 3 * z := by ring
        _ ≤ x ^ 4 + (C * k) ^ 4 * z ^ 4 := hy
        _ = (S * (√X + c * A / r)) ^ 2 + C ^ 4 * k ^ 4 * A ^ 6 := by rw [hx4, mul_pow, hz4]; ring
        _ ≤ k / 2 * (X + c ^ 2 * A ^ 2) + C ^ 4 * k ^ 4 * A ^ 6 := by linarith
        _ = k * ((X + c ^ 2 * A ^ 2) / 2 + C ^ 4 * k ^ 3 * A ^ 6) := by ring
    exact le_of_mul_le_mul_left h' hk
  have hxz : s ^ (3 / 2 : ℝ) * z ≤ x ^ 3 * z := mul_le_mul_of_nonneg_right hsB hz0
  have h1 : C * (s ^ (3 / 2 : ℝ) * z / r) ≤
      ((X + c ^ 2 * A ^ 2) / 2 + C ^ 4 * k ^ 3 * A ^ 6) / r := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right ((mul_le_mul_of_nonneg_left hxz hC).trans hmain) hr0.le
  have h2 : X / 2 / r ≤ X / 2 := div_le_self (by positivity) hr
  calc C * (s ^ (3 / 2 : ℝ) * z / r) ≤ ((X + c ^ 2 * A ^ 2) / 2 + C ^ 4 * k ^ 3 * A ^ 6) / r := h1
    _ = X / 2 / r + (c ^ 2 / 2 * A ^ 2 + C ^ 4 * k ^ 3 * A ^ 6) / r := by ring
    _ ≤ _ := by linarith

/-- Let `r ≥ 1` and let `A`, `U₀`, `X`, `s`, `S`, `c`, `ρ`, `σ` be nonnegative real numbers with
`ρ ≤ 1 / r`, `σ ≤ 1 / r` and `s ≤ S * (√X + c * A / r)`. If `|L| ≤ c1 * A ^ 2 / r`,
`|Tu| ≤ c2 * U₀ * A ^ 2 / r`, `|Tw| ≤ c3 * s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r`,
`|St| ≤ 2 * U₁ * E`,
`|SS| ≤ c4 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ)`,
`|M1 + M2| ≤ c5 * U₀ * A ^ 2 / r` and `T = Tu + Tw`, then
`-X + L + T - St - (SS + M1 + M2) ≤ 2 * U₁ * E + (|c1| + |c2| + |c5| + |c4| + c ^ 2 / 2 + (|c3| +
|c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 + |c4| ^ 2 * S ^ 2 + |c4| * S * c) * (1 + U₀) * (A ^ 2 + A ^ 6) /
r`. The proof absorbs the terms that contain `s` into `-X` by two Young-type bounds and uses
`A ^ 3 ≤ A ^ 2 + A ^ 6` and `A ^ 4 ≤ A ^ 2 + A ^ 6`. -/
theorem neg_add_sub_le_of_abs_le {X s E A U₀ U₁ r S c c1 c2 c3 c4 c5 L T Tu Tw St SS M1 M2 ρ σ : ℝ}
    (hr : 1 ≤ r) (hA : 0 ≤ A) (hU : 0 ≤ U₀) (hX : 0 ≤ X) (hs : 0 ≤ s) (hS : 0 ≤ S) (hc : 0 ≤ c)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / r) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / r)
    (hso : s ≤ S * (√X + c * A / r)) (hL : |L| ≤ c1 * A ^ 2 / r) (hTu : |Tu| ≤ c2 * U₀ * A ^ 2 / r)
    (hTw : |Tw| ≤ c3 * s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) (hSt : |St| ≤ 2 * U₁ * E)
    (hSS : |SS| ≤ c4 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ))
    (hM : |M1 + M2| ≤ c5 * U₀ * A ^ 2 / r) (hT : T = Tu + Tw) :
    -X + L + T - St - (SS + M1 + M2) ≤
      2 * U₁ * E + (|c1| + |c2| + |c5| + |c4| + c ^ 2 / 2 + (|c3| + |c4|) ^ 4 *
          (4 * S ^ 2 + 1) ^ 3 +
      |c4| ^ 2 * S ^ 2 + |c4| * S * c) * (1 + U₀) * (A ^ 2 + A ^ 6) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hP : 0 ≤ s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by positivity
  have hQ : 0 ≤ s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ := by positivity
  have hC : 0 ≤ |c3| + |c4| := by positivity
  have hcub' := rpow_three_halves_mul_le_half_add hX hA hr hs hS hc hC hso
  have hquad := mul_sq_mul_mul_le_quarter_add hX hA hr hS hc (abs_nonneg c4) hρ0 hρ hso
  have hTw' : |Tw| ≤ |c3| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by
    calc |Tw| ≤ c3 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by
          rw [← mul_div_assoc, ← mul_assoc]; exact hTw
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self c3) hP
  have hSS' := hSS.trans (mul_le_mul_of_nonneg_right (le_abs_self c4) hQ)
  have hL' : c1 * A ^ 2 / r ≤ |c1| * A ^ 2 / r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self c1) (sq_nonneg A)) hr0.le
  have hTu' : c2 * U₀ * A ^ 2 / r ≤ |c2| * U₀ * A ^ 2 / r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self c2) hU) (sq_nonneg A)) hr0.le
  have hM' : c5 * U₀ * A ^ 2 / r ≤ |c5| * U₀ * A ^ 2 / r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self c5) hU) (sq_nonneg A)) hr0.le
  have hσ' : |c4| * (A ^ 3 * σ) ≤ |c4| * A ^ 3 / r := by
    calc |c4| * (A ^ 3 * σ) ≤ |c4| * (A ^ 3 * (1 / r)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hσ (by positivity)) (abs_nonneg c4)
      _ = |c4| * A ^ 3 / r := by ring
  have hN : |c1| * A ^ 2 + |c2| * U₀ * A ^ 2 + |c5| * U₀ * A ^ 2 + |c4| * A ^ 3 +
      (c ^ 2 / 2 * A ^ 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 * A ^ 6) +
      (|c4| ^ 2 * S ^ 2 * A ^ 4 + |c4| * S * c * A ^ 3) ≤
          (|c1| + |c2| + |c5| + |c4| + c ^ 2 / 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 +
      |c4| ^ 2 * S ^ 2 + |c4| * S * c) * (1 + U₀) * (A ^ 2 + A ^ 6) := by
    have h3 := cube_le_sq_add_pow_six A
    have h4 := pow_four_le_sq_add_pow_six A
    have hA2 : A ^ 2 ≤ A ^ 2 + A ^ 6 := le_add_of_nonneg_right (by positivity)
    have hA6 : A ^ 6 ≤ A ^ 2 + A ^ 6 := le_add_of_nonneg_left (by positivity)
    have hW : 0 ≤ A ^ 2 + A ^ 6 := by positivity
    have hk0 : 0 ≤ (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 := by positivity
    have e1 := mul_le_mul_of_nonneg_left hA2 (abs_nonneg c1)
    have e2 := mul_le_mul_of_nonneg_left hA2 (mul_nonneg (abs_nonneg c2) hU)
    have e3 := mul_le_mul_of_nonneg_left hA2 (mul_nonneg (abs_nonneg c5) hU)
    have e4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg c4)
    have e5 := mul_le_mul_of_nonneg_left hA2 (by positivity : (0 : ℝ) ≤ c ^ 2 / 2)
    have e6 := mul_le_mul_of_nonneg_left hA6 hk0
    have e7 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ |c4| ^ 2 * S ^ 2)
    have e8 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ |c4| * S * c)
    have f1 : 0 ≤ |c1| * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f2 : 0 ≤ |c2| * (A ^ 2 + A ^ 6) := by positivity
    have f3 : 0 ≤ |c5| * (A ^ 2 + A ^ 6) := by positivity
    have f4 : 0 ≤ |c4| * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f5 : 0 ≤ c ^ 2 / 2 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f6 : 0 ≤ (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f7 : 0 ≤ |c4| ^ 2 * S ^ 2 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f8 : 0 ≤ |c4| * S * c * U₀ * (A ^ 2 + A ^ 6) := by positivity
    linarith
  have hNr := div_le_div_of_nonneg_right hN hr0.le
  have hNsplit : (|c1| * A ^ 2 + |c2| * U₀ * A ^ 2 + |c5| * U₀ * A ^ 2 + |c4| * A ^ 3 +
      (c ^ 2 / 2 * A ^ 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 * A ^ 6) +
      (|c4| ^ 2 * S ^ 2 * A ^ 4 + |c4| * S * c * A ^ 3)) / r =
      |c1| * A ^ 2 / r + |c2| * U₀ * A ^ 2 / r + |c5| * U₀ * A ^ 2 / r + |c4| * A ^ 3 / r +
      (c ^ 2 / 2 * A ^ 2 + (|c3| + |c4|) ^ 4 * (4 * S ^ 2 + 1) ^ 3 * A ^ 6) / r +
      (|c4| ^ 2 * S ^ 2 * A ^ 4 + |c4| * S * c * A ^ 3) / r := by ring
  have hlin : |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ) =
      |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) + |c4| * (A ^ 2 * s * ρ) +
        |c4| * (A ^ 3 * σ) := by ring
  have hlin2 : (|c3| + |c4|) * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) =
      |c3| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) + |c4| *
          (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by
    ring
  have a1 := neg_abs_le SS
  have a2 := neg_abs_le (M1 + M2)
  have a3 := le_abs_self L
  have a4 := le_abs_self Tu
  have a5 := le_abs_self Tw
  have a6 := neg_abs_le St
  rw [hT]
  linarith

/-- Let `1 ≤ r`, let `A`, `U₀`, `D`, `s`, `S`, `ρ`, `σ` be nonnegative with `ρ ≤ 1 / r`, `σ ≤ 1 / r`
and `s ≤ S * (A + √D)`, and let `T = Tu + Tw`. If `(3 / 4) * D - C0 * A ^ 2 / r ^ 2 ≤ I`,
`|Tu| ≤ c2 * U₀ * A ^ 2 / r`, `|Tw| ≤ c3 * s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r`,
`|St| ≤ 2 * U₁ * E`,
`|SS| ≤ c4 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ)` and
`|M1 + M2| ≤ c5 * U₀ * A ^ 2 / r`, then
`-I + T - St - (SS + M1 + M2) ≤ 2 * U₁ * E + (|C0| + |c2| + |c5| + |c4| +
4 * (|c3| + |c4|) * √S ^ 3 + 8 ^ 3 * (4 * (|c3| + |c4|) * √S ^ 3) ^ 4 + |c4| * S + 2 * |c4| ^ 2 *
S ^ 2) * (1 + U₀) * (A ^ 2 + A ^ 6) / r`. The terms containing `s` are absorbed into `(3 / 4) *
D` by two Young-type bounds that cost `D / 8` each, and `A ^ 3`, `A ^ 4` are bounded by `A ^ 2 + A ^
6`. -/
theorem neg_add_sub_sub_le_of_bounds
    {I D s E A U₀ U₁ r S C0 c2 c3 c4 c5 T Tu Tw St SS M1 M2 ρ σ : ℝ}
    (hr : 1 ≤ r) (hA : 0 ≤ A) (hU : 0 ≤ U₀) (hD : 0 ≤ D) (hs : 0 ≤ s) (hS : 0 ≤ S)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / r) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / r)
    (hso : s ≤ S * (A + √D)) (hI : (3 / 4) * D - C0 * A ^ 2 / r ^ 2 ≤ I)
    (hTu : |Tu| ≤ c2 * U₀ * A ^ 2 / r)
    (hTw : |Tw| ≤ c3 * s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) (hSt : |St| ≤ 2 * U₁ * E)
    (hSS : |SS| ≤ c4 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ))
    (hM : |M1 + M2| ≤ c5 * U₀ * A ^ 2 / r) (hT : T = Tu + Tw) :
    -I + T - St - (SS + M1 + M2) ≤
      2 * U₁ * E + (|C0| + |c2| + |c5| + |c4| + 4 * (|c3| + |c4|) * √S ^ 3 +
        8 ^ 3 * (4 * (|c3| + |c4|) * √S ^ 3) ^ 4 + |c4| * S + 2 * |c4| ^ 2 * S ^ 2) *
        (1 + U₀) * (A ^ 2 + A ^ 6) / r := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hP : 0 ≤ s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r := by positivity
  have hQ : 0 ≤ s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ := by positivity
  have hC : 0 ≤ |c3| + |c4| := by positivity
  have hcub := rpow_mul_rpow_le_div_eight_add hD hA hr hs hS hC hso
  have hquad := sq_mul_mul_le_div_eight_add hD hA hr hS (abs_nonneg c4) hρ0 hρ hso
  have hTw' : |Tw| ≤ |c3| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by
    calc |Tw| ≤ c3 * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by
          rw [← mul_div_assoc, ← mul_assoc]; exact hTw
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_abs_self c3) hP
  have hSS' := hSS.trans (mul_le_mul_of_nonneg_right (le_abs_self c4) hQ)
  have hrr : r ≤ r ^ 2 := by nlinarith
  have hI' : C0 * A ^ 2 / r ^ 2 ≤ |C0| * A ^ 2 / r := by
    calc C0 * A ^ 2 / r ^ 2 ≤ |C0| * A ^ 2 / r ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C0) (sq_nonneg A))
            (by positivity)
      _ ≤ |C0| * A ^ 2 / r := div_le_div_of_nonneg_left (by positivity) hr0 hrr
  have hTu' : c2 * U₀ * A ^ 2 / r ≤ |c2| * U₀ * A ^ 2 / r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self c2) hU) (sq_nonneg A)) hr0.le
  have hM' : c5 * U₀ * A ^ 2 / r ≤ |c5| * U₀ * A ^ 2 / r :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self c5) hU) (sq_nonneg A)) hr0.le
  have hσ' : |c4| * (A ^ 3 * σ) ≤ |c4| * A ^ 3 / r := by
    calc |c4| * (A ^ 3 * σ) ≤ |c4| * (A ^ 3 * (1 / r)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hσ (by positivity)) (abs_nonneg c4)
      _ = |c4| * A ^ 3 / r := by ring
  set k1 := 4 * (|c3| + |c4|) * √S ^ 3
  set k2 := 8 ^ 3 * (4 * (|c3| + |c4|) * √S ^ 3) ^ 4
  have hk1 : 0 ≤ k1 := by positivity
  have hk2 : 0 ≤ k2 := by positivity
  have hN : |C0| * A ^ 2 + |c2| * U₀ * A ^ 2 + |c5| * U₀ * A ^ 2 + |c4| * A ^ 3 +
      (k1 * A ^ 3 + k2 * A ^ 6) + (|c4| * S * A ^ 3 + 2 * |c4| ^ 2 * S ^ 2 * A ^ 4) ≤
      (|C0| + |c2| + |c5| + |c4| + k1 + k2 + |c4| * S + 2 * |c4| ^ 2 * S ^ 2) *
        (1 + U₀) * (A ^ 2 + A ^ 6) := by
    have h3 := cube_le_sq_add_pow_six A
    have h4 := pow_four_le_sq_add_pow_six A
    have hA2 : A ^ 2 ≤ A ^ 2 + A ^ 6 := le_add_of_nonneg_right (by positivity)
    have hA6 : A ^ 6 ≤ A ^ 2 + A ^ 6 := le_add_of_nonneg_left (by positivity)
    have hW : 0 ≤ A ^ 2 + A ^ 6 := by positivity
    have e1 := mul_le_mul_of_nonneg_left hA2 (abs_nonneg C0)
    have e2 := mul_le_mul_of_nonneg_left hA2 (mul_nonneg (abs_nonneg c2) hU)
    have e3 := mul_le_mul_of_nonneg_left hA2 (mul_nonneg (abs_nonneg c5) hU)
    have e4 := mul_le_mul_of_nonneg_left h3 (abs_nonneg c4)
    have e5 := mul_le_mul_of_nonneg_left h3 hk1
    have e6 := mul_le_mul_of_nonneg_left hA6 hk2
    have e7 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ |c4| * S)
    have e8 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * |c4| ^ 2 * S ^ 2)
    have f1 : 0 ≤ |C0| * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f2 : 0 ≤ |c2| * (A ^ 2 + A ^ 6) := by positivity
    have f3 : 0 ≤ |c5| * (A ^ 2 + A ^ 6) := by positivity
    have f4 : 0 ≤ |c4| * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f5 : 0 ≤ k1 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f6 : 0 ≤ k2 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f7 : 0 ≤ |c4| * S * U₀ * (A ^ 2 + A ^ 6) := by positivity
    have f8 : 0 ≤ 2 * |c4| ^ 2 * S ^ 2 * U₀ * (A ^ 2 + A ^ 6) := by positivity
    linarith
  have hNr := div_le_div_of_nonneg_right hN hr0.le
  have hNsplit : (|C0| * A ^ 2 + |c2| * U₀ * A ^ 2 + |c5| * U₀ * A ^ 2 + |c4| * A ^ 3 +
      (k1 * A ^ 3 + k2 * A ^ 6) + (|c4| * S * A ^ 3 + 2 * |c4| ^ 2 * S ^ 2 * A ^ 4)) / r =
      |C0| * A ^ 2 / r + |c2| * U₀ * A ^ 2 / r + |c5| * U₀ * A ^ 2 / r + |c4| * A ^ 3 / r +
      (k1 * A ^ 3 + k2 * A ^ 6) / r +
      (|c4| * S * A ^ 3 + 2 * |c4| ^ 2 * S ^ 2 * A ^ 4) / r := by ring
  have hlin : |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r + A ^ 2 * s * ρ + A ^ 3 * σ) =
      |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) + |c4| * (A ^ 2 * s * ρ) +
        |c4| * (A ^ 3 * σ) := by ring
  have hlin2 : (|c3| + |c4|) * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) =
      |c3| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) +
        |c4| * (s ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) / r) := by ring
  have a1 := neg_abs_le SS
  have a2 := neg_abs_le (M1 + M2)
  have a4 := le_abs_self Tu
  have a5 := le_abs_self Tw
  have a6 := neg_abs_le St
  rw [hT]
  linarith

end PDE.Analysis
