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

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Basic.ENNReal.Holder
public import Mathlib.Data.List.GetD
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Linarith.NNRealPreprocessor
public import PDE.Analysis.Order.MinMax
public import PDE.Analysis.Scalar.Powers

set_option linter.style.header false

/-!
# Extended nonnegative real numbers

The lemmas move between real numbers and `ℝ≥0∞` (`ENNReal.ofReal`, `ENNReal.toReal`, the extended
norm), compute real powers of products and of squares, and compare finite and infinite values. The
proofs use the lemmas of Mathlib on `ENNReal.rpow` and `ENNReal.ofReal` and case splits on whether a
value is finite.

## Main results

* `PDE.Analysis.ofReal_mul_mul_sum_four_le`: Let `0 ≤ w`, `w ≤ Bw`, `0 ≤ a`, `0 ≤ M`, `e1 ≤ M * s1`,
  `e2 ≤ M * s2`, `e3 ≤ M * s3`, `e4 ≤ M * s4` be real numbers, with `s1`, `s2`, `s3`, `s4`
  nonnegative. Then `ENNReal.ofReal (w * a * (e1 + e2 + e3 + e4)) ≤ ENNReal.ofReal (Bw * M) *
  (ENNReal.ofReal (a * s1) + ENNReal.ofReal (a * s2) + ENNReal.ofReal (a * s3) + ENNReal.ofReal (a *
  s4))`.
* `PDE.Analysis.ofReal_abs_le_ofReal_mul_add`: For real numbers with `0 ≤ K₁`, `0 ≤ K₂`, `0 ≤ D`,
  `0 ≤ A` and `|r| ≤ K₁ * D + K₂ * A`, `ENNReal.ofReal |r| ≤ ENNReal.ofReal K₁ * ENNReal.ofReal D +
  ENNReal.ofReal K₂ * ENNReal.ofReal A`.
* `PDE.Analysis.ofReal_add_neg_le_of_sub_le`: For real numbers with `0 ≤ a`, `0 ≤ s` and
  `a - s ≤ X`, `ENNReal.ofReal a + ENNReal.ofReal (-X) ≤ ENNReal.ofReal X + ENNReal.ofReal s`.
* `PDE.Analysis.enorm_sq_le_of_norm_le`: For `x` in a normed additive group and a real `c`, if
  `‖x‖ ≤ c` then `‖x‖ₑ ^ 2 ≤ ENNReal.ofReal (c ^ 2)`.
* `PDE.Analysis.le_sqrt_toReal_of_ofReal_sq_le`: Let `x`, `D`, `K`, `g` be nonnegative reals and let
  `P : ℝ≥0∞` and `Q : Fin 3 → ℝ≥0∞` satisfy `P ≠ ⊤` and `Q j ≠ ⊤` for all `j`. If `ENNReal.ofReal (x
  ^ 2) ≤ ENNReal.ofReal (6 * D ^ 2) * (P + ∑ j, Q j) + ENNReal.ofReal K * ENNReal.ofReal (g ^ 2)`,
  then `x ≤ 3 * D * (√(P.toReal) + ∑ j, √((Q j).toReal)) + √K * g`.
* `PDE.Analysis.ne_top_and_toReal_le_add_toReal`: Let `d r : ℝ≥0∞` with `r ≠ ⊤` and let `t` be a
  real number. If `d + ENNReal.ofReal (-t) ≤ ENNReal.ofReal t + r`, then `d ≠ ⊤` and
  `d.toReal ≤ t + r.toReal`.
* `PDE.Analysis.ofReal_abs_add_sum_add_sum_le`: Let `a` be a real number, `e : Fin n → ℝ` with
  `e β ≤ 0` for all `β`, and `mm c d : Fin k → ℝ` with `mm β = -(c β) - d β`, `0 ≤ c β` and
  `0 ≤ d β` for all `β`. Then `ENNReal.ofReal |a + ∑ β, e β + ∑ β, mm β| ≤ ENNReal.ofReal |a| + ∑ β,
  ENNReal.ofReal (-e β) + ∑ β, (ENNReal.ofReal (c β) + ENNReal.ofReal (d β))`.
* `PDE.Analysis.ofReal_mul_div_add_eq`: For real numbers with `0 ≤ d`, `0 ≤ a`, `0 < c` and `0 ≤ b`,
  `ENNReal.ofReal (d * (a / c + b)) = ENNReal.ofReal (d / c) * ENNReal.ofReal a +
  ENNReal.ofReal (d * b)`.

There are 108 further lemmas of the same kind.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open Filter Topology Real
open scoped ENNReal NNReal

namespace PDE.Analysis

/-- Let `a`, `b`, `w₀` be nonnegative reals and `I : ℝ≥0∞` with `I ≠ ⊤`. If
`ENNReal.ofReal a + ENNReal.ofReal w₀ * ENNReal.ofReal b ≤ I`, then `a + w₀ * b ≤ I.toReal`. -/
theorem add_mul_le_toReal_of_ofReal_le {a b w₀ : ℝ} {I : ℝ≥0∞} (hw0 : 0 ≤ w₀) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hI : I ≠ ⊤)
    (h : ENNReal.ofReal a + ENNReal.ofReal w₀ * ENNReal.ofReal b ≤ I) : a + w₀ * b ≤ I.toReal := by
  rw [← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_add ha (mul_nonneg hw0 hb)] at h
  exact (ENNReal.ofReal_le_iff_le_toReal hI).1 h

/-- Let `p n N Q : ℝ≥0∞` with `N ≠ ⊤` and `Q ≠ ⊤`, and let `X = Q.toReal - N.toReal`. If
`p + N ≤ Q + n`, then `p + ENNReal.ofReal (-X) ≤ ENNReal.ofReal X + n`. The proof shows
`Q + ENNReal.ofReal (-X) = ENNReal.ofReal X + N`, adds `N` to both sides of the goal and cancels it.
-/
theorem add_ofReal_neg_le_of_add_le {p n N Q : ℝ≥0∞} {X : ℝ} (hN : N ≠ ⊤) (hQ : Q ≠ ⊤)
    (hX : Q.toReal - N.toReal = X)
    (h : p + N ≤ Q + n) : p + ENNReal.ofReal (-X) ≤ ENNReal.ofReal X + n := by
  have key : Q + ENNReal.ofReal (-X) = ENNReal.ofReal X + N := by
    rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.2 ⟨hQ, ENNReal.ofReal_ne_top⟩)
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hN⟩),
          ENNReal.toReal_add hQ ENNReal.ofReal_ne_top,
      ENNReal.toReal_add ENNReal.ofReal_ne_top hN]
    rcases le_total 0 X with hx | hx
    · rw [ENNReal.toReal_ofReal hx, ENNReal.ofReal_of_nonpos (by linarith)]
      simp
      linarith
    · rw [ENNReal.toReal_ofReal (by linarith), ENNReal.ofReal_of_nonpos hx]
      simp
      linarith
  have h2 : p + ENNReal.ofReal (-X) + N ≤ ENNReal.ofReal X + n + N :=
    calc p + ENNReal.ofReal (-X) + N = (p + N) + ENNReal.ofReal (-X) := by ring
      _ ≤ (Q + n) + ENNReal.ofReal (-X) := by gcongr
      _ = (Q + ENNReal.ofReal (-X)) + n := by ring
      _ = ENNReal.ofReal X + n + N := by rw [key]; ring
  exact (ENNReal.add_le_add_iff_right hN).1 h2

/-- For `a b : ℝ≥0∞` with `a ≠ ⊤` and `b ≠ ⊤`,
`a + ENNReal.ofReal (-(a.toReal - b.toReal)) ≤ ENNReal.ofReal (a.toReal - b.toReal) +
b`. The proof writes `a` and `b` as `ENNReal.ofReal` of nonnegative real numbers and splits on which
of the two is larger. -/
theorem add_ofReal_neg_toReal_sub_le (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a + ENNReal.ofReal (-(a.toReal - b.toReal)) ≤ ENNReal.ofReal (a.toReal - b.toReal) + b := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ a = ENNReal.ofReal x :=
    ⟨a.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal ha).symm⟩
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ b = ENNReal.ofReal t :=
    ⟨b.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hb).symm⟩
  rw [ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal ht]
  rcases le_total t x with h | h
  · rw [ENNReal.ofReal_of_nonpos (p := -(x - t)) (by linarith), add_zero,
      ← ENNReal.ofReal_add (by linarith) ht]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [ENNReal.ofReal_of_nonpos (p := x - t) (by linarith), zero_add,
      ← ENNReal.ofReal_add hx (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- For `x y : ℝ≥0∞`, `(x + y) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2)`. The proof uses `x + y ≤ 2 * max x y`. The
constant `4` is not sharp: the same bound holds with `2`. -/
theorem add_sq_le_four_mul_sq_add (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 4 * (x ^ 2 + y ^ 2) := by
  have h : x + y ≤ 2 * max x y := by
    rw [two_mul]; exact add_le_add (le_max_left _ _) (le_max_right _ _)
  calc (x + y) ^ 2 ≤ (2 * max x y) ^ 2 := by gcongr
    _ = 4 * max x y ^ 2 := by rw [mul_pow]; norm_num
    _ ≤ 4 * (x ^ 2 + y ^ 2) := by
      gcongr
      rcases le_total x y with h | h
      · rw [max_eq_right h]; exact le_add_self
      · rw [max_eq_left h]; exact le_self_add

/-- For `x y : ℝ≥0∞`, `(x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2`. The cases where `x` or `y` is `⊤` are
immediate, and the finite case reduces to `0 ≤ (x - y) ^ 2` for real numbers. -/
theorem add_sq_le_two_mul_sq_add (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  induction x using ENNReal.recTopCoe with
  | top => simp
  | coe x =>
    induction y using ENNReal.recTopCoe with
    | top => simp
    | coe y =>
      norm_cast
      rw [← NNReal.coe_le_coe]
      push_cast
      nlinarith [sq_nonneg ((x : ℝ) - y)]

/-- For `a b : ℝ≥0∞`, `(a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2)`. This is `add_sq_le_two_mul_sq_add` with
the factor `2` outside. -/
theorem ennreal_add_sq_le_two_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  rw [mul_add]
  exact add_sq_le_two_mul_sq_add a b

/-- Every `z : ℝ≥0∞` satisfies `z = (z ^ (1 / 2 : ℝ)) ^ (2 : ℝ)`. -/
theorem ennreal_eq_rpow_half_rpow_two (z : ℝ≥0∞) : z = (z ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
  rw [← ENNReal.rpow_mul]; norm_num

/-- If `X = h * X' * Z` for real numbers with `0 ≤ h` and `0 ≤ X'`, then
`ENNReal.ofReal X * Y = ENNReal.ofReal h * ENNReal.ofReal X' * (ENNReal.ofReal Z * Y)` for every `Y
: ℝ≥0∞`. -/
theorem ennreal_ofReal_mul_eq_of_eq_mul {X h X' Z : ℝ} (hh : 0 ≤ h) (hX' : 0 ≤ X')
    (e : X = h * X' * Z)
    (Y : ℝ≥0∞) :
    ENNReal.ofReal X * Y = ENNReal.ofReal h * ENNReal.ofReal X' * (ENNReal.ofReal Z * Y) := by
  rw [e, ENNReal.ofReal_mul (mul_nonneg hh hX'), ENNReal.ofReal_mul hh]
  ring

/-- For every real `t`, `‖t‖ₑ ≤ ENNReal.ofReal t + ENNReal.ofReal (-t)`. -/
theorem enorm_le_ofReal_add_ofReal_neg (t : ℝ) : ‖t‖ₑ ≤ ENNReal.ofReal t + ENNReal.ofReal (-t) := by
  rw [Real.eNorm_eq_ofReal_abs]
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
    exact le_self_add
  · rw [abs_of_nonpos h]
    exact le_add_self

/-- Let `v`, `x1`, `x2`, `x3`, `c` be real with `0 ≤ c`. If `‖v‖ ≤ c * x1 + c * x2 + c * x3`, then
`‖v‖ₑ ≤ ENNReal.ofReal c * ENNReal.ofReal x1 + ENNReal.ofReal c * ENNReal.ofReal x2 + ENNReal.ofReal
c * ENNReal.ofReal x3`. -/
theorem enorm_le_ofReal_mul_add_add {v x1 x2 x3 c : ℝ} (hc : 0 ≤ c)
    (h : ‖v‖ ≤ c * x1 + c * x2 + c * x3) :
    ‖v‖ₑ ≤ ENNReal.ofReal c * ENNReal.ofReal x1 + ENNReal.ofReal c * ENNReal.ofReal x2 +
      ENNReal.ofReal c * ENNReal.ofReal x3 := by
  rw [← ofReal_norm]
  calc ENNReal.ofReal ‖v‖ ≤ ENNReal.ofReal (c * x1 + c * x2 + c * x3) := ENNReal.ofReal_le_ofReal h
    _ ≤ ENNReal.ofReal (c * x1 + c * x2) + ENNReal.ofReal (c * x3) := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (c * x1) + ENNReal.ofReal (c * x2) + ENNReal.ofReal (c * x3) :=
        add_le_add_left ENNReal.ofReal_add_le _
    _ = _ := by rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hc]

/-- For reals `x`, `r` with `|x| ≤ r`, `‖x‖ₑ ≤ ENNReal.ofReal r`. -/
theorem enorm_le_ofReal_of_abs_le {x r : ℝ} (h : |x| ≤ r) : ‖x‖ₑ ≤ ENNReal.ofReal r := by
  rw [Real.eNorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal h

/-- For `y` in a normed additive commutative group and reals `0 ≤ c`, `0 ≤ s`, the bound
`‖y‖ ≤ 1 + c * s` implies `‖y‖ₑ ≤ 1 + ENNReal.ofReal c * ENNReal.ofReal s`. -/
theorem enorm_le_one_add_ofReal_mul_ofReal {Y : Type*} [NormedAddCommGroup Y] (y : Y) (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s)
    (h : ‖y‖ ≤ 1 + c * s) : ‖y‖ₑ ≤ 1 + ENNReal.ofReal c * ENNReal.ofReal s := by
  rw [← ofReal_norm, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (mul_nonneg hc hs)]
  exact ENNReal.ofReal_le_ofReal h

/-- For `x` in a normed additive group, `‖x‖ₑ ≤ 1 + ENNReal.ofReal (‖x‖ ^ 2)`. -/
theorem enorm_le_one_add_sq {E : Type*} [NormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ≤ 1 + ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]

/-- Let `r > 0`, `w` complex and `t` real with `‖w‖ ≤ ‖t‖`. Then
`‖w‖ₑ ≤ ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) + ENNReal.ofReal r * ‖t‖ₑ ^ 6`. -/
theorem enorm_le_rpow_add_mul_enorm_pow (r : ℝ) (hr : 0 < r) {w : ℂ} {t : ℝ} (h : ‖w‖ ≤ ‖t‖) :
    ‖w‖ₑ ≤ ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) + ENNReal.ofReal r * ‖t‖ₑ ^ 6 := by
  have h' := h.trans (le_rpow_neg_add_mul_pow_six r ‖t‖ hr)
  calc ‖w‖ₑ = ENNReal.ofReal ‖w‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (r ^ (-(1 / 5 : ℝ)) + r * ‖t‖ ^ 6) := ENNReal.ofReal_le_ofReal h'
    _ = ENNReal.ofReal (r ^ (-(1 / 5 : ℝ))) + ENNReal.ofReal r * ‖t‖ₑ ^ 6 := by
      rw [ENNReal.ofReal_add (Real.rpow_nonneg hr.le _) (by positivity), ENNReal.ofReal_mul hr.le,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- For real `μ > 0`, `q ≥ 0` and `a = 3 / 2 * q`,
`‖μ ^ a‖ₑ * ENNReal.ofReal (μ ^ (-(3 / 2 : ℝ))) ^ q = 1` in `ℝ≥0∞`. -/
theorem enorm_rpow_mul_ofReal_rpow_eq_one {μ : ℝ} (hμ : 0 < μ) {a q : ℝ} (hq : 0 ≤ q)
    (ha : a = 3 / 2 * q) :
    ‖μ ^ a‖ₑ * ENNReal.ofReal (μ ^ (-(3 / 2 : ℝ))) ^ q = 1 := by
  rw [eNorm_of_nonneg (Real.rpow_nonneg hμ.le _),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hμ.le _) hq,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hμ.le _), ← Real.rpow_mul hμ.le, ← Real.rpow_add hμ, ha,
    show 3 / 2 * q + -(3 / 2) * q = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one]

/-- For a real `a`, `‖a‖ₑ ^ 2 = ENNReal.ofReal (a * a)`. -/
theorem enorm_sq_eq_ofReal_mul_self (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a * a) := by
  rw [Real.eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg a), sq_abs, sq]

/-- For `x` in a normed additive group and a real `c`, if `‖x‖ ≤ c` then
`‖x‖ₑ ^ 2 ≤ ENNReal.ofReal (c ^ 2)`. -/
theorem enorm_sq_le_of_norm_le {E : Type*} [NormedAddCommGroup E] {x : E} {c : ℝ} (h : ‖x‖ ≤ c) :
    ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal (c ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)

/-- For complex `x`, `y`: `‖x - y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2` in `ℝ≥0∞`. The proof
transfers the real inequality `‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2` through `ENNReal.ofReal`. -/
theorem enorm_sub_sq_le (x y : ℂ) : ‖x - y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  have e : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z ↦ by
    rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, e]
  have h := norm_sub_le x y
  have key : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x - y)]
  calc ENNReal.ofReal (‖x - y‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal key
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

/-- Let `0 < κ`, `0 < γ`, `0 < P` and let `c N : ℝ≥0∞` with `c ≠ ⊤`. If
`N ≤ ENNReal.ofReal (K * (C * Real.exp (-(s₀ + n * P)) ^ κ)) + c * ENNReal.ofReal (Real.exp (-(s₀ +
n * P)) ^ γ * M)` for every natural number `n` with `0 ≤ s₀ + n * P`, then `N =
0`. The right side tends to `0` as `n` tends to infinity. -/
theorem eq_zero_of_le_ofReal_exp_rpow {K C κ γ M s₀ P : ℝ} {c N : ℝ≥0∞} (hκ : 0 < κ) (hγ : 0 < γ)
    (hP : 0 < P) (hcne : c ≠ ⊤)
    (hbound : ∀ n : ℕ, 0 ≤ s₀ + n * P → N ≤ ENNReal.ofReal
        (K * (C * Real.exp (-(s₀ + n * P)) ^ κ)) +
      c * ENNReal.ofReal (Real.exp (-(s₀ + n * P)) ^ γ * M)) : N = 0 := by
  have hsn : Tendsto (fun n : ℕ ↦ s₀ + n * P) atTop atTop :=
    tendsto_atTop_add_const_left _ s₀
      (tendsto_natCast_atTop_atTop.atTop_mul_const hP)
  have hμn : Tendsto (fun n : ℕ ↦ Real.exp (-(s₀ + n * P))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hsn
  have l1 : Tendsto (fun n : ℕ ↦ K * (C * Real.exp (-(s₀ + n * P)) ^ κ)) atTop (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto.comp hμn
    rw [Real.zero_rpow hκ.ne'] at this
    simpa using (this.const_mul C).const_mul K
  have l2 : Tendsto (fun n : ℕ ↦ Real.exp (-(s₀ + n * P)) ^ γ * M) atTop (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto.comp hμn
    rw [Real.zero_rpow hγ.ne'] at this
    simpa using this.mul_const M
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (K * (C * Real.exp (-(s₀ + n * P)) ^ κ)) +
      c * ENNReal.ofReal (Real.exp (-(s₀ + n * P)) ^ γ * M)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_ofReal l1).add
      (ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal l2) (Or.inr hcne))
    simpa using this
  have hev : ∀ᶠ n : ℕ in atTop, N ≤ ENNReal.ofReal (K * (C * Real.exp (-(s₀ + n * P)) ^ κ)) +
      c * ENNReal.ofReal (Real.exp (-(s₀ + n * P)) ^ γ * M) := by
    filter_upwards [hsn.eventually_ge_atTop 0] with n hn
    exact hbound n hn
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto hlim hev)

/-- In `ℝ≥0∞`, `4 * ENNReal.ofReal (1 / 2) = 2`. -/
theorem four_mul_ofReal_half_eq_two : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 2 := by
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat,
    show (4 : ℝ≥0∞) = 2 * 2 by
      norm_num, mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
    mul_one]

/-- For positive reals `p`, `q`, `r` with `p⁻¹ + q⁻¹ = r⁻¹`, the exponents `ENNReal.ofReal p`,
`ENNReal.ofReal q` and `ENNReal.ofReal r` form a Hölder triple in `ℝ≥0∞`. -/
theorem holderTriple_ofReal_of_inv_add_inv_eq {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p⁻¹ + q⁻¹ = r⁻¹) :
    ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) :=
  ⟨by rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_add (by positivity) (by positivity), h]⟩

/-- The exponents `6`, `6`, `3` form a Hölder triple in `ℝ≥0∞`: `ENNReal.HolderTriple 6 6 3`, that
is `6⁻¹ + 6⁻¹ = 3⁻¹`. -/
theorem holderTriple_six_six_three : ENNReal.HolderTriple 6 6 3 := by
  constructor
  have h6 : (6 : ℝ≥0∞) = 2 * 3 := by norm_num
  rw [← two_mul, h6, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- For `a : ℝ≥0∞`, the supremum over `n : ℕ` of `min a (n : ℝ≥0∞)` equals `a`. If `a = ⊤` this is
`⨆ n : ℕ, (n : ℝ≥0∞) = ⊤`, and otherwise some natural number is larger than `a`. -/
theorem iSup_min_natCast (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  refine le_antisymm (iSup_le fun n ↦ min_le_left _ _) ?_
  by_cases ha : a = ⊤
  · subst ha
    simp only [min_eq_right le_top]
    exact ENNReal.iSup_natCast.ge
  · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le n (min_eq_left hn.le).ge

/-- For a set `s`, a function `f : α → ℝ≥0∞` and a point `x`:
`s.indicator f x ^ (2 : ℝ) = s.indicator (fun x ↦ f x ^ 2) x`, with the real power `2` on the left
and the natural power on the right. -/
theorem indicator_rpow_two {α : Type*} (s : Set α) (f : α → ℝ≥0∞) (x : α) :
    s.indicator f x ^ (2 : ℝ) = s.indicator (fun x ↦ f x ^ 2) x := by
  rw [ENNReal.rpow_two]
  by_cases h : x ∈ s <;> simp [h]

/-- For `x : ℝ≥0∞` and real `r` with `0 ≤ r`, if `x ^ 2 ≤ ENNReal.ofReal (r ^ 2)` then
`x ≤ ENNReal.ofReal r`. -/
theorem le_ofReal_of_sq_le {x : ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) (h : x ^ 2 ≤ ENNReal.ofReal (r ^ 2)) :
    x ≤ ENNReal.ofReal r := by
  rw [ENNReal.ofReal_pow hr] at h
  exact not_lt.mp fun hlt ↦ absurd h (not_le.mpr (ENNReal.pow_lt_pow_left two_ne_zero hlt))

/-- For nonnegative reals `x` and `B`, if `ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (B ^ 2)` then
`x ≤ B`. -/
theorem le_of_ofReal_sq_le {x B : ℝ} (hx : 0 ≤ x) (hB : 0 ≤ B)
    (h : ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (B ^ 2)) : x ≤ B :=
  (sq_le_sq₀ hx hB).1 ((ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 h)

/-- In `ℝ≥0∞` the factor `ENNReal.ofReal (2 * Real.pi)` can be cancelled: if
`ENNReal.ofReal 2 * (ENNReal.ofReal (2 * Real.pi) * a) ≤ ENNReal.ofReal (2 * Real.pi) *
b`, then `ENNReal.ofReal 2 * a ≤ b`. -/
theorem le_of_ofReal_two_pi_mul_le {a b : ℝ≥0∞}
    (h : ENNReal.ofReal 2 * (ENNReal.ofReal (2 * Real.pi) * a) ≤ ENNReal.ofReal (2 * Real.pi) * b) :
    ENNReal.ofReal 2 * a ≤ b := by
  rw [mul_left_comm] at h
  exact (ENNReal.mul_le_mul_iff_right (by simp [Real.pi_pos]) ENNReal.ofReal_ne_top).1 h

/-- Every `x : ℝ≥0∞` satisfies `x ≤ 1 + x ^ 2`. -/
theorem le_one_add_sq (x : ℝ≥0∞) : x ≤ 1 + x ^ 2 := by
  rcases le_total x 1 with h | h
  · exact h.trans le_self_add
  · calc x = x ^ 1 := (pow_one x).symm
      _ ≤ x ^ 2 := pow_le_pow_right₀ h (by norm_num)
      _ ≤ 1 + x ^ 2 := le_add_self

/-- For `x a b : ℝ≥0∞`, if `x ^ 2 ≤ a * b` then `x ≤ a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ)`. -/
theorem le_rpow_mul_rpow_of_sq_le (x a b : ℝ≥0∞) (h : x ^ 2 ≤ a * b) :
    x ≤ a ^ (1 / 2 : ℝ) * b ^ (1 / 2 : ℝ) := by
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have e : x = (x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [e]
  exact ENNReal.rpow_le_rpow h (by norm_num)

/-- Let `x`, `D`, `K`, `g` be nonnegative reals and let `P : ℝ≥0∞` and `Q : Fin 3 → ℝ≥0∞` satisfy
`P ≠ ⊤` and `Q j ≠ ⊤` for all `j`. If
`ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (6 * D ^ 2) * (P + ∑ j, Q j) + ENNReal.ofReal K *
ENNReal.ofReal (g ^ 2)`, then `x ≤ 3 * D * (√(P.toReal) + ∑ j, √((Q j).toReal)) + √K *
g`. The proof moves the hypothesis to the reals and then takes square roots term by term. -/
theorem le_sqrt_toReal_of_ofReal_sq_le {x D K g : ℝ} {P : ℝ≥0∞} {Q : Fin 3 → ℝ≥0∞} (hx : 0 ≤ x)
    (hD : 0 ≤ D)
    (hK : 0 ≤ K) (hg : 0 ≤ g) (hP : P ≠ ⊤) (hQ : ∀ j, Q j ≠ ⊤)
    (h : ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (6 * D ^ 2) * (P + ∑ j, Q j) +
      ENNReal.ofReal K * ENNReal.ofReal (g ^ 2)) :
    x ≤ 3 * D * (Real.sqrt P.toReal + ∑ j, Real.sqrt (Q j).toReal) + Real.sqrt K * g := by
  have hs : P + ∑ j, Q j = ENNReal.ofReal (P.toReal + ∑ j, (Q j).toReal) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (Finset.sum_nonneg fun j _ ↦
        ENNReal.toReal_nonneg),
      ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hP]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ (ENNReal.ofReal_toReal (hQ j)).symm
  have hs0 : 0 ≤ P.toReal + ∑ j, (Q j).toReal :=
    add_nonneg ENNReal.toReal_nonneg (Finset.sum_nonneg fun j _ ↦ ENNReal.toReal_nonneg)
  rw [hs, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hK,
    ← ENNReal.ofReal_add (mul_nonneg (by positivity) hs0) (mul_nonneg hK (sq_nonneg _)),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg (by positivity) hs0)
      (mul_nonneg hK (sq_nonneg _)))] at h
  rw [Fin.sum_univ_three] at h ⊢
  exact le_add_sqrt_of_sq_le_add hx hD hK hg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg h

/-- The exponents `ENNReal.ofReal (6 / 5)`, `6` and `1` form a Hölder triple in `ℝ≥0∞`, that is,
`(ENNReal.ofReal (6 / 5))⁻¹ + 6⁻¹ = 1⁻¹`. -/
theorem holderTriple_ofReal_six_fifths_six_one :
    ENNReal.HolderTriple (ENNReal.ofReal (6 / 5)) 6 1 := by
  constructor
  have h6 : (6 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 6) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
  rw [h6, ← ENNReal.ofReal_inv_of_pos (by
    norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- For `a x : ℝ≥0∞`, `(a * x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a ^ 2 * x`. The outer exponent on the left
is the real number `2`, and the exponent of `a` on the right is the natural number `2`. -/
theorem mul_rpow_half_rpow_two (a x : ℝ≥0∞) : (a * x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a ^ 2 * x := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul]
  norm_num

/-- Let `d r : ℝ≥0∞` with `r ≠ ⊤` and let `t` be a real number. If
`d + ENNReal.ofReal (-t) ≤ ENNReal.ofReal t + r`, then `d ≠ ⊤` and `d.toReal ≤ t + r.toReal`. The
proof gets `d ≠ ⊤` because the right side is finite, then applies `ENNReal.toReal` to both sides and
splits on the sign of `t`. -/
theorem ne_top_and_toReal_le_add_toReal {d r : ℝ≥0∞} {t : ℝ} (hr : r ≠ ⊤)
    (h : d + ENNReal.ofReal (-t) ≤ ENNReal.ofReal t + r) :
    d ≠ ⊤ ∧ d.toReal ≤ t + r.toReal := by
  have hd : d ≠ ⊤ := by
    intro hd
    rw [hd, top_add] at h
    exact (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hr⟩) (top_le_iff.1 h)
  refine ⟨hd, ?_⟩
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hr⟩) h
  rw [ENNReal.toReal_add hd ENNReal.ofReal_ne_top, ENNReal.toReal_add ENNReal.ofReal_ne_top hr,
    ENNReal.toReal_ofReal', ENNReal.toReal_ofReal'] at h2
  rcases le_total 0 t with ht | ht
  · rw [max_eq_right (by linarith : -t ≤ 0), max_eq_left ht] at h2
    linarith
  · rw [max_eq_left (by linarith : 0 ≤ -t), max_eq_right ht] at h2
    linarith

/-- For `a n : ℝ≥0∞` and a real number `x`, if `a + ENNReal.ofReal (-x) ≤ ENNReal.ofReal x + n` and
`n ≠ ⊤`, then `a ≠ ⊤`. -/
theorem ne_top_of_add_ofReal_neg_le {a n : ℝ≥0∞} {x : ℝ}
    (h : a + ENNReal.ofReal (-x) ≤ ENNReal.ofReal x + n)
    (hn : n ≠ ⊤) : a ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hn⟩) (le_trans le_self_add h)

/-- Let `a` be a real number, `e : Fin n → ℝ` with `e β ≤ 0` for all `β`, and `mm c d : Fin k → ℝ`
with `mm β = -(c β) - d β`, `0 ≤ c β` and `0 ≤ d β` for all `β`. Then
`ENNReal.ofReal |a + ∑ β, e β + ∑ β, mm β| ≤ ENNReal.ofReal |a| + ∑ β, ENNReal.ofReal (-e β) + ∑ β,
(ENNReal.ofReal (c β) + ENNReal.ofReal (d
β))`. The proof uses the triangle inequality, the signs of the two sums, and additivity of
`ENNReal.ofReal` on nonnegative numbers. -/
theorem ofReal_abs_add_sum_add_sum_le {n k : ℕ} (a : ℝ) (e : Fin n → ℝ) (mm c d : Fin k → ℝ)
    (he : ∀ β, e β ≤ 0)
    (hmm : ∀ β, mm β = -(c β) - d β) (hc : ∀ β, 0 ≤ c β) (hd : ∀ β, 0 ≤ d β) :
    ENNReal.ofReal |a + ∑ β, e β + ∑ β, mm β| ≤
      ENNReal.ofReal |a| + ∑ β, ENNReal.ofReal (-e β) + ∑ β,
          (ENNReal.ofReal (c β) + ENNReal.ofReal (d β)) := by
  have h1 : |∑ β, e β| ≤ ∑ β, -e β := by
    rw [abs_of_nonpos (Finset.sum_nonpos fun β _ ↦ he β), Finset.sum_neg_distrib]
  have h2 : |∑ β, mm β| ≤ ∑ β, (c β + d β) := by
    have hs : ∑ β, mm β = -∑ β, (c β + d β) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ ↦ by rw [hmm β]; ring
    rw [hs, abs_neg, abs_of_nonneg (Finset.sum_nonneg fun β _ ↦ add_nonneg (hc β) (hd β))]
  have h3 : |a + ∑ β, e β + ∑ β, mm β| ≤ |a| + ∑ β, -e β + ∑ β, (c β + d β) := by
    have := abs_add_le (a + ∑ β, e β) (∑ β, mm β)
    have := abs_add_le a (∑ β, e β)
    linarith
  have n1 : 0 ≤ ∑ β, -e β := Finset.sum_nonneg fun β _ ↦ neg_nonneg.2 (he β)
  have n2 : 0 ≤ ∑ β, (c β + d β) := Finset.sum_nonneg fun β _ ↦ add_nonneg (hc β) (hd β)
  calc ENNReal.ofReal |a + ∑ β, e β + ∑ β, mm β|
      ≤ ENNReal.ofReal (|a| + ∑ β, -e β + ∑ β, (c β + d β)) := ENNReal.ofReal_le_ofReal h3
    _ = _ := by
      rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg _) n1) n2,
          ENNReal.ofReal_add (abs_nonneg _) n1,
        ENNReal.ofReal_sum_of_nonneg (fun β _ ↦ neg_nonneg.2 (he β)),
        ENNReal.ofReal_sum_of_nonneg (fun β _ ↦ add_nonneg (hc β) (hd β))]
      congr 1
      exact Finset.sum_congr rfl fun β _ ↦ ENNReal.ofReal_add (hc β) (hd β)

/-- For a real `a`, `ENNReal.ofReal |a| = ENNReal.ofReal a + ENNReal.ofReal (-a)`: the absolute
value is the sum of the positive part and the negative part. -/
theorem ofReal_abs_eq_ofReal_add_ofReal_neg (a : ℝ) :
    ENNReal.ofReal |a| = ENNReal.ofReal a + ENNReal.ofReal (-a) := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (by linarith : -a ≤ 0), add_zero]
  · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]

/-- For real numbers with `0 ≤ K₁`, `0 ≤ K₂`, `0 ≤ D`, `0 ≤ A` and `|r| ≤ K₁ * D + K₂ * A`,
`ENNReal.ofReal |r| ≤ ENNReal.ofReal K₁ * ENNReal.ofReal D + ENNReal.ofReal K₂ * ENNReal.ofReal
A`. -/
theorem ofReal_abs_le_ofReal_mul_add {r D A K₁ K₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hD : 0 ≤ D)
    (hA : 0 ≤ A)
    (h : |r| ≤ K₁ * D + K₂ * A) :
    ENNReal.ofReal (|r|) ≤ ENNReal.ofReal K₁ * ENNReal.ofReal D + ENNReal.ofReal K₂ *
        ENNReal.ofReal A := by
  rw [← ENNReal.ofReal_mul hK₁, ← ENNReal.ofReal_mul hK₂,
    ← ENNReal.ofReal_add (mul_nonneg hK₁ hD) (mul_nonneg hK₂ hA)]
  exact ENNReal.ofReal_le_ofReal h

/-- For nonnegative reals `x`, `y`, `z`, `w`,
`ENNReal.ofReal x + ENNReal.ofReal y + ENNReal.ofReal z + ENNReal.ofReal w = ENNReal.ofReal (x + y +
z + w)`. -/
theorem ofReal_add_four {x y z w : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    ENNReal.ofReal x + ENNReal.ofReal y + ENNReal.ofReal z + ENNReal.ofReal w =
        ENNReal.ofReal (x + y + z + w) := by
  rw [ENNReal.ofReal_add (by
    linarith) hw, ENNReal.ofReal_add (by linarith) hz, ENNReal.ofReal_add hx hy]

/-- For real numbers with `0 ≤ p`, `0 ≤ r` and `p ≤ T + r`,
`ENNReal.ofReal p + ENNReal.ofReal (-T) ≤ ENNReal.ofReal T + ENNReal.ofReal r`. -/
theorem ofReal_add_neg_le_of_le_add {p T r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (h : p ≤ T + r) :
    ENNReal.ofReal p + ENNReal.ofReal (-T) ≤ ENNReal.ofReal T + ENNReal.ofReal r := by
  rcases le_total 0 T with hT | hT
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -T ≤ 0), add_zero, ← ENNReal.ofReal_add hT hr]
    exact ENNReal.ofReal_le_ofReal h
  · rw [ENNReal.ofReal_of_nonpos hT, zero_add, ← ENNReal.ofReal_add hp (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- For real numbers with `0 ≤ a`, `0 ≤ s` and `a - s ≤ X`,
`ENNReal.ofReal a + ENNReal.ofReal (-X) ≤ ENNReal.ofReal X + ENNReal.ofReal s`. -/
theorem ofReal_add_neg_le_of_sub_le {a s X : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (h : a - s ≤ X) :
    ENNReal.ofReal a + ENNReal.ofReal (-X) ≤ ENNReal.ofReal X + ENNReal.ofReal s := by
  rcases le_total 0 X with hX | hX
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -X ≤ 0), add_zero, ← ENNReal.ofReal_add hX hs]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [← ENNReal.ofReal_add ha (by linarith : 0 ≤ -X), ENNReal.ofReal_of_nonpos hX, zero_add]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- For real `a` with `0 ≤ a`, `ENNReal.ofReal (4 * a) ^ (1 / (2 : ℝ)) = ENNReal.ofReal (2 * √a)`.
-/
theorem ofReal_four_mul_rpow_half (a : ℝ) (ha : 0 ≤ a) :
    ENNReal.ofReal (4 * a) ^ (1 / (2 : ℝ)) = ENNReal.ofReal (2 * Real.sqrt a) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (by norm_num)]
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h4]

/-- Let `M`, `R2`, `X`, `Y` be nonnegative reals and `u`, `d` reals. If
`u ≤ d + M * (3 * X + R2 * Y)`, then
`ENNReal.ofReal u ≤ ENNReal.ofReal d +
ENNReal.ofReal M * (3 * ENNReal.ofReal X + ENNReal.ofReal R2 * ENNReal.ofReal Y)`. -/
theorem ofReal_le_ofReal_add_mul_of_le (u d M R2 X Y : ℝ) (hM : 0 ≤ M) (hR : 0 ≤ R2) (hX : 0 ≤ X)
    (hY : 0 ≤ Y)
    (h : u ≤ d + M * (3 * X + R2 * Y)) :
    ENNReal.ofReal u ≤ ENNReal.ofReal d
      + ENNReal.ofReal M * (3 * ENNReal.ofReal X + ENNReal.ofReal R2 * ENNReal.ofReal Y) := by
  refine (ENNReal.ofReal_le_ofReal h).trans (ENNReal.ofReal_add_le.trans (le_of_eq ?_))
  rw [ENNReal.ofReal_mul hM, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_mul hR, ENNReal.ofReal_ofNat]

/-- For every real `x`, `ENNReal.ofReal (max x 0) = ENNReal.ofReal x`. -/
theorem ofReal_max_zero (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

/-- For real numbers with `0 ≤ d`, `0 ≤ a`, `0 < c` and `0 ≤ b`,
`ENNReal.ofReal (d * (a / c + b)) = ENNReal.ofReal (d / c) * ENNReal.ofReal a + ENNReal.ofReal (d *
b)`. -/
theorem ofReal_mul_div_add_eq (d a b c : ℝ) (hd : 0 ≤ d) (ha : 0 ≤ a) (hc : 0 < c) (hb : 0 ≤ b) :
    ENNReal.ofReal (d * (a / c + b)) = ENNReal.ofReal (d / c) * ENNReal.ofReal a +
        ENNReal.ofReal (d * b) := by
  rw [← ENNReal.ofReal_mul (div_nonneg hd hc.le), ← ENNReal.ofReal_add
      (mul_nonneg (div_nonneg hd hc.le) ha)
    (mul_nonneg hd hb)]
  congr 1
  ring

/-- Let `0 ≤ w`, `w ≤ Bw`, `0 ≤ a`, `0 ≤ M`, `e1 ≤ M * s1`, `e2 ≤ M * s2`, `e3 ≤ M * s3`,
`e4 ≤ M * s4` be real numbers, with `s1`, `s2`, `s3`, `s4` nonnegative. Then
`ENNReal.ofReal (w * a * (e1 + e2 + e3 + e4)) ≤ ENNReal.ofReal (Bw * M) * (ENNReal.ofReal (a * s1) +
ENNReal.ofReal (a * s2) + ENNReal.ofReal (a * s3) + ENNReal.ofReal (a *
s4))`. The proof shows the real inequality `w * a * (e1 + e2 + e3 + e4) ≤ (Bw * M) * (a * s1 + a *
s2 + a * s3 + a *
s4)` and then uses that `ENNReal.ofReal` is monotone, and additive and multiplicative on nonnegative
numbers. -/
theorem ofReal_mul_mul_sum_four_le {w a Bw M e1 e2 e3 e4 s1 s2 s3 s4 : ℝ} (hw : 0 ≤ w)
    (hwB : w ≤ Bw) (ha : 0 ≤ a)
    (hM : 0 ≤ M) (h1 : e1 ≤ M * s1) (h2 : e2 ≤ M * s2) (h3 : e3 ≤ M * s3) (h4 : e4 ≤ M * s4)
    (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3) (hs4 : 0 ≤ s4) :
    ENNReal.ofReal (w * a * (e1 + e2 + e3 + e4)) ≤
      ENNReal.ofReal (Bw * M) * (ENNReal.ofReal (a * s1) + ENNReal.ofReal (a * s2) +
          ENNReal.ofReal (a * s3)
        + ENNReal.ofReal (a * s4)) := by
  have hBw : 0 ≤ Bw := le_trans hw hwB
  have hle : w * a * (e1 + e2 + e3 + e4) ≤ (Bw * M) * (a * s1 + a * s2 + a * s3 + a * s4) := by
    have hwa : 0 ≤ w * a := mul_nonneg hw ha
    have hs : e1 + e2 + e3 + e4 ≤ M * (s1 + s2 + s3 + s4) := by linarith
    calc w * a * (e1 + e2 + e3 + e4) ≤ w * a * (M * (s1 + s2 + s3 + s4)) :=
             mul_le_mul_of_nonneg_left hs hwa
      _ = (w * M) * (a * s1 + a * s2 + a * s3 + a * s4) := by ring
      _ ≤ (Bw * M) * (a * s1 + a * s2 + a * s3 + a * s4) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwB hM) ?_
          have := mul_nonneg ha hs1; have := mul_nonneg ha hs2
          have := mul_nonneg ha hs3; have := mul_nonneg ha hs4
          linarith
  refine le_trans (ENNReal.ofReal_le_ofReal hle) (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (mul_nonneg hBw hM), ENNReal.ofReal_add (by
    positivity) (mul_nonneg ha hs4),
    ENNReal.ofReal_add (by positivity) (mul_nonneg ha hs3),
    ENNReal.ofReal_add (mul_nonneg ha hs1) (mul_nonneg ha hs2)]

/-- For nonnegative reals `M`, `X`, `S`,
`ENNReal.ofReal M * (ENNReal.ofReal X * ENNReal.ofReal (2 * S) + ENNReal.ofReal (X ^ 2)) ≤
ENNReal.ofReal (2 * M * (X * S + X ^ 2))`. -/
theorem ofReal_mul_ofReal_mul_add_sq_le {M X S : ℝ} (hM : 0 ≤ M) (hX : 0 ≤ X) (hS : 0 ≤ S) :
    ENNReal.ofReal M * (ENNReal.ofReal X * ENNReal.ofReal (2 * S) + ENNReal.ofReal (X ^ 2)) ≤
      ENNReal.ofReal (2 * M * (X * S + X ^ 2)) := by
  rw [← ENNReal.ofReal_mul hX, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hM]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_nonneg hM (sq_nonneg X), mul_nonneg (mul_nonneg hM hX) hS]

/-- For real `C₀`, `x`, `y` with `0 ≤ x`,
`ENNReal.ofReal C₀ * ENNReal.ofReal x * ENNReal.ofReal y ≤ ENNReal.ofReal ((|C₀| + 1) * x * y)`. -/
theorem ofReal_mul_ofReal_mul_ofReal_le (C₀ x y : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal C₀ * ENNReal.ofReal x * ENNReal.ofReal y ≤
      ENNReal.ofReal ((|C₀| + 1) * x * y) := by
  have hD : 0 ≤ |C₀| + 1 := by positivity
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (|C₀| + 1) * x), ENNReal.ofReal_mul hD]
  gcongr
  exact (le_abs_self C₀).trans (by linarith)

/-- For real numbers with `0 ≤ A` and `0 ≤ w₀`,
`ENNReal.ofReal A * (ENNReal.ofReal (S ^ 2) + ENNReal.ofReal w₀ * ENNReal.ofReal (D ^ 2)) =
ENNReal.ofReal (A * (S ^ 2 + w₀ * D ^ 2))`. -/
theorem ofReal_mul_ofReal_sq_add_mul_sq {A S D w₀ : ℝ} (hA : 0 ≤ A) (hw0 : 0 ≤ w₀) :
    ENNReal.ofReal A * (ENNReal.ofReal (S ^ 2) + ENNReal.ofReal w₀ * ENNReal.ofReal (D ^ 2)) =
      ENNReal.ofReal (A * (S ^ 2 + w₀ * D ^ 2)) := by
  rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg hw0 (sq_nonneg _)),
    ENNReal.ofReal_mul hw0]

/-- For a real `a ≥ 0` and `y : ℝ≥0∞`,
`ENNReal.ofReal a * y ^ (3 / 4 : ℝ) ≤ ENNReal.ofReal (4 * π ^ 2) * y + ENNReal.ofReal (a * (a / (4 *
π ^ 2)) ^ 3)`. For finite `y` the proof sets `q = y ^ (1 / 4 : ℝ)` and compares `q` with `a / (4 * π
^ 2)`: if `q` is the smaller one the second term on the right bounds `a * q ^
3`, otherwise the first term does. -/
theorem ofReal_mul_rpow_three_quarters_le {a : ℝ} (ha : 0 ≤ a) (y : ℝ≥0∞) :
    ENNReal.ofReal a * y ^ (3 / 4 : ℝ) ≤
      ENNReal.ofReal (4 * π ^ 2) * y + ENNReal.ofReal (a * (a / (4 * π ^ 2)) ^ 3) := by
  have hpi : 0 < 4 * π ^ 2 := by positivity
  rcases eq_or_ne y ⊤ with rfl | hy
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hpi).ne']
    simp
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 ≤ r ∧ y = ENNReal.ofReal r :=
    ⟨y.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hy).symm⟩
  have hb0 : 0 ≤ a / (4 * π ^ 2) := div_nonneg ha hpi.le
  rw [ENNReal.ofReal_rpow_of_nonneg hr (by norm_num), ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_mul hpi.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hq0 : 0 ≤ r ^ (1 / 4 : ℝ) := Real.rpow_nonneg hr _
  have hr3 : r ^ (3 / 4 : ℝ) = (r ^ (1 / 4 : ℝ)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
  have hr4 : r = (r ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
  have hab : a = 4 * π ^ 2 * (a / (4 * π ^ 2)) := by field_simp
  rw [hr3]
  conv_rhs => rw [hr4]
  rcases le_total (r ^ (1 / 4 : ℝ)) (a / (4 * π ^ 2)) with h | h
  · have h3 : (r ^ (1 / 4 : ℝ)) ^ 3 ≤ (a / (4 * π ^ 2)) ^ 3 := pow_le_pow_left₀ hq0 h 3
    have := mul_le_mul_of_nonneg_left h3 ha
    have := mul_nonneg hpi.le (pow_nonneg hq0 4)
    linarith
  · have key : a * (r ^ (1 / 4 : ℝ)) ^ 3 ≤ 4 * π ^ 2 * (r ^ (1 / 4 : ℝ)) ^ 4 := by
      calc a * (r ^ (1 / 4 : ℝ)) ^ 3 = 4 * π ^ 2 * ((a / (4 * π ^ 2)) * (r ^ (1 / 4 : ℝ)) ^ 3) := by
            field_simp
        _ ≤ 4 * π ^ 2 * (r ^ (1 / 4 : ℝ) * (r ^ (1 / 4 : ℝ)) ^ 3) := by gcongr
        _ = 4 * π ^ 2 * (r ^ (1 / 4 : ℝ)) ^ 4 := by ring
    have := mul_nonneg ha (pow_nonneg hb0 3)
    linarith

/-- For a real `a ≥ 0` and `y : ℝ≥0∞`,
`ENNReal.ofReal a * y ^ (3 / 4 : ℝ) ≤ y + ENNReal.ofReal (a ^ 4)`. The case `y = ⊤` is trivial, and
for finite `y` it reduces to the real inequality `a * q ^ 3 ≤ q ^ 4 + a ^ 4` with
`q = y.toReal ^ (1 / 4 : ℝ)`, proved by comparing `q` with `a`. -/
theorem ofReal_mul_rpow_three_quarters_le_add {a : ℝ} (ha : 0 ≤ a) (y : ℝ≥0∞) :
    ENNReal.ofReal a * y ^ (3 / 4 : ℝ) ≤ y + ENNReal.ofReal (a ^ 4) := by
  rcases eq_or_ne y ⊤ with rfl | hy
  · simp
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 ≤ r ∧ y = ENNReal.ofReal r :=
    ⟨y.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hy).symm⟩
  rw [ENNReal.ofReal_rpow_of_nonneg hr (by norm_num), ← ENNReal.ofReal_mul ha,
    ← ENNReal.ofReal_add hr (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hq0 : 0 ≤ r ^ (1 / 4 : ℝ) := Real.rpow_nonneg hr _
  have hr3 : r ^ (3 / 4 : ℝ) = (r ^ (1 / 4 : ℝ)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
  have hr4 : r = (r ^ (1 / 4 : ℝ)) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]; norm_num
  rw [hr3]
  conv_rhs => rw [hr4]
  rcases le_total (r ^ (1 / 4 : ℝ)) a with h | h
  · have h3 : (r ^ (1 / 4 : ℝ)) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hq0 h 3
    have := mul_le_mul_of_nonneg_left h3 ha
    have := pow_nonneg hq0 4
    nlinarith
  · have := mul_le_mul_of_nonneg_right h (pow_nonneg hq0 3)
    have := pow_nonneg ha 4
    nlinarith

/-- For real numbers with `0 ≤ x`, `0 ≤ y` and `x ≤ m`,
`ENNReal.ofReal ((x * y) ^ 2) ≤ ENNReal.ofReal ((m * y) ^ 2)`. -/
theorem ofReal_mul_sq_le_ofReal_mul_sq {x m y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x ≤ m) :
    ENNReal.ofReal ((x * y) ^ 2) ≤ ENNReal.ofReal ((m * y) ^ 2) :=
  ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (mul_nonneg hx hy) (mul_le_mul_of_nonneg_right h hy) 2)

/-- For reals `f` and `g`,
`ENNReal.ofReal (-f) + ENNReal.ofReal g + ENNReal.ofReal (f - g) = ENNReal.ofReal f + ENNReal.ofReal
(-g) + ENNReal.ofReal (-(f -
g))`. Both sides are finite, and after `toReal` the identity follows from `max x 0 - max (-x) 0 =
x` applied to `f`, `g` and `f - g`. -/
theorem ofReal_neg_add_ofReal_add_ofReal_sub (f g : ℝ) :
    ENNReal.ofReal (-f) + ENNReal.ofReal g + ENNReal.ofReal (f - g)
      = ENNReal.ofReal f + ENNReal.ofReal (-g) + ENNReal.ofReal (-(f - g)) := by
  refine (ENNReal.toReal_eq_toReal_iff' ?_ ?_).1 ?_
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
      ENNReal.ofReal_ne_top⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩,
      ENNReal.ofReal_ne_top⟩
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
      ENNReal.ofReal_ne_top, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
      ENNReal.ofReal_ne_top, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal']
  have h1 := max_zero_sub_max_neg_zero_eq_self f
  have h2 := max_zero_sub_max_neg_zero_eq_self g
  have h3 := max_zero_sub_max_neg_zero_eq_self (f - g)
  linarith

/-- For real numbers `a`, `b`, `c`,
`ENNReal.ofReal (-(a + b + c)) ≤ ENNReal.ofReal (-a) + ENNReal.ofReal (-b) + ENNReal.ofReal
(-c)`. -/
theorem ofReal_neg_add_three_le (a b c : ℝ) :
    ENNReal.ofReal (-(a + b + c)) ≤ ENNReal.ofReal (-a) + ENNReal.ofReal (-b) +
        ENNReal.ofReal (-c) := by
  rw [neg_add, neg_add]
  exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)

/-- For `x` in a normed additive commutative group, `ENNReal.ofReal (‖x‖ ^ 6) = ‖x‖ₑ ^ (6 : ℝ)`,
where the right side is a real power in `ℝ≥0∞`. -/
theorem ofReal_norm_pow_six_eq_enorm_rpow {X : Type*} [NormedAddCommGroup X] (x : X) :
    ENNReal.ofReal (‖x‖ ^ 6) = ‖x‖ₑ ^ (6 : ℝ) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  norm_cast

/-- For a real `t ≥ 0`, a natural number `n` and a real `p ≥ 0`,
`ENNReal.ofReal (t ^ n) ^ p = ENNReal.ofReal (t ^ ((n : ℝ) * p))`. -/
theorem ofReal_pow_rpow {t : ℝ} (ht : 0 ≤ t) (n : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (t ^ n) ^ p = ENNReal.ofReal (t ^ ((n : ℝ) * p)) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (pow_nonneg ht n) hp, ← Real.rpow_natCast, ← Real.rpow_mul ht]

/-- For a real `t ≥ 0`, `ENNReal.ofReal (t ^ 6) ^ (1 / 6 : ℝ) = ENNReal.ofReal t`. -/
theorem ofReal_pow_six_rpow_sixth {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (t ^ 6) ^ (1 / 6 : ℝ) = ENNReal.ofReal t := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_natCast,
    ← Real.rpow_mul ht]
  norm_num

/-- For a real `t ≥ 0`, `ENNReal.ofReal t ^ (6 : ℝ) = ENNReal.ofReal (t ^ 6)`. The exponent on the
left is the real number `6`, and the exponent on the right is the natural number `6`. -/
theorem ofReal_rpow_six {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal t ^ (6 : ℝ) = ENNReal.ofReal (t ^ 6) := by
  rw [ENNReal.ofReal_rpow_of_nonneg ht (by norm_num), show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]

/-- For a real `t ≥ 0`, `ENNReal.ofReal (t ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = ENNReal.ofReal t`. -/
theorem ofReal_rpow_three_halves_rpow_two_thirds {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (t ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) = ENNReal.ofReal t := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul ht]
  norm_num

/-- For a real `t ≥ 0`, `ENNReal.ofReal t ^ (2 : ℝ) = ENNReal.ofReal (t ^ 2)`. The exponent on the
left is the real number `2`, and the exponent on the right is the natural number `2`. -/
theorem ofReal_rpow_two {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal t ^ (2 : ℝ) = ENNReal.ofReal (t ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg ht (by norm_num), Real.rpow_two]

/-- Let `v`, `K`, `M` be nonnegative reals. If `a ^ 2 ≤ M * (v * K + v ^ 2)`, then
`ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal M * (ENNReal.ofReal (v ^ 2) ^ (1 / 2 : ℝ) * ENNReal.ofReal
K + ENNReal.ofReal (v ^ 2))`. The proof uses `ENNReal.ofReal (v ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal
v`. -/
theorem ofReal_sq_le_mul_rpow_half_add {a v K M : ℝ} (hv : 0 ≤ v) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (h : a ^ 2 ≤ M * (v * K + v ^ 2)) :
    ENNReal.ofReal (a ^ 2) ≤ ENNReal.ofReal M *
      (ENNReal.ofReal (v ^ 2) ^ (1 / 2 : ℝ) * ENNReal.ofReal K + ENNReal.ofReal (v ^ 2)) := by
  have e : ENNReal.ofReal (v ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal v := by
    rw [ENNReal.ofReal_pow hv, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [e, ← ENNReal.ofReal_mul hv, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hM]
  exact ENNReal.ofReal_le_ofReal h

/-- For real numbers with `0 ≤ x` and `x ≤ y`, `ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (y ^ 2)`. -/
theorem ofReal_sq_le_ofReal_sq {x y : ℝ} (hx : 0 ≤ x) (h : x ≤ y) :
    ENNReal.ofReal (x ^ 2) ≤ ENNReal.ofReal (y ^ 2) :=
  ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hx h 2)

/-- For nonnegative reals `a` and `b`,
`ENNReal.ofReal a ^ 2 * ENNReal.ofReal b ^ 2 = ENNReal.ofReal ((a * b) ^ 2)`. -/
theorem ofReal_sq_mul_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a ^ 2 * ENNReal.ofReal b ^ 2 = ENNReal.ofReal ((a * b) ^ 2) := by
  rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

/-- For real `x` with `0 ≤ x`, `ENNReal.ofReal (√x) ^ 2 = ENNReal.ofReal x`. -/
theorem ofReal_sqrt_sq {x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal (Real.sqrt x) ^ 2 = ENNReal.ofReal x :=
    by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hx]

/-- For reals `0 ≤ x` and `0 ≤ y`,
`ENNReal.ofReal (x - y) + ENNReal.ofReal y = ENNReal.ofReal (y - x) + ENNReal.ofReal x`. -/
theorem ofReal_sub_add_ofReal_comm {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal (x - y) + ENNReal.ofReal y = ENNReal.ofReal (y - x) + ENNReal.ofReal x := by
  rcases le_total x y with hxy | hxy
  · rw [ENNReal.ofReal_of_nonpos (by linarith), zero_add, ← ENNReal.ofReal_add (by linarith) hx]
    congr 1
    ring
  · rw [ENNReal.ofReal_of_nonpos (show y - x ≤ 0 by
      linarith), zero_add, ← ENNReal.ofReal_add (by linarith) hy]
    congr 1
    ring

/-- For a family `a` in a normed additive group indexed by a finite type,
`ENNReal.ofReal (∑ i, ‖a i‖ ^ 2) = ∑ i, ‖a i‖ₑ ^ 2`. -/
theorem ofReal_sum_norm_sq {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] (a : ι → F) :
    ENNReal.ofReal (∑ i, ‖a i‖ ^ 2) = ∑ i, ‖a i‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sq_nonneg _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- For a real family `F a b c` indexed by `a b c : Fin 3`, `ENNReal.ofReal` commutes with the
triple sum of the squares:
`ENNReal.ofReal (∑ a, ∑ b, ∑ c, F a b c * F a b c) = ∑ a, ∑ b, ∑ c, ENNReal.ofReal (F a b c * F a b
c)`. -/
theorem ofReal_sum_sum_sum_mul_self (F : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    ENNReal.ofReal (∑ a, ∑ b, ∑ c, F a b c * F a b c) =
      ∑ a, ∑ b, ∑ c, ENNReal.ofReal (F a b c * F a b c) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun a _ ↦
    Finset.sum_nonneg fun b _ ↦ Finset.sum_nonneg fun c _ ↦ mul_self_nonneg _]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun b _ ↦ Finset.sum_nonneg fun c _ ↦ mul_self_nonneg _]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun c _ ↦ mul_self_nonneg _]

/-- In `ℝ≥0∞`, if `ENNReal.ofReal 2 * a0 ≤ b0`, `ENNReal.ofReal 2 * a1 ≤ b1` and
`ENNReal.ofReal 2 * a2 ≤ b2`, then `ENNReal.ofReal 2 * (c * (a0 + a1 + a2)) ≤ c * (b0 + b1 + b2)`
for every `c`. -/
theorem ofReal_two_mul_mul_add_le {c a0 a1 a2 b0 b1 b2 : ℝ≥0∞} (h0 : ENNReal.ofReal 2 * a0 ≤ b0)
    (h1 : ENNReal.ofReal 2 * a1 ≤ b1) (h2 : ENNReal.ofReal 2 * a2 ≤ b2) :
    ENNReal.ofReal 2 * (c * (a0 + a1 + a2)) ≤ c * (b0 + b1 + b2) := by
  calc ENNReal.ofReal 2 * (c * (a0 + a1 + a2))
      = c * (ENNReal.ofReal 2 * a0 + ENNReal.ofReal 2 * a1 + ENNReal.ofReal 2 * a2) := by ring
    _ ≤ c * (b0 + b1 + b2) := by gcongr

/-- In `ℝ≥0∞`, `1 ≤ 3 / 2`. -/
theorem one_le_three_halves_ennreal : (1 : ℝ≥0∞) ≤ 3 / 2 := by
  rw [ENNReal.le_div_iff_mul_le (by simp) (by simp)]
  norm_num

/-- For `A K B : ℝ≥0∞`,
`(A * K) ^ (1 / 2 : ℝ) * (K * B) ^ (1 / 3 : ℝ) * (A * B) ^ (1 / 6 : ℝ) = A ^ (2 / 3 : ℝ) * K ^ (5 /
6 : ℝ) * B ^ (1 / 2 :
ℝ)`. Each power of a product is split into a product of powers, and the exponents of each variable
are added. -/
theorem pairwise_mul_rpow_eq_rpow_mul_rpow (A K B : ℝ≥0∞) :
    (A * K) ^ (1 / 2 : ℝ) * (K * B) ^ (1 / 3 : ℝ) * (A * B) ^ (1 / 6 : ℝ) =
      A ^ (2 / 3 : ℝ) * K ^ (5 / 6 : ℝ) * B ^ (1 / 2 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  have eA : A ^ (2 / 3 : ℝ) = A ^ (1 / 2 : ℝ) * A ^ (1 / 6 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  have eK : K ^ (5 / 6 : ℝ) = K ^ (1 / 2 : ℝ) * K ^ (1 / 3 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  have eB : B ^ (1 / 2 : ℝ) = B ^ (1 / 3 : ℝ) * B ^ (1 / 6 : ℝ) := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  rw [eA, eK, eB]
  ring

/-- The real number `1 / 4` equals `3 / 2 * (1 / (6 : ℝ≥0∞)).toReal`. -/
theorem quarter_eq_mul_toReal_sixth : (1 / 4 : ℝ) = 3 / 2 * (1 / (6 : ℝ≥0∞)).toReal := by
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  norm_num

/-- For `a : ℝ≥0∞` and a real `c ≥ 0`, if `a ≤ ENNReal.ofReal (c ^ 2)` then
`a ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c`. -/
theorem rpow_half_le_of_le_ofReal_sq {a : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c)
    (h : a ≤ ENNReal.ofReal (c ^ 2)) :
    a ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal c := by
  refine (ENNReal.rpow_le_rpow h (by norm_num)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_pow hc, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Every `x : ℝ≥0∞` satisfies `x ^ (1 / 2 : ℝ) ≤ 1 + x`. -/
theorem rpow_half_le_one_add (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · exact (ENNReal.rpow_le_one h (by norm_num)).trans le_self_add
  · calc x ^ (1 / 2 : ℝ) ≤ x ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le h (by norm_num)
      _ = x := ENNReal.rpow_one x
      _ ≤ 1 + x := le_add_self

/-- For `x : ℝ≥0∞`, `x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x`. -/
theorem rpow_half_mul_rpow_half (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num

/-- For `x : ℝ≥0∞`, `x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (3 / 4 : ℝ)`. -/
theorem rpow_half_mul_rpow_quarter (x : ℝ≥0∞) :
    x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (3 / 4 : ℝ) := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num

/-- If `x : ℝ≥0∞` is not `⊤`, then `x ^ (1 / 2 : ℝ)` is not `⊤`. -/
theorem rpow_half_ne_top {x : ℝ≥0∞} (h : x ≠ ⊤) : x ^ (1 / 2 : ℝ) ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg (by norm_num) h

/-- For `x : ℝ≥0∞` and real exponents `s ≥ 0` and `t ≥ 0` with `s + t = 1`, `x ^ s * x ^ t = x`. -/
theorem rpow_mul_rpow_of_add_eq_one (x : ℝ≥0∞) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s + t = 1) :
    x ^ s * x ^ t = x := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ hs ht, hst, ENNReal.rpow_one]

/-- For `x : ℝ≥0∞` and every real `r`, the fourth power of `x ^ r` is `x ^ (4 * r)`. -/
theorem rpow_pow_four (x : ℝ≥0∞) (r : ℝ) : (x ^ r) ^ 4 = x ^ (4 * r) := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  ring_nf

/-- Every `a : ℝ≥0∞` satisfies `a ^ ((1 : ℝ) / 6) ≤ 1 + a ^ ((1 : ℝ) / 3)`. -/
theorem rpow_sixth_le_one_add_rpow_third (a : ℝ≥0∞) :
    a ^ ((1 : ℝ) / 6) ≤ 1 + a ^ ((1 : ℝ) / 3) := by
  rcases le_total a 1 with h | h
  · exact (ENNReal.rpow_le_one h (by norm_num)).trans le_self_add
  · exact (ENNReal.rpow_le_rpow_of_exponent_le h (by norm_num)).trans le_add_self

/-- For `I : ℝ≥0∞` and a real `B ≥ 0`, if `I ≤ ENNReal.ofReal (B ^ 2)` then `√(I.toReal) ≤ B`. -/
theorem sqrt_toReal_le {I : ℝ≥0∞} {B : ℝ} (hB : 0 ≤ B) (h : I ≤ ENNReal.ofReal (B ^ 2)) :
    Real.sqrt I.toReal ≤ B :=
  (Real.sqrt_le_sqrt (ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) h)).trans_eq (Real.sqrt_sq hB)

/-- If a sequence `d : ℕ → ℝ≥0∞` tends to `0`, then for every `x : ℝ≥0∞` and every real `C` the
sequence `x + ENNReal.ofReal C * d n` tends to `x`. -/
theorem tendsto_add_ofReal_mul_of_tendsto_zero (x : ENNReal) (C : ℝ) (d : ℕ → ENNReal)
    (hd : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n ↦ x + ENNReal.ofReal C * d n) atTop (𝓝 x) := by
  have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) hd (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at this
  simpa using (tendsto_const_nhds (x := x)).add this

/-- For `x : ℝ≥0∞` with `x ≠ ⊤`, the sequence `ENNReal.ofReal (1 + 1 / (j + 1)) * x` tends to `x` as
`j → ∞`. -/
theorem tendsto_ofReal_one_add_one_div_mul (x : ENNReal) (hx : x ≠ ⊤) :
    Tendsto (fun j : ℕ ↦ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * x) atTop (𝓝 x) := by
  have h0 : Tendsto (fun j : ℕ ↦ 1 + 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  rw [add_zero] at h0
  have h1 : Tendsto (fun j : ℕ ↦ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1))) atTop (𝓝 1) := by
    simpa using ENNReal.tendsto_ofReal h0
  simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hx)

/-- In `ℝ≥0∞`, `3 / 2 ≤ 2`. -/
theorem three_halves_le_two_ennreal : (3 / 2 : ℝ≥0∞) ≤ 2 := by
  rw [ENNReal.div_le_iff (by simp) (by simp)]
  norm_num

/-- The real number `3 / 4` equals `3 / 2 * (1 / (2 : ℝ≥0∞)).toReal`. -/
theorem three_quarters_eq_mul_toReal_half : (3 / 4 : ℝ) = 3 / 2 * (1 / (2 : ℝ≥0∞)).toReal := by
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  norm_num

/-- Let `x y d : ℝ≥0∞` with `y ≠ ⊤` and `d ≠ ⊤`, and let `t > 0` be a real number. If
`x ≤ ENNReal.ofReal (1 + t) * y + ENNReal.ofReal (1 + 1 / t) * d`, then
`x.toReal ≤ (1 + t) * y.toReal + (1 + 1 / t) * d.toReal`. -/
theorem toReal_le_mul_toReal_add_mul_toReal {x y d : ℝ≥0∞} (hy : y ≠ ⊤) (hd : d ≠ ⊤) {t : ℝ}
    (ht : 0 < t)
    (h : x ≤ ENNReal.ofReal (1 + t) * y + ENNReal.ofReal (1 + 1 / t) * d) :
    x.toReal ≤ (1 + t) * y.toReal + (1 + 1 / t) * d.toReal := by
  have h1 : ENNReal.ofReal (1 + t) * y ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy
  have h2 : ENNReal.ofReal (1 + 1 / t) * d ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hd
  have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h1, h2⟩) h
  rwa [ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by positivity)] at this

/-- Let `b : ℤ × ℤ → ℝ`, `er : Fin nE → ℤ × ℤ → ℝ`, `mr : Fin nM → ℤ × ℤ → ℝ`, `eb : Fin nE → ℝ` and
`mb : Fin nM → ℝ`, with all values of `er`, `mr`, `eb`, `mb` nonpositive. Then in `ℝ≥0∞`,
`(∑' ι, ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι))) + ofReal (-(∑ β, eb β + ∑ β, mb β)) ≤ (∑' ι,
ofReal (-b ι)) + ∑ β, ((∑' ι, ofReal (-er β ι)) + ofReal (-eb β)) + ∑ β, ((∑' ι, ofReal (-mr β ι)) +
ofReal (-mb β))`, where `ofReal` stands for `ENNReal.ofReal`. The proof uses subadditivity of
`ofReal` at each `ι`, its additivity on the nonnegative numbers `-er β ι`, `-mr β ι`, `-eb β`,
`-mb β`, and the exchange of `∑'` with the finite sums. -/
theorem tsum_ofReal_neg_sum_add_le {nE nM : ℕ} (b : ℤ × ℤ → ℝ) (er : Fin nE → ℤ × ℤ → ℝ)
    (eb : Fin nE → ℝ)
    (mr : Fin nM → ℤ × ℤ → ℝ) (mb : Fin nM → ℝ)
    (her : ∀ β ι, er β ι ≤ 0) (heb : ∀ β, eb β ≤ 0) (hmr : ∀ β ι, mr β ι ≤ 0)
        (hmb : ∀ β, mb β ≤ 0) :
    (∑' ι, ENNReal.ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι)))
        + ENNReal.ofReal (-(∑ β, eb β + ∑ β, mb β))
      ≤ (∑' ι, ENNReal.ofReal (-b ι))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-er β ι)) + ENNReal.ofReal (-eb β))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-mr β ι)) + ENNReal.ofReal (-mb β)) := by
  have hblkn : ENNReal.ofReal (-(∑ β, eb β + ∑ β, mb β))
      = ∑ β, ENNReal.ofReal (-eb β) + ∑ β, ENNReal.ofReal (-mb β) := by
    rw [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ENNReal.ofReal_add (Finset.sum_nonneg fun β _ ↦ neg_nonneg.2 (heb β))
        (Finset.sum_nonneg fun β _ ↦ neg_nonneg.2 (hmb β)),
      ENNReal.ofReal_sum_of_nonneg fun β _ ↦ neg_nonneg.2 (heb β),
      ENNReal.ofReal_sum_of_nonneg fun β _ ↦ neg_nonneg.2 (hmb β)]
  have h1 : ∀ ι, ENNReal.ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι))
      ≤ ENNReal.ofReal (-b ι) + ∑ β, ENNReal.ofReal (-er β ι) + ∑ β, ENNReal.ofReal (-mr β ι) := by
    intro ι
    have hs1 : 0 ≤ ∑ β, -er β ι := Finset.sum_nonneg fun β _ ↦ neg_nonneg.2 (her β ι)
    have hs2 : 0 ≤ ∑ β, -mr β ι := Finset.sum_nonneg fun β _ ↦ neg_nonneg.2 (hmr β ι)
    have hx : -(b ι + ∑ β, er β ι + ∑ β, mr β ι) = -b ι + ∑ β, -er β ι + ∑ β, -mr β ι := by
      rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
      ring
    rw [hx, ← ENNReal.ofReal_sum_of_nonneg fun β _ ↦ neg_nonneg.2 (her β ι),
      ← ENNReal.ofReal_sum_of_nonneg fun β _ ↦ neg_nonneg.2 (hmr β ι)]
    exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
  rw [hblkn]
  have step : (∑' ι, ENNReal.ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι)))
      ≤ (∑' ι, ENNReal.ofReal (-b ι)) + (∑ β, ∑' ι, ENNReal.ofReal (-er β ι))
          + ∑ β, ∑' ι, ENNReal.ofReal (-mr β ι) := by
    refine (tsum_le_tsum h1).trans (le_of_eq ?_)
    rw [tsum_add, tsum_add, Summable.tsum_finsetSum fun β _ ↦ CompleteLattice.summable,
      Summable.tsum_finsetSum fun β _ ↦ CompleteLattice.summable]
  refine (add_le_add step le_rfl).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- In `ℝ≥0∞`, `12 * ENNReal.ofReal (1 / 2) = 6`. -/
theorem twelve_mul_ofReal_half_eq_six : (12 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 6 := by
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat,
    show (12 : ℝ≥0∞) = 6 * 2 by
      norm_num, mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
    mul_one]

/-- For `P : ℝ≥0∞` with `P < ⊤` and a natural number `N`, `2 * (N : ℝ≥0∞) * P < ⊤`. -/
theorem two_mul_natCast_mul_lt_top {P : ℝ≥0∞} (N : ℕ) (hP : P < ⊤) : 2 * (N : ℝ≥0∞) * P < ⊤ :=
  ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofNat_lt_top (ENNReal.natCast_lt_top N)) hP

/-- For `x` and `y` in normed additive groups and `K : ℝ≥0∞` with `K ≠ ⊤`,
`(‖x‖ₑ * K) ^ 2 * ‖y‖ₑ ^ 2 = ENNReal.ofReal ((‖x‖ * K.toReal * ‖y‖) ^ 2)`. -/
theorem enorm_mul_sq_mul_enorm_sq {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {K : ℝ≥0∞}
    (hK : K ≠ ⊤) (x : E) (y : F) :
    (‖x‖ₑ * K) ^ 2 * ‖y‖ₑ ^ 2 = ENNReal.ofReal ((‖x‖ * K.toReal * ‖y‖) ^ 2) := by
  calc (‖x‖ₑ * K) ^ 2 * ‖y‖ₑ ^ 2
      = (ENNReal.ofReal ‖x‖ * ENNReal.ofReal K.toReal) ^ 2 * ENNReal.ofReal ‖y‖ ^ 2 := by
        rw [ofReal_norm, ofReal_norm, ENNReal.ofReal_toReal hK]
    _ = ENNReal.ofReal ((‖x‖ * K.toReal * ‖y‖) ^ 2) := by
        rw [← ENNReal.ofReal_mul (norm_nonneg _),
          ofReal_sq_mul_sq (mul_nonneg (norm_nonneg _) ENNReal.toReal_nonneg) (norm_nonneg _)]

/-- For `α κ β : ℝ≥0∞`, the product `α * κ * β` equals
`(α ^ (3 / 2 : ℝ) * κ ^ (6 / 5 : ℝ)) ^ (1 / 2 : ℝ) * (κ ^ (6 / 5 : ℝ) * β ^ (2 : ℝ)) ^ (1 / 3 : ℝ) *
(α ^ (3 / 2 : ℝ) * β ^ (2 : ℝ)) ^ (1 / 6 :
ℝ)`. On the right the exponents of each of `α`, `κ` and `β` add up to `1`. -/
theorem mul_mul_eq_prod_pairwise_rpow (α κ β : ℝ≥0∞) :
    α * κ * β = (α ^ (3 / 2 : ℝ) * κ ^ (6 / 5 : ℝ)) ^ (1 / 2 : ℝ) *
      (κ ^ (6 / 5 : ℝ) * β ^ (2 : ℝ)) ^ (1 / 3 : ℝ) * (α ^ (3 / 2 : ℝ) * β ^ (2 : ℝ)) ^
          (1 / 6 : ℝ) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 6)]
  simp only [← ENNReal.rpow_mul]
  calc α * κ * β = (α ^ (3 / 2 * (1 / 2) : ℝ) * α ^ (3 / 2 * (1 / 6) : ℝ)) *
        (κ ^ (6 / 5 * (1 / 2) : ℝ) * κ ^ (6 / 5 * (1 / 3) : ℝ)) *
        (β ^ (2 * (1 / 3) : ℝ) * β ^ (2 * (1 / 6) : ℝ)) := by
        rw [rpow_mul_rpow_of_add_eq_one α (by norm_num) (by norm_num) (by norm_num),
          rpow_mul_rpow_of_add_eq_one κ (by norm_num) (by norm_num) (by norm_num),
          rpow_mul_rpow_of_add_eq_one β (by norm_num) (by norm_num) (by norm_num)]
    _ = _ := by ring

/-- For every real `t`, `ENNReal.ofReal t = ENNReal.ofReal (max t 0)`. This is `ofReal_max_zero`
with the two sides exchanged. -/
theorem ofReal_eq_ofReal_max_zero (t : ℝ) : ENNReal.ofReal t = ENNReal.ofReal (max t 0) :=
  (ofReal_max_zero t).symm

/-- For `a n : ℝ≥0∞` with `a ≠ ⊤` and `n ≠ ⊤` and a real number `x`,
`a + ENNReal.ofReal (-x) ≤ ENNReal.ofReal x + n` holds if and only if `a.toReal ≤ x + n.toReal`. The
proof writes the two sides as `ENNReal.ofReal` of the real numbers `a.toReal + max (-x) 0` and
`max x 0 + n.toReal` and uses `max x 0 - max (-x) 0 = x`. -/
theorem add_ofReal_neg_le_iff_toReal_le {a n : ℝ≥0∞} {x : ℝ} (ha : a ≠ ⊤) (hn : n ≠ ⊤) :
    a + ENNReal.ofReal (-x) ≤ ENNReal.ofReal x + n ↔ a.toReal ≤ x + n.toReal := by
  have e1 : a + ENNReal.ofReal (-x) = ENNReal.ofReal (a.toReal + max (-x) 0) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (le_max_right _ _), ENNReal.ofReal_toReal ha,
      ← ofReal_eq_ofReal_max_zero]
  have e2 : ENNReal.ofReal x + n = ENNReal.ofReal (max x 0 + n.toReal) := by
    rw [ENNReal.ofReal_add (le_max_right _ _) ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hn,
      ← ofReal_eq_ofReal_max_zero]
  rw [e1, e2, ENNReal.ofReal_le_ofReal_iff (add_nonneg (le_max_right _ _) ENNReal.toReal_nonneg)]
  have h5 : max x 0 - max (-x) 0 = x := by
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.2 hx)]
      ring
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.2 hx)]
      ring
  constructor <;> intro h <;> linarith

/-- For `x S : ℝ≥0∞` and a natural number `k`, if `2 ^ k * x ≤ S` then `x ≤ S * 2⁻¹ ^ k`. -/
theorem le_mul_inv_two_pow {x S : ℝ≥0∞} (k : ℕ) (h : 2 ^ k * x ≤ S) : x ≤ S * 2⁻¹ ^ k := by
  calc x = 2⁻¹ ^ k * (2 ^ k * x) := by
        rw [← mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow,
          one_mul]
    _ ≤ 2⁻¹ ^ k * S := by gcongr
    _ = S * 2⁻¹ ^ k := mul_comm _ _

/-- Let `Q S sl cr kq` be reals with `0 ≤ kq` and let `N P O Z : ℝ≥0∞` with `P ≠ ⊤`, `N ≠ ⊤` and
`Z = 0`. If `ENNReal.ofReal Q + ENNReal.ofReal (-S) + ENNReal.ofReal sl + ENNReal.ofReal cr + N + O
≤ P + Z + ENNReal.ofReal S + ENNReal.ofReal (-Q) + ENNReal.ofReal kq`, then
`Q + sl + cr ≤ P.toReal - N.toReal + S + kq`. The proof drops `O`, applies `ENNReal.toReal` to both
sides and uses `max x 0 - max (-x) 0 = x` for `Q` and `S`. -/
theorem le_toReal_sub_toReal_of_ofReal_le {Q S sl cr kq : ℝ} {N P O Z : ℝ≥0∞} (hP : P ≠ ⊤)
    (hN : N ≠ ⊤) (hZ : Z = 0)
    (hk : 0 ≤ kq)
    (h : ENNReal.ofReal Q + ENNReal.ofReal (-S) + ENNReal.ofReal sl + ENNReal.ofReal cr + N + O
      ≤ P + Z + ENNReal.ofReal S + ENNReal.ofReal (-Q) + ENNReal.ofReal kq) :
    Q + sl + cr ≤ P.toReal - N.toReal + S + kq := by
  subst hZ
  rw [add_zero] at h
  have h1 : ENNReal.ofReal Q + ENNReal.ofReal (-S) + ENNReal.ofReal sl + ENNReal.ofReal cr + N
      ≤ P + ENNReal.ofReal S + ENNReal.ofReal (-Q) + ENNReal.ofReal kq :=
    le_trans le_self_add h
  have hR : P + ENNReal.ofReal S + ENNReal.ofReal (-Q) + ENNReal.ofReal kq ≠ ⊤ := by
    simp [ENNReal.add_eq_top, hP]
  have h2 := ENNReal.toReal_mono hR h1
  simp only [ENNReal.toReal_add, ENNReal.toReal_ofReal', ne_eq, ENNReal.add_eq_top,
      ENNReal.ofReal_ne_top,
    hP, hN, not_false_eq_true, or_self] at h2
  have hq := max_zero_sub_max_neg_zero_eq_self Q
  have hs := max_zero_sub_max_neg_zero_eq_self S
  have hsl := le_max_left sl 0
  have hcr := le_max_left cr 0
  have hkq : max kq 0 = kq := max_eq_left hk
  linarith

/-- For real numbers `pe`, `pm`, `bd`, `re`, `rm`,
`ENNReal.ofReal (pe + pm) + ENNReal.ofReal (bd + re + rm) + (ENNReal.ofReal (-bd) + ENNReal.ofReal
(-re) + ENNReal.ofReal (-rm)) ≤ (ENNReal.ofReal pe + ENNReal.ofReal re) + (ENNReal.ofReal pm +
ENNReal.ofReal rm) + ENNReal.ofReal bd + ENNReal.ofReal (-(bd + re +
rm))`. The proof passes to real numbers, where `ENNReal.ofReal x` becomes `max x 0`, uses `max (pe +
pm) 0 ≤ max pe 0 + max pm 0`, and uses the relation between `x`, `max x 0` and `max (-x)
0` for `bd`, `re`, `rm` and their sum. -/
theorem ofReal_add_add_ofReal_sum_three_le (pe pm bd re rm : ℝ) :
    ENNReal.ofReal (pe + pm) + ENNReal.ofReal (bd + re + rm)
        + (ENNReal.ofReal (-bd) + ENNReal.ofReal (-re) + ENNReal.ofReal (-rm)) ≤
      (ENNReal.ofReal pe + ENNReal.ofReal re) + (ENNReal.ofReal pm + ENNReal.ofReal rm) +
          ENNReal.ofReal bd
        + ENNReal.ofReal (-(bd + re + rm)) := by
  simp only [ENNReal.ofReal, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  rw [← NNReal.coe_le_coe]
  simp only [NNReal.coe_add, Real.coe_toNNReal']
  have h0 : max (pe + pm) 0 ≤ max pe 0 + max pm 0 :=
    max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
      (add_nonneg (le_max_right _ _) (le_max_right _ _))
  have h1 := max_zero_eq_add_max_neg_zero bd
  have h2 := max_zero_eq_add_max_neg_zero re
  have h3 := max_zero_eq_add_max_neg_zero rm
  have h4 := max_zero_eq_add_max_neg_zero (bd + re + rm)
  linarith

/-- Transfers a real inequality to `ℝ≥0∞`, with the signed terms `A` and `S` split into positive and
negative parts. For reals `A S s c t` with `0 ≤ s` and `0 ≤ c`, and `a b e d : ℝ≥0∞` all different
from `⊤`, if `A - S + s + c + b.toReal + e.toReal ≤ a.toReal + d.toReal + t` then
`ENNReal.ofReal A + ENNReal.ofReal (-S) + ENNReal.ofReal s + ENNReal.ofReal c + b + e ≤ a + d +
ENNReal.ofReal S + ENNReal.ofReal (-A) + ENNReal.ofReal t`. The proof writes each `ENNReal.ofReal
x` as `ENNReal.ofReal (max x 0)`, collects each side into one `ENNReal.ofReal`, and uses `max x 0 -
max (-x) 0 = x`. -/
theorem ofReal_add_le_of_toReal_add_le (A S s c t : ℝ) (a b e d : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (he : e ≠ ⊤)
    (hd : d ≠ ⊤) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (h : A - S + s + c + b.toReal + e.toReal ≤ a.toReal + d.toReal + t) :
    ENNReal.ofReal A + ENNReal.ofReal (-S) + ENNReal.ofReal s + ENNReal.ofReal c + b + e
      ≤ a + d + ENNReal.ofReal S + ENNReal.ofReal (-A) + ENNReal.ofReal t := by
  have m1 := le_max_right A 0
  have m2 := le_max_right (-S) 0
  have m3 := le_max_right S 0
  have m4 := le_max_right (-A) 0
  have m5 := le_max_right t 0
  have tb : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  have te : 0 ≤ e.toReal := ENNReal.toReal_nonneg
  have ta : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  have td : 0 ≤ d.toReal := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb, ← ENNReal.ofReal_toReal he,
    ← ENNReal.ofReal_toReal hd, ofReal_eq_ofReal_max_zero A, ofReal_eq_ofReal_max_zero (-S),
        ofReal_eq_ofReal_max_zero S,
    ofReal_eq_ofReal_max_zero (-A), ofReal_eq_ofReal_max_zero t, ofReal_add_four m1 m2 hs hc,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg m1 m2) hs) hc) tb,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg (add_nonneg m1 m2) hs) hc) tb) te,
    ofReal_add_four ta td m3 m4,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (add_nonneg ta td) m3) m4) m5]
  apply ENNReal.ofReal_le_ofReal
  have h1 := max_zero_sub_max_neg_zero_eq_self A
  have h2 := max_zero_sub_max_neg_zero_eq_self S
  have h3 : t ≤ max t 0 := le_max_left _ _
  linarith

/-- For real numbers `a`, `b`, `c`, `d`,
`ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d + ENNReal.ofReal
(-(a + b + c + d)) = ENNReal.ofReal (a + b + c + d) + (ENNReal.ofReal (-a) + ENNReal.ofReal (-b) +
ENNReal.ofReal (-c) + ENNReal.ofReal (-d))`. The proof passes to real numbers, where `ENNReal.ofReal
x` becomes `max x 0`, and uses the relation between `x`, `max x 0` and `max (-x)
0` for each of `a`, `b`, `c`, `d` and their sum. -/
theorem ofReal_four_add_ofReal_neg_sum_eq (a b c d : ℝ) :
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d
        + ENNReal.ofReal (-(a + b + c + d)) =
      ENNReal.ofReal (a + b + c + d) + (ENNReal.ofReal (-a) + ENNReal.ofReal (-b)
        + ENNReal.ofReal (-c) + ENNReal.ofReal (-d)) := by
  simp only [ENNReal.ofReal, ← ENNReal.coe_add, ENNReal.coe_inj]
  apply NNReal.eq
  simp only [NNReal.coe_add, Real.coe_toNNReal']
  have h1 := max_zero_eq_add_max_neg_zero a
  have h2 := max_zero_eq_add_max_neg_zero b
  have h3 := max_zero_eq_add_max_neg_zero c
  have h4 := max_zero_eq_add_max_neg_zero d
  have h5 := max_zero_eq_add_max_neg_zero (a + b + c + d)
  linarith

/-- For real numbers `b` and `s ≥ 0`,
`ENNReal.ofReal (b - s) + (ENNReal.ofReal (-b) + ENNReal.ofReal s) = ENNReal.ofReal b +
ENNReal.ofReal (-(b - s))`. The proof rewrites each `ENNReal.ofReal x` as `ENNReal.ofReal (max x
0)`, combines each side into one `ENNReal.ofReal`, and checks the resulting real identity by cases.
-/
theorem ofReal_sub_add_ofReal_neg_add_eq (b s : ℝ) (hs : 0 ≤ s) :
    ENNReal.ofReal (b - s) + (ENNReal.ofReal (-b) + ENNReal.ofReal s)
      = ENNReal.ofReal b + ENNReal.ofReal (-(b - s)) := by
  rw [ofReal_eq_ofReal_max_zero (b - s), ofReal_eq_ofReal_max_zero (-b),
      ofReal_eq_ofReal_max_zero b, ofReal_eq_ofReal_max_zero (-(b - s)),
    ← ENNReal.ofReal_add (le_max_right _ _) hs,
    ← ENNReal.ofReal_add (le_max_right _ _) (add_nonneg (le_max_right _ _) hs),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
  congr 1
  rw [max_def, max_def, max_def, max_def]
  split_ifs <;> linarith

/-- For every `x` in `ℝ≥0∞`, `(x ^ (1 / 2)) ^ 2 = x`, where `1 / 2` is a real exponent and `2` a
natural number. -/
theorem rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- For `w x : ℝ≥0∞` and a real `C`, if `w ≤ ENNReal.ofReal C * x ^ (1 / 2 : ℝ)`, then
`w ^ 2 ≤ ENNReal.ofReal ((|C| + 1) ^ 2) * x`. -/
theorem sq_le_of_le_mul_rpow_half {w x : ℝ≥0∞} {C : ℝ}
    (h : w ≤ ENNReal.ofReal C * x ^ (1 / 2 : ℝ)) :
    w ^ 2 ≤ ENNReal.ofReal ((|C| + 1) ^ 2) * x := by
  have hC : ENNReal.ofReal C ≤ ENNReal.ofReal (|C| + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith [le_abs_self C])
  calc w ^ 2 ≤ (ENNReal.ofReal C * x ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ENNReal.ofReal C ^ 2 * x := by rw [mul_pow, rpow_half_sq]
    _ ≤ ENNReal.ofReal (|C| + 1) ^ 2 * x := by gcongr
    _ = ENNReal.ofReal ((|C| + 1) ^ 2) * x := by
      rw [ENNReal.ofReal_pow (by positivity)]

/-- In `ℝ≥0∞`, `2 * 4⁻¹ = 2⁻¹`. -/
theorem two_mul_inv_four : (2 : ℝ≥0∞) * 4⁻¹ = 2⁻¹ := by
  rw [show (4 : ℝ≥0∞) = 2 * 2 by
    norm_num, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- Let `a1 a2 n1 n2 : ℝ≥0∞` with `n1 ≠ ⊤` and `n2 ≠ ⊤`, and let `x1`, `x2` be real numbers. If
`a1 + ENNReal.ofReal (-x1) ≤ ENNReal.ofReal x1 + n1` and
`a2 + ENNReal.ofReal (-x2) ≤ ENNReal.ofReal x2 + n2`, then
`(a1 + a2) + ENNReal.ofReal (-(x1 + x2)) ≤ ENNReal.ofReal (x1 + x2) + (n1 + n2)`. The proof turns
each inequality into a real inequality of the form `a.toReal ≤ x + n.toReal` and adds the two. -/
theorem add_add_ofReal_neg_add_le {a1 a2 n1 n2 : ℝ≥0∞} {x1 x2 : ℝ}
    (h1 : a1 + ENNReal.ofReal (-x1) ≤ ENNReal.ofReal x1 + n1)
    (h2 : a2 + ENNReal.ofReal (-x2) ≤ ENNReal.ofReal x2 + n2) (hn1 : n1 ≠ ⊤) (hn2 : n2 ≠ ⊤) :
    (a1 + a2) + ENNReal.ofReal (-(x1 + x2)) ≤ ENNReal.ofReal (x1 + x2) + (n1 + n2) := by
  have ha1 := ne_top_of_add_ofReal_neg_le h1 hn1
  have ha2 := ne_top_of_add_ofReal_neg_le h2 hn2
  rw [add_ofReal_neg_le_iff_toReal_le ha1 hn1] at h1
  rw [add_ofReal_neg_le_iff_toReal_le ha2 hn2] at h2
  rw [add_ofReal_neg_le_iff_toReal_le (ENNReal.add_ne_top.2 ⟨ha1, ha2⟩)
      (ENNReal.add_ne_top.2 ⟨hn1, hn2⟩),
    ENNReal.toReal_add ha1 ha2, ENNReal.toReal_add hn1 hn2]
  linarith

/-- Let `b : ℤ × ℤ → ℝ`, `ep er : Fin nE → ℤ × ℤ → ℝ`, `mp mr : Fin nM → ℤ × ℤ → ℝ`,
`eb : Fin nE → ℝ` and `mb : Fin nM → ℝ`, with all values of `ep`, `mp` nonnegative and all values of
`er`, `mr`, `eb`, `mb` nonpositive, and write `S ι = b ι + ∑ β, er β ι + ∑ β, mr β ι` and
`T = ∑ β, eb β + ∑ β, mb β`. Then in `ℝ≥0∞`,
`(∑' ι, ofReal (∑ β, ep β ι + ∑ β, mp β ι)) + (∑' ι, ofReal (S ι)) + ofReal T + ((∑' ι, ofReal (-b
ι)) + ∑ β, ((∑' ι, ofReal (-er β ι)) + ofReal (-eb β)) + ∑ β, ((∑' ι, ofReal (-mr β ι)) + ofReal
(-mb β))) ≤ ((∑ β, ∑' ι, ofReal (ep β ι)) + (∑ β, ∑' ι, ofReal (mp β ι)) + ∑' ι, ofReal (b ι)) +
((∑' ι, ofReal (-S ι)) + ofReal
(-T))`, where `ofReal` stands for `ENNReal.ofReal`. The proof shows that the two sides are equal,
using `ofReal (x - s) + (ofReal (-x) + ofReal s) = ofReal x + ofReal (-(x - s))` for `s ≥ 0` at each
`ι` and exchanging `∑'` with the finite sums. -/
theorem tsum_ofReal_sum_add_tsum_neg_le {nE nM : ℕ} (b : ℤ × ℤ → ℝ) (ep er : Fin nE → ℤ × ℤ → ℝ)
    (eb : Fin nE → ℝ)
    (mp mr : Fin nM → ℤ × ℤ → ℝ) (mb : Fin nM → ℝ)
    (hep : ∀ β ι, 0 ≤ ep β ι) (her : ∀ β ι, er β ι ≤ 0) (heb : ∀ β, eb β ≤ 0)
    (hmp : ∀ β ι, 0 ≤ mp β ι) (hmr : ∀ β ι, mr β ι ≤ 0) (hmb : ∀ β, mb β ≤ 0) :
    (∑' ι, ENNReal.ofReal (∑ β, ep β ι + ∑ β, mp β ι))
        + (∑' ι, ENNReal.ofReal (b ι + ∑ β, er β ι + ∑ β, mr β ι))
        + ENNReal.ofReal (∑ β, eb β + ∑ β, mb β)
        + ((∑' ι, ENNReal.ofReal (-b ι))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-er β ι)) + ENNReal.ofReal (-eb β))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-mr β ι)) + ENNReal.ofReal (-mb β)))
      ≤ ((∑ β, ∑' ι, ENNReal.ofReal (ep β ι)) + (∑ β, ∑' ι, ENNReal.ofReal (mp β ι))
          + ∑' ι, ENNReal.ofReal (b ι))
        + ((∑' ι, ENNReal.ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι)))
          + ENNReal.ofReal (-(∑ β, eb β + ∑ β, mb β))) := by
  have hpos : ∀ ι, ENNReal.ofReal (∑ β, ep β ι + ∑ β, mp β ι)
      = ∑ β, ENNReal.ofReal (ep β ι) + ∑ β, ENNReal.ofReal (mp β ι) := by
    intro ι
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun β _ ↦ hep β ι)
        (Finset.sum_nonneg fun β _ ↦ hmp β ι),
      ENNReal.ofReal_sum_of_nonneg fun β _ ↦ hep β ι, ENNReal.ofReal_sum_of_nonneg fun β _ ↦
          hmp β ι]
  have hblk : ENNReal.ofReal (∑ β, eb β + ∑ β, mb β) = 0 :=
    ENNReal.ofReal_of_nonpos (add_nonpos (Finset.sum_nonpos fun β _ ↦ heb β)
        (Finset.sum_nonpos fun β _ ↦ hmb β))
  have hblkn : ENNReal.ofReal (-(∑ β, eb β + ∑ β, mb β))
      = ∑ β, ENNReal.ofReal (-eb β) + ∑ β, ENNReal.ofReal (-mb β) := by
    rw [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ENNReal.ofReal_add (Finset.sum_nonneg fun β _ ↦ neg_nonneg.2 (heb β))
        (Finset.sum_nonneg fun β _ ↦ neg_nonneg.2 (hmb β)),
      ENNReal.ofReal_sum_of_nonneg fun β _ ↦ neg_nonneg.2 (heb β),
      ENNReal.ofReal_sum_of_nonneg fun β _ ↦ neg_nonneg.2 (hmb β)]
  have hι : ∀ ι, ENNReal.ofReal (b ι + ∑ β, er β ι + ∑ β, mr β ι)
      + (ENNReal.ofReal (-b ι) + (∑ β, ENNReal.ofReal (-er β ι) + ∑ β, ENNReal.ofReal (-mr β ι)))
      = ENNReal.ofReal (b ι) + ENNReal.ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι)) := by
    intro ι
    have hs1 : 0 ≤ ∑ β, -er β ι := Finset.sum_nonneg fun β _ ↦ neg_nonneg.2 (her β ι)
    have hs2 : 0 ≤ ∑ β, -mr β ι := Finset.sum_nonneg fun β _ ↦ neg_nonneg.2 (hmr β ι)
    have hx : b ι + ∑ β, er β ι + ∑ β, mr β ι = b ι - (∑ β, -er β ι + ∑ β, -mr β ι) := by
      rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
      ring
    have hsum : ∑ β, ENNReal.ofReal (-er β ι) + ∑ β, ENNReal.ofReal (-mr β ι)
        = ENNReal.ofReal (∑ β, -er β ι + ∑ β, -mr β ι) := by
      rw [ENNReal.ofReal_add hs1 hs2, ENNReal.ofReal_sum_of_nonneg fun β _ ↦
          neg_nonneg.2 (her β ι),
        ENNReal.ofReal_sum_of_nonneg fun β _ ↦ neg_nonneg.2 (hmr β ι)]
    rw [hsum, hx]
    exact ofReal_sub_add_ofReal_neg_add_eq _ _ (add_nonneg hs1 hs2)
  have hsumι := congrArg (fun f : ℤ × ℤ → ℝ≥0∞ ↦ ∑' ι, f ι) (funext hι)
  simp only [tsum_add] at hsumι
  rw [Summable.tsum_finsetSum fun β _ ↦ CompleteLattice.summable,
    Summable.tsum_finsetSum fun β _ ↦ CompleteLattice.summable] at hsumι
  simp only [hpos, tsum_add, hblk, hblkn, Finset.sum_add_distrib]
  rw [Summable.tsum_finsetSum fun β _ ↦ CompleteLattice.summable,
    Summable.tsum_finsetSum fun β _ ↦ CompleteLattice.summable]
  refine le_of_eq ?_
  calc _ = (∑ β, ∑' ι, ENNReal.ofReal (ep β ι)) + (∑ β, ∑' ι, ENNReal.ofReal (mp β ι))
        + ((∑' ι, ENNReal.ofReal (b ι + ∑ β, er β ι + ∑ β, mr β ι))
          + ((∑' ι, ENNReal.ofReal (-b ι)) + ((∑ β, ∑' ι, ENNReal.ofReal (-er β ι))
            + ∑ β, ∑' ι, ENNReal.ofReal (-mr β ι))))
        + (∑ β, ENNReal.ofReal (-eb β) + ∑ β, ENNReal.ofReal (-mb β)) := by ring
    _ = _ := by rw [hsumι]; ring

/-- Let `s` be a finite set in a type `ι`, let `a n : ι → ℝ≥0∞` and `x : ι → ℝ`, and suppose
`n i ≠ ⊤` for every `i ∈ s`. If `a i + ENNReal.ofReal (-x i) ≤ ENNReal.ofReal (x i) + n i` for every
`i ∈ s`, then `(∑ i ∈ s, a i) + ENNReal.ofReal (-∑ i ∈ s, x i) ≤ ENNReal.ofReal (∑ i ∈ s, x i) + ∑ i
∈ s, n i`. The proof is by induction on `s`, with the statement for two summands as the induction
step. -/
theorem sum_add_ofReal_neg_sum_le {ι : Type*} (s : Finset ι) {a n : ι → ℝ≥0∞} {x : ι → ℝ}
    (h : ∀ i ∈ s, a i + ENNReal.ofReal (-x i) ≤ ENNReal.ofReal (x i) + n i)
        (hn : ∀ i ∈ s, n i ≠ ⊤) :
    (∑ i ∈ s, a i) + ENNReal.ofReal (-∑ i ∈ s, x i) ≤ ENNReal.ofReal (∑ i ∈ s, x i) + ∑ i ∈ s,
        n i := by
  classical
  revert h hn
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    simp
  · intro i s hi ih h hn
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    exact add_add_ofReal_neg_add_le (h i (Finset.mem_insert_self i s))
      (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
          (fun j hj ↦ hn j (Finset.mem_insert_of_mem hj)))
      (hn i (Finset.mem_insert_self i s))
      (ENNReal.sum_ne_top.2 fun j hj ↦ hn j (Finset.mem_insert_of_mem hj))

/-- If `Y : ℝ → ℝ≥0∞` tends to zero along a filter `l` on `ℝ` and `c ≠ ⊤`, then
`s ↦ (c * Y s) ^ (1 / 2)` tends to zero along `l`. Multiplication by a finite constant and the
power `1 / 2` are continuous on `ℝ≥0∞` and send zero to zero. -/
theorem tendsto_mul_rpow_half_zero {l : Filter ℝ} {Y : ℝ → ℝ≥0∞} (hY : Tendsto Y l (𝓝 0)) (c : ℝ≥0∞)
    (hc : c ≠ ⊤) : Tendsto (fun s ↦ (c * Y s) ^ (1 / 2 : ℝ)) l (𝓝 0) := by
  have h1 : Tendsto (fun s ↦ c * Y s) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hY (Or.inr hc)
  have h2 := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp h1
  simpa [ENNReal.zero_rpow_of_pos, Function.comp_def] using h2

/-- If `d : ι → ℝ≥0∞` tends to zero along a filter `l`, then `s ↦ d s ^ (1 / 2)` tends to zero along
`l`. The power `1 / 2` is continuous on `ℝ≥0∞` and sends zero to zero. -/
theorem tendsto_rpow_half_zero {ι : Type*} {l : Filter ι} {d : ι → ℝ≥0∞}
    (hd : Tendsto d l (𝓝 0)) : Tendsto (fun s ↦ d s ^ (1 / 2 : ℝ)) l (𝓝 0) := by
  have h := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hd
  simpa [ENNReal.zero_rpow_of_pos, Function.comp_def] using h

/-- For a real `n ≥ 0`, `ENNReal.ofReal (n ^ 3) ^ (2 / 3) = ENNReal.ofReal (n ^ 2)`, where `2 / 3`
is a real exponent. -/
theorem ofReal_cube_rpow_two_thirds {n : ℝ} (hn : 0 ≤ n) :
    ENNReal.ofReal (n ^ 3) ^ ((2 : ℝ) / 3) = ENNReal.ofReal (n ^ 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  congr 1
  rw [← Real.rpow_natCast n 3, ← Real.rpow_mul hn, ← Real.rpow_natCast n 2]
  norm_num

/-- For every `x` in a normed additive commutative group, `ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2`. -/
theorem ofReal_norm_sq_eq_eNorm_sq {E : Type*} [NormedAddCommGroup E] (x : E) :
    ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg x), ofReal_norm]

/-- The exponents `3`, `6`, `2` form a Hölder triple in `ℝ≥0∞`: `3⁻¹ + 6⁻¹ = 2⁻¹`. -/
theorem holderTriple_three_six_two : ENNReal.HolderTriple 3 6 2 := by
  constructor
  have h3 : (3 : ℝ≥0∞) = ((3 : ℝ≥0) : ℝ≥0∞) := rfl
  have h6 : (6 : ℝ≥0∞) = ((6 : ℝ≥0) : ℝ≥0∞) := rfl
  have h2 : (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞) := rfl
  rw [h3, h6, h2, ← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_inv (by norm_num),
    ← ENNReal.coe_inv (by norm_num), ← ENNReal.coe_add]
  congr 1
  norm_num

/-- For every `a` in `ℝ≥0∞`, `(a ^ (1 / 2)) ^ 2 = a`, where both exponents are real numbers. -/
theorem rpow_half_rpow_two (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- For a real `t ≥ 0`, `ENNReal.ofReal (t ^ 2) ^ (1 / 2) = ENNReal.ofReal t`, where `1 / 2` is a
real exponent. -/
theorem ofReal_sq_rpow_half {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (t ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal t := by
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg t) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq ht]

/-- The exponents `6`, `3`, `2` form a Hölder triple in `ℝ≥0∞`: `6⁻¹ + 3⁻¹ = 2⁻¹`. -/
theorem holderTriple_six_three_two : ENNReal.HolderTriple 6 3 2 := by
  constructor
  rw [← ENNReal.toReal_eq_toReal_iff' (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  norm_num

/-- For every real `B`, `ENNReal.ofReal B ^ 2 ≤ ENNReal.ofReal (B ^ 2)`. There is equality for
`B ≥ 0`, and the left side is zero for `B < 0`. -/
theorem sq_ofReal_le_ofReal_sq (B : ℝ) : ENNReal.ofReal B ^ 2 ≤ ENNReal.ofReal (B ^ 2) := by
  rcases le_or_gt 0 B with h | h
  · rw [ENNReal.ofReal_pow h]
  · rw [ENNReal.ofReal_of_nonpos h.le]
    simp

/-- For every real `x`, `2 * ENNReal.ofReal x = ENNReal.ofReal (2 * x)` in `ℝ≥0∞`. -/
theorem two_mul_ofReal (x : ℝ) :
    (2 : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) := by
  rw [ENNReal.ofReal_mul (by norm_num)]
  simp

/-- For every `x` in `ℝ≥0∞`, `(x ^ (1 / 4)) ^ 4 = x`, where `1 / 4` is a real exponent and `4` a
natural number. -/
theorem rpow_quarter_pow_four (x : ℝ≥0∞) : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- For every `z` in `ℝ≥0∞`, `(z ^ 2) ^ (1 / 2) = z`, where `2` is a natural number and `1 / 2` a
real exponent. -/
theorem ennreal_sq_rpow_half (z : ℝ≥0∞) : (z ^ 2) ^ (1 / 2 : ℝ) = z := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- For every `z` in a normed additive commutative group, `‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2)`. -/
theorem eNorm_sq_eq_ofReal_norm_sq {E : Type*} [NormedAddCommGroup E] (z : E) :
    ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := Eq.symm (ofReal_norm_sq_eq_eNorm_sq z)

end PDE.Analysis
